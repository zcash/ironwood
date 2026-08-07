import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Probability.Distributions.Uniform
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.SpendAuthority

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# Probabilistic capstones

The deterministic layer quantifies over valid annotated ledgers. This layer quantifies
over a distribution of them: an adversary is an arbitrary `PMF` over `ValidAnnotated`,
and we do not model the interaction that produced it. That matches the games' stance —
the annotated-ledger quantification is a superset of what a real adversary can reach —
and it keeps the oracle bookkeeping inside the discharge of each per-arm hypothesis,
where the machine models exist.

Restricting the distribution to *valid* ledgers loses no generality. Every game's bad
event requires validity, so mass on invalid ledgers contributes nothing to success:
conditioning any adversary on validity can only increase its success probability, and
a bound for valid-only adversaries implies the bound for all of them.

Events are reduction-branch preimages: "the reduction lands in this arm on this
sample". An existential break predicate would need choice to extract data from; the
branch of a computed reduction needs none. The composition is pure event algebra — the
violation event is contained in the union of the arm events, so its probability is at
most the sum of the per-arm probabilities (`measure_mono` plus `measure_union_le`).
No independence, no counting. The all-prefixes variants name each ε on one event
shared across prefixes, so a bound over `k` prefixes costs no factor of `k`. The
value-side events are prefix-indexed and the Balance-subset events step-indexed; a
statement taking an event at a successor prefix — the one step/prefix crossing,
where non-negativity after the first `i + 1` transactions rests on subset step
`i` — carries `_succ` in its name, and everything else is same-index. Each arm's
probability is then bounded by a named ε hypothesis. The key-binding arm's ε is
discharged in `KeyBindingArm.lean` against the key-binding layer's probability bound
(`toInterface_break_measure_le`), for a ledger adversary in the oracle model.
Connecting that bound to this layer's named-ε slot — an oracle machine against a `PMF`
over valid annotated ledgers — is still open (#155), as are the Merkle and
note-commitment arms (against Sinsemilla/DLR hardness).
-/

namespace Zcash.Security.Ledger.Model

open scoped ENNReal

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

/-! ## Event algebra -/

/-- Union bound over two events: an event contained in a union is bounded by the sum
of the two measures. -/
theorem toOuterMeasure_le_add₂ {α : Type*} (p : PMF α) {E B₁ B₂ : Set α}
    (h : E ⊆ B₁ ∪ B₂) :
    p.toOuterMeasure E ≤ p.toOuterMeasure B₁ + p.toOuterMeasure B₂ :=
  le_trans (MeasureTheory.measure_mono h) (MeasureTheory.measure_union_le _ _)

/-- Union bound over three events: an event contained in a triple union is bounded by
the sum of the three measures. -/
theorem toOuterMeasure_le_add₃ {α : Type*} (p : PMF α) {E B₁ B₂ B₃ : Set α}
    (h : E ⊆ B₁ ∪ B₂ ∪ B₃) :
    p.toOuterMeasure E
      ≤ p.toOuterMeasure B₁ + p.toOuterMeasure B₂ + p.toOuterMeasure B₃ :=
  le_trans (MeasureTheory.measure_mono h)
    (le_trans (MeasureTheory.measure_union_le _ _)
      (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl))

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

variable (P kv issuance maxActions) in
/-- The adversary's sample space: a valid witness-annotated ledger, with its validity
proof. Bundling validity is a convenience, not a restriction — a bad event requires
validity, so conditioning any distribution on validity can only increase its success
probability, and a bound over this space implies the bound over bare ledgers. -/
abbrev ValidAnnotated :=
  {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth //
    ValidLedger P kv issuance maxActions ledger}

/-! ## Balance conservation and shielded balance cap -/

/-- The transaction-balance premiss violation event: the samples on which the
transaction-balance premiss hands the conservation reduction a break of the abstract
type `VB`. -/
def txBalanceBreakEvent {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b : VB, balanceConservationOrBreak (issuance := issuance) (perTx ω) i = .inr b}

/-- The balance-conservation violation event: the shielded pool plus the transparent
pool differs from the minted issuance after the first `i` transactions. -/
def balanceConservationViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | shieldedPoolBalance ω.1 i + transparentPoolBalance issuance ω.1 i
    ≠ issuanceTotal issuance ω.1 i}

/-- The shielded-balance-cap violation event: the shielded pool exceeds the minted
issuance after the first `i` transactions. -/
def shieldedBalanceCapViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ shieldedPoolBalance ω.1 i ≤ issuanceTotal issuance ω.1 i}

/-- A conservation-violating sample lands in the transaction-balance premiss arm: on
it, the conservation reduction cannot return the equation. -/
theorem balanceConservationViolation_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    balanceConservationViolation (P := P) (kv := kv) (maxActions := maxActions) i
      ⊆ txBalanceBreakEvent perTx i := by
  intro ω hω
  rcases h : balanceConservationOrBreak (issuance := issuance) (perTx ω) i with heq | b
  · exact absurd heq hω
  · exact ⟨b, h⟩

/-- A cap-violating sample lands in the transaction-balance premiss arm too: if the
reduction returned the conservation equation, transparent nonnegativity would force the
bound. -/
theorem shieldedBalanceCapViolation_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    shieldedBalanceCapViolation (P := P) (kv := kv) (maxActions := maxActions) i
      ⊆ txBalanceBreakEvent perTx i := by
  intro ω hω
  rcases h : balanceConservationOrBreak (issuance := issuance) (perTx ω) i with heq | b
  · exact absurd (by have := ω.2.transparent_nonneg i; omega) hω
  · exact ⟨b, h⟩

/-- **Balance conservation at one prefix.** For any adversary, the probability that
the ledger fails to balance after the first `i` transactions is at most the
transaction-balance premiss arm's ε. -/
theorem balanceConservationPerTx_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) {ε_conservation : ℝ≥0∞}
    (hvb : A.toOuterMeasure (txBalanceBreakEvent perTx i) ≤ ε_conservation) :
    A.toOuterMeasure (balanceConservationViolation i) ≤ ε_conservation :=
  le_trans (MeasureTheory.measure_mono (balanceConservationViolation_subset perTx i)) hvb

/-- **Shielded balance cap at one prefix.** For any adversary, the probability that
the shielded pool exceeds the minted issuance after the first `i` transactions is at
most the transaction-balance premiss arm's ε. -/
theorem shieldedBalanceCapPerTx_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) {ε_cap : ℝ≥0∞}
    (hvb : A.toOuterMeasure (txBalanceBreakEvent perTx i) ≤ ε_cap) :
    A.toOuterMeasure (shieldedBalanceCapViolation i) ≤ ε_cap :=
  le_trans (MeasureTheory.measure_mono (shieldedBalanceCapViolation_subset perTx i)) hvb

/-- The all-prefixes transaction-balance break event: there exists `i < k` such that
after the first `i` transactions, the conservation reduction is handed a break. -/
def txBalanceBreakEventBefore {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ txBalanceBreakEvent perTx i}

/-- The all-prefixes balance-conservation violation event: there exists `i < k` such
that after the first `i` transactions, the shielded pool plus the transparent pool
differs from the minted issuance. -/
def balanceConservationViolationBefore (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ balanceConservationViolation i}

/-- The all-prefixes shielded-balance-cap violation event: there exists `i < k` such
that after the first `i` transactions, the shielded pool exceeds the minted issuance. -/
def shieldedBalanceCapViolationBefore (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ shieldedBalanceCapViolation i}

/-- A sample violating conservation at some prefix lands in the all-prefixes
transaction-balance premiss arm, at that same prefix. -/
theorem balanceConservationViolationBefore_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) :
    balanceConservationViolationBefore (P := P) (kv := kv) (maxActions := maxActions) k
      ⊆ txBalanceBreakEventBefore perTx k := by
  rintro ω ⟨i, hik, hω⟩
  exact ⟨i, hik, balanceConservationViolation_subset perTx i hω⟩

/-- A sample violating the cap at some prefix lands in the all-prefixes
transaction-balance premiss arm, at that same prefix. -/
theorem shieldedBalanceCapViolationBefore_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) :
    shieldedBalanceCapViolationBefore (P := P) (kv := kv) (maxActions := maxActions) k
      ⊆ txBalanceBreakEventBefore perTx k := by
  rintro ω ⟨i, hik, hω⟩
  exact ⟨i, hik, shieldedBalanceCapViolation_subset perTx i hω⟩

/-- **Balance conservation at every prefix, at no extra cost in `k`.** For any
adversary, the probability that the pools fail to sum to issuance after one of the
first `k` transactions is at most a single ε. A naive union bound over the `k`
prefixes would pay `k · ε`; instead the hypothesis names one ε on the shared
all-prefixes break event, and every prefix's violation lands there. -/
theorem balanceConservation_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) {ε_conservation : ℝ≥0∞}
    (hvb : A.toOuterMeasure (txBalanceBreakEventBefore perTx k) ≤ ε_conservation) :
    A.toOuterMeasure (balanceConservationViolationBefore k) ≤ ε_conservation :=
  le_trans
    (MeasureTheory.measure_mono (balanceConservationViolationBefore_subset perTx k)) hvb

/-- **Shielded balance cap at every prefix, at no extra cost in `k`.** For any
adversary, the probability that the shielded pool exceeds the minted issuance after
one of the first `k` transactions is at most a single ε, by the same event-sharing
as balance conservation. -/
theorem shieldedBalanceCap_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) {ε_cap : ℝ≥0∞}
    (hvb : A.toOuterMeasure (txBalanceBreakEventBefore perTx k) ≤ ε_cap) :
    A.toOuterMeasure (shieldedBalanceCapViolationBefore k) ≤ ε_cap :=
  le_trans
    (MeasureTheory.measure_mono (shieldedBalanceCapViolationBefore_subset perTx k)) hvb

/-! ## Balance-subset -/

/-- The three arms of a `BalanceBreak`, as a plain tag for naming the arm events. -/
inductive BalanceArm
  | merkle
  | noteCommit
  | keyBinding

/-- The arm a break lies in. -/
def BalanceBreak.arm : BalanceBreak P kv → BalanceArm
  | .merkle _ => .merkle
  | .noteCommit _ => .noteCommit
  | .keyBinding _ _ _ => .keyBinding

section BalanceSubset

variable [DecidableEq F] [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI]
  [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK] [NoZeroSMulDivisors F G]

/-- The branch-preimage event for one arm: the samples on which the Balance-subset
reduction lands in that arm. -/
def balanceSubsetBreakEvent (i : ℕ) (arm : BalanceArm) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b : BalanceBreak P kv, balanceSubsetOrBreak ω.2 i = .inr b ∧ b.arm = arm}

/-- The Balance-subset violation event: the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i`. -/
def balanceSubsetViolation (i : ℕ) : Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ nonZeroSpends ω.1 (i + 1) ≤ ↑(positionedOutputs ω.1 i)}

/-- A violating sample lands in one of the three arms: on it, the reduction cannot
return the subset proof, so it returns a break, and the break's arm classifies it. -/
theorem balanceSubsetViolation_subset (i : ℕ) :
    balanceSubsetViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) i
      ⊆ balanceSubsetBreakEvent i .merkle ∪ balanceSubsetBreakEvent i .noteCommit
        ∪ balanceSubsetBreakEvent i .keyBinding := by
  intro ω hω
  rcases h : balanceSubsetOrBreak ω.2 i with hle | b
  · exact absurd hle hω
  · cases b with
    | merkle c => exact Or.inl (Or.inl ⟨_, h, rfl⟩)
    | noteCommit nb => exact Or.inl (Or.inr ⟨_, h, rfl⟩)
    | keyBinding w₁ w₂ hbr => exact Or.inr ⟨_, h, rfl⟩

/-- **Balance-subset at one prefix.** For any adversary — a distribution over valid
annotated ledgers — the probability that the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i` is at most
the sum of the three break-arm probabilities, each bounded by its named ε
hypothesis. -/
theorem balanceSubsetPerTx_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (i : ℕ) {εm εnc εkb : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEvent i .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEvent i .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEvent i .keyBinding) ≤ εkb) :
    A.toOuterMeasure (balanceSubsetViolation i) ≤ εm + εnc + εkb :=
  le_trans (toOuterMeasure_le_add₃ A (balanceSubsetViolation_subset i))
    (add_le_add (add_le_add hm hnc) hkb)

/-- The all-prefixes event for one arm: at some step `i < k`, the Balance-subset
reduction lands in that arm. Step `i` compares the spends of the first `i + 1`
transactions against the outputs of the first `i`, and so (unlike the conservation
and cap events) it concerns the state after the first `i + 1` transactions; this
is natural given the definition of `balanceSubsetBreakEvent`. -/
def balanceSubsetBreakEventUpTo (k : ℕ) (arm : BalanceArm) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ balanceSubsetBreakEvent i arm}

/-- The all-prefixes Balance-subset violation event: for some `i < k`, the nonzero
spends of the first `i + 1` transactions are not covered by the positioned outputs
of the first `i`. -/
def balanceSubsetViolationUpTo (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ balanceSubsetViolation i}

/-- A sample violating Balance-subset at some prefix lands in one of the three arms,
at that same prefix. -/
theorem balanceSubsetViolationUpTo_subset (k : ℕ) :
    balanceSubsetViolationUpTo (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ balanceSubsetBreakEventUpTo k .merkle ∪ balanceSubsetBreakEventUpTo k .noteCommit
        ∪ balanceSubsetBreakEventUpTo k .keyBinding := by
  rintro ω ⟨i, hik, hω⟩
  rcases balanceSubsetViolation_subset i hω with (h | h) | h
  · exact Or.inl (Or.inl ⟨i, hik, h⟩)
  · exact Or.inl (Or.inr ⟨i, hik, h⟩)
  · exact Or.inr ⟨i, hik, h⟩

/-- **Balance-subset at every prefix, at no extra cost in `k`.** For any adversary,
the probability that the nonzero spends escape the earlier positioned outputs at
some step `i < k` is at most the sum of three ε's — one per arm, each named on that
arm's shared all-prefixes event. This is the same bound as for a single step,
independent of `k`. -/
theorem balanceSubset_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (k : ℕ) {εm εnc εkb : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .keyBinding) ≤ εkb) :
    A.toOuterMeasure (balanceSubsetViolationUpTo k) ≤ εm + εnc + εkb :=
  le_trans (toOuterMeasure_le_add₃ A (balanceSubsetViolationUpTo_subset k))
    (add_le_add (add_le_add hm hnc) hkb)

end BalanceSubset

/-! ## Balance integrity -/

section BalanceIntegrity

variable [DecidableEq F] [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI]
  [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK] [NoZeroSMulDivisors F G]

/-- The shielded-balance non-negativity violation event: the shielded pool goes
negative after the first `i` transactions — value spent that was never created. -/
def shieldedBalanceNonNegativeViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ 0 ≤ shieldedPoolBalance ω.1 i}

/-- The one step/prefix crossing: the pool can only go negative after a transaction,
so a non-negativity violation at prefix `i + 1` lands in the three Balance-subset
arms at step `i` — were the spends covered by the earlier outputs, the pool could
not go negative (`shieldedPoolBalance_nonneg`). -/
theorem shieldedBalanceNonNegativeViolation_succ_subset (i : ℕ) :
    shieldedBalanceNonNegativeViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) (i + 1)
      ⊆ balanceSubsetBreakEvent i .merkle ∪ balanceSubsetBreakEvent i .noteCommit
        ∪ balanceSubsetBreakEvent i .keyBinding := by
  intro ω hω
  exact balanceSubsetViolation_subset i
    (fun hsub => hω (shieldedPoolBalance_nonneg ω.1 i hsub))

/-- **Shielded non-negativity, probabilistically.** The pool can only go negative
after a transaction: for any adversary, the probability that the shielded pool goes
negative after the first `i + 1` transactions is at most the three step-`i`
Balance-subset arm ε's. -/
theorem shieldedBalanceNonNegative_succ_measure_le
    (A : PMF (ValidAnnotated P kv issuance maxActions)) (i : ℕ) {εm εnc εkb : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEvent i .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEvent i .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEvent i .keyBinding) ≤ εkb) :
    A.toOuterMeasure (shieldedBalanceNonNegativeViolation (i + 1)) ≤ εm + εnc + εkb :=
  le_trans
    (toOuterMeasure_le_add₃ A (shieldedBalanceNonNegativeViolation_succ_subset i))
    (add_le_add (add_le_add hm hnc) hkb)

/-- The per-prefix Balance-integrity violation event: after the first `i`
transactions, the shielded pool goes negative, the transparent pool goes negative,
or the pools fail to sum to the minted issuance. The event mirrors
`balanceIntegrityOrBreak`'s conclusion; on the valid sample space the transparent
conjunct cannot fail (`ValidLedger.transparent_nonneg`). -/
def balanceIntegrityPerTxViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ (0 ≤ shieldedPoolBalance ω.1 i
    ∧ 0 ≤ transparentPoolBalance issuance ω.1 i
    ∧ shieldedPoolBalance ω.1 i + transparentPoolBalance issuance ω.1 i
        = issuanceTotal issuance ω.1 i)}

/-- A per-prefix integrity violation at prefix `i` is a shielded non-negativity
violation or a conservation violation, at that same prefix: the transparent
conjunct cannot fail on the valid sample space. -/
theorem balanceIntegrityPerTxViolation_subset (i : ℕ) :
    balanceIntegrityPerTxViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) i
      ⊆ shieldedBalanceNonNegativeViolation i ∪ balanceConservationViolation i := by
  intro ω hω
  rcases not_and_or.mp hω with h | h
  · exact Or.inl h
  · rcases not_and_or.mp h with h' | h'
    · exact absurd (ω.2.transparent_nonneg i) h'
    · exact Or.inr h'

/-- **Balance integrity at one prefix.** For any adversary, the probability that
balance integrity fails (the shielded pool goes negative or the pools fail to sum
to the minted issuance) after the first `i` transactions is at most a
non-negativity ε plus the transaction-balance premiss arm's ε. Discharge
`ε_nonneg` at successor prefixes with `shieldedBalanceNonNegative_succ_measure_le`;
the empty prefix cannot go negative. -/
theorem balanceIntegrityPerTx_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) {ε_nonneg ε_conservation : ℝ≥0∞}
    (hnn : A.toOuterMeasure (shieldedBalanceNonNegativeViolation i) ≤ ε_nonneg)
    (hvb : A.toOuterMeasure (txBalanceBreakEvent perTx i) ≤ ε_conservation) :
    A.toOuterMeasure (balanceIntegrityPerTxViolation i) ≤ ε_nonneg + ε_conservation :=
  le_trans
    (toOuterMeasure_le_add₂ A
      ((balanceIntegrityPerTxViolation_subset i).trans
        (Set.union_subset_union subset_rfl
          (balanceConservationViolation_subset perTx i))))
    (add_le_add hnn hvb)

/-- The all-prefixes Balance-integrity violation event: there exists `i < k` such
that balance integrity fails after the first `i` transactions: the shielded pool
goes negative or the pools fail to sum to the minted issuance. -/
def balanceIntegrityViolationBefore (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ balanceIntegrityPerTxViolation i}

/-- An integrity violation at some prefix lands in one of the three all-prefixes
arms or the all-prefixes transaction-balance premiss arm: a negative pool at prefix
`j + 1` lands in an arm at step `j` (the empty prefix cannot go negative), and a
conservation violation lands in the premiss arm at its own prefix. One bound `k`
serves the mixed step-indexed (`UpTo`) and prefix-indexed (`Before`) right-hand
side: the crossing only produces steps `j` with `j + 1 < k`, so `j < k`. -/
theorem balanceIntegrityViolationBefore_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) :
    balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ (balanceSubsetBreakEventUpTo k .merkle
          ∪ balanceSubsetBreakEventUpTo k .noteCommit
          ∪ balanceSubsetBreakEventUpTo k .keyBinding)
        ∪ txBalanceBreakEventBefore perTx k := by
  rintro ω ⟨i, hik, hω⟩
  rcases not_and_or.mp hω with h | h
  · cases i with
    | zero => exact absurd (shieldedPoolBalance_zero ω.1).symm.le h
    | succ j =>
        rcases shieldedBalanceNonNegativeViolation_succ_subset j h with (h' | h') | h'
        · exact Or.inl (Or.inl (Or.inl ⟨j, Nat.lt_of_succ_lt hik, h'⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨j, Nat.lt_of_succ_lt hik, h'⟩))
        · exact Or.inl (Or.inr ⟨j, Nat.lt_of_succ_lt hik, h'⟩)
  · rcases not_and_or.mp h with h' | h'
    · exact absurd (ω.2.transparent_nonneg i) h'
    · exact Or.inr ⟨i, hik, balanceConservationViolation_subset perTx i h'⟩

/-- **Balance integrity at every prefix, at no extra cost in `k`.** For any adversary,
the probability that balance integrity is violated (the shielded pool goes negative
or the pools fail to sum to the minted issuance) at some prefix `i < k` is at most
the three Balance-subset arm ε's plus the transaction-balance premiss arm's ε. This
is the same bound as for a single prefix, independent of `k`. -/
theorem balanceIntegrity_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (k : ℕ) {εm εnc εkb ε_conservation : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEventUpTo k .keyBinding) ≤ εkb)
    (hvb : A.toOuterMeasure (txBalanceBreakEventBefore perTx k) ≤ ε_conservation) :
    A.toOuterMeasure (balanceIntegrityViolationBefore k) ≤ εm + εnc + εkb + ε_conservation :=
  le_trans (toOuterMeasure_le_add₂ A (balanceIntegrityViolationBefore_subset perTx k))
    (add_le_add
      (le_trans (toOuterMeasure_le_add₃ A subset_rfl)
        (add_le_add (add_le_add hm hnc) hkb))
      hvb)

end BalanceIntegrity

/-! ## Spend Authority -/

section SpendAuthority

variable [DecidableEq G] [NoZeroSMulDivisors F G]

/-- The forgery arm event, for a victim key witness `wV` with signing history
`Signed`: the samples with an Action spending a note addressed to `wV` in a
transaction with an unsigned sighash, on which the Spend Authority reduction lands in
the forgery arm. -/
def spendAuthorityForgeryEvent (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ f,
    spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh = .inl f}

/-- The key-binding arm event: as `spendAuthorityForgeryEvent`, with the reduction
landing in the break arm. -/
def spendAuthorityBreakEvent (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ b,
    spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh = .inr b}

/-- The Spend Authority violation event: some Action spends a note addressed to `wV`
in a transaction whose sighash the holder of `wV` never signed. -/
def spendAuthorityViolation (wV : KW) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx ∈ ω.1, ∃ a ∈ tx.actions,
    a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd ∧ ¬ Signed tx.sighash}

/-- A violating sample lands in the forgery arm or the break arm: the reduction runs
on the violating Action, and its branch classifies the sample. -/
theorem spendAuthorityViolation_subset (wV : KW) (hKB : kv.KB wV)
    (Signed : MSG → Prop) :
    spendAuthorityViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) wV Signed
      ⊆ spendAuthorityForgeryEvent wV hKB Signed ∪ spendAuthorityBreakEvent wV hKB Signed := by
  rintro ω ⟨tx, htx, a, ha, hrecv, hfresh⟩
  rcases h : spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh with f | b
  · exact Or.inl ⟨tx, htx, a, ha, hrecv, hfresh, f, h⟩
  · exact Or.inr ⟨tx, htx, a, ha, hrecv, hfresh, b, h⟩

/-- **Spend Authority, probabilistically.** For any adversary, the probability that
some Action spends a note addressed to `wV` over an unsigned sighash is at most the
forgery arm's ε plus the key-binding arm's ε. -/
theorem spendAuthority_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) {εf εkb : ℝ≥0∞}
    (hf : A.toOuterMeasure (spendAuthorityForgeryEvent wV hKB Signed) ≤ εf)
    (hkb : A.toOuterMeasure (spendAuthorityBreakEvent wV hKB Signed) ≤ εkb) :
    A.toOuterMeasure (spendAuthorityViolation wV Signed) ≤ εf + εkb :=
  le_trans (toOuterMeasure_le_add₂ A (spendAuthorityViolation_subset wV hKB Signed))
    (add_le_add hf hkb)

end SpendAuthority

end Validity

end Zcash.Security.Ledger.Model
