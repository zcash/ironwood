import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.ExtractionArm
import Zcash.Security.Ledger.KeyBindingDLR
import Zcash.Security.Ledger.NoteCommitDLR
import Zcash.Security.Ledger.MerkleDLR

/-!
# The Orchard instantiation: every Balance-subset arm computes a discrete-log relation

The fully composed Orchard Balance capstones — for a proof-emitting adversary, with
the knowledge hypotheses discharged — are the `_of_dlogProfiles` endpoints of
`Zcash.Security.Ledger.OrchardExtractionExperiment`, not here.

These are the instantiations that use the Orchard-protocol bases and parameters. At
them, each of the three Balance-subset break arms reduces to a nontrivial discrete-log
relation among the fixed Sinsemilla bases. Each reducer is a total, hypothesis-free
function from the arm's break to its relation, so it needs no random-oracle model.
`orchardBalanceSubsetOrRelation` runs all three: from a valid Orchard ledger it
computes either the Balance-subset containment or a nontrivial relation among the
fixed bases.

The probability layer names the relation event — the samples on which the reduction
computes a relation — and bounds every capstone violation by it. One ε suffices where
the abstract capstones name one per arm, and one ε suffices for every prefix of a
`k`-transaction ledger where a naive union bound would pay `k · ε`: the arms and the
prefixes all land in the same event, a nontrivial discrete-log relation among the same
fixed bases.

That probability, `ε_sinsemilladlr`, is the advantage in finding a nontrivial
discrete-log relation among the Sinsemilla bases (spec Theorems 5.4.3 and 5.4.4,
re-proved as `preCoeffs_inj` and `relationOfChainPmEq`). It reduces tightly to
discrete-log hardness of the fixed bases (Jaeger–Tessaro, eprint 2020/1213 Lemma 3,
re-proved as `relation_prob_le_of_textbookDL`). The witness-level model quantifies
over valid annotated ledgers, so it abstracts away Halo 2 knowledge soundness — a
separate, lossy reduction on the different Halo 2 bases; that is where the end-to-end
reduction loss lives. In the protocol's design, value conservation rests on the
binding signature. `ε_bindsig` is a named hypothesis on the conservation events. The
extractor-plus-knowledge-error form replaces it with named bounds further down the
reduction: with the binding-signature primitives pinned to a RedDSA shape,
`orchardBalanceConservationBefore_measure_le_kerr` and
`orchardBalanceIntegrity_measure_le_kerr` bound the same events by `ε_dlr + κ`, a
`(Vbase, Rbase)` discrete-log-relation advantage plus the extractor's knowledge error;
the conservation experiment discharges both in the challenge-oracle model, through one
combined finder.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model
open scoped ENNReal

variable {MSG SIG : Type*}
  (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
  (issuance : ℕ → ℕ) (maxActions : ℕ)

/-- The Orchard instantiation's sample space. -/
abbrev OrchardAnnotated :=
  ValidAnnotated (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify) keyBinding
    issuance maxActions

/-- **The Orchard Balance-subset reduction.** In a valid Orchard ledger, either the
nonzero spends of the first `i + 1` transactions are covered by the positioned outputs
of the first `i`, or the ledger's own data computes a nontrivial discrete-log relation
among the fixed Sinsemilla bases. Each Balance-subset break arm is routed through its
Orchard reducer, so a break in any arm becomes a nontrivial relation among the fixed
bases, with no random-oracle model. -/
def orchardBalanceSubsetOrRelation {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify) keyBinding
      issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i))
      ⊕' NontrivialRelation (F := Fq) pallasS orchardPoints :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (relationOfKeyBindingBreak h)
  | .inr (.noteCommit nb) => .inr (relationOfNoteCommitBreak spendAuthVerify bindingVerify nb)
  | .inr (.merkle c) => .inr (relationOfMerkleCollision c.2)

/-! ## The Orchard Balance-subset probability bound -/

/-- The Orchard relation event: the samples on which the Orchard reduction computes a
nontrivial discrete-log relation among the fixed Sinsemilla bases. -/
def orchardRelationEvent (i : ℕ) :
    Set (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions) :=
  {ω | ∃ r : NontrivialRelation (F := Fq) pallasS orchardPoints,
    orchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions ω.2 i = .inr r}

/-- A Balance-subset-violating Orchard ledger lands in the relation event: the total
reduction cannot return the containment on such a sample, so it returns a relation. -/
theorem balanceSubsetViolation_subset_relation (i : ℕ) :
    balanceSubsetViolation (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding)
        (issuance := issuance) (maxActions := maxActions) i
      ⊆ orchardRelationEvent spendAuthVerify bindingVerify issuance maxActions i := by
  intro ω hω
  rcases h : orchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions ω.2 i
    with hle | r
  · exact absurd hle hω
  · exact ⟨r, h⟩

/-- **The Orchard Balance-subset probability bound.** For any adversary — a
distribution over valid Orchard ledgers — the probability that the nonzero spends of
the first `i + 1` transactions escape the positioned outputs of the first `i` is at
most the probability that the ledger computes a nontrivial discrete-log relation among
the fixed Sinsemilla bases. That single discrete-log-relation advantage
`ε_sinsemilladlr` bounds the whole event, in place of the three named per-arm ε's of
`balanceSubsetPerTx_measure_le`, with no random-oracle model. -/
theorem orchardBalanceSubsetPerTx_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions)) (i : ℕ)
    {ε_sinsemilladlr : ℝ≥0∞}
    (hsin : A.toOuterMeasure
      (orchardRelationEvent spendAuthVerify bindingVerify issuance maxActions i) ≤ ε_sinsemilladlr) :
    A.toOuterMeasure (balanceSubsetViolation (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) i)
      ≤ ε_sinsemilladlr :=
  le_trans (MeasureTheory.measure_mono
    (balanceSubsetViolation_subset_relation spendAuthVerify bindingVerify issuance maxActions i)) hsin

/-- The all-prefixes Orchard relation event: at some step `i < k`, the reduction
computes a nontrivial discrete-log relation. -/
def orchardRelationEventUpTo (k : ℕ) :
    Set (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ orchardRelationEvent spendAuthVerify bindingVerify issuance maxActions i}

/-- A sample violating Balance-subset at some step lands in the all-prefixes relation
event, at that same step. -/
theorem balanceSubsetViolationUpTo_subset_relation (k : ℕ) :
    balanceSubsetViolationUpTo (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding)
        (issuance := issuance) (maxActions := maxActions) k
      ⊆ orchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions k := by
  rintro ω ⟨i, hik, hω⟩
  exact ⟨i, hik,
    balanceSubsetViolation_subset_relation spendAuthVerify bindingVerify issuance maxActions i hω⟩

/-- **The Orchard Balance-subset bound at every prefix, from one bound on the relation
event.** One `ε_sinsemilladlr`, hypothesized on the shared all-prefixes relation event,
bounds the Balance-subset violation at every step `i < k`, where the abstract bound names
three ε's per arm family: every step's break lands in the one relation event, a
nontrivial relation among the same fixed bases. -/
theorem orchardBalanceSubset_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions)) (k : ℕ)
    {ε_sinsemilladlr : ℝ≥0∞}
    (hsin : A.toOuterMeasure
      (orchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions k) ≤ ε_sinsemilladlr) :
    A.toOuterMeasure (balanceSubsetViolationUpTo (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) k)
      ≤ ε_sinsemilladlr :=
  le_trans (MeasureTheory.measure_mono
    (balanceSubsetViolationUpTo_subset_relation spendAuthVerify bindingVerify issuance maxActions k)) hsin

/-! ## The Orchard shielded pool is non-negative -/

/-- A negative shielded pool lands in the relation event: by spend integrity
(`shieldedPoolBalance_nonneg`) the Balance-subset containment forces a non-negative
pool, so a negative pool refutes the containment and the reduction returns a
relation. The one step/prefix crossing at the Orchard instantiation. -/
theorem shieldedBalanceNonNegativeViolation_succ_subset_relation (i : ℕ) :
    shieldedBalanceNonNegativeViolation (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) (i + 1)
      ⊆ orchardRelationEvent spendAuthVerify bindingVerify issuance maxActions i := by
  intro ω hω
  exact balanceSubsetViolation_subset_relation spendAuthVerify bindingVerify issuance maxActions i
    (fun hsub => hω (shieldedPoolBalance_nonneg ω.1 i hsub))

/-- **The Orchard shielded pool is non-negative, probabilistically.** For any
adversary over valid Orchard ledgers, the probability that the shielded pool goes
negative after the first `i + 1` transactions is at most the single
discrete-log-relation advantage `ε_sinsemilladlr`: no value is spent that was never
created. -/
theorem orchardShieldedBalanceNonNegative_succ_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions)) (i : ℕ)
    {ε_sinsemilladlr : ℝ≥0∞}
    (hsin : A.toOuterMeasure
      (orchardRelationEvent spendAuthVerify bindingVerify issuance maxActions i) ≤ ε_sinsemilladlr) :
    A.toOuterMeasure (shieldedBalanceNonNegativeViolation
        (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding) (issuance := issuance)
        (maxActions := maxActions) (i + 1))
      ≤ ε_sinsemilladlr :=
  le_trans (MeasureTheory.measure_mono
    (shieldedBalanceNonNegativeViolation_succ_subset_relation spendAuthVerify bindingVerify issuance
      maxActions i)) hsin

/-! ## Full Orchard Balance integrity -/

/-- **Full Orchard Balance, probabilistically.** Balance integrity holds after the
first `i` transactions — the shielded pool is non-negative and the pools sum to the
minted issuance — except with probability at most `ε_nonneg + ε_bindsig`. Discharge
`ε_nonneg` at successor prefixes with
`orchardShieldedBalanceNonNegative_succ_measure_le`, giving `ε_sinsemilladlr`: no
value is spent that was never created, except with the discrete-log-relation
advantage. `ε_bindsig` is a named hypothesis on the conservation event; its binding-signature
discharge is the conservation experiment's, in the challenge-oracle model. -/
theorem orchardBalanceIntegrityPerTx_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions)) (i : ℕ)
    {ε_nonneg ε_bindsig : ℝ≥0∞}
    (hnn : A.toOuterMeasure (shieldedBalanceNonNegativeViolation
        (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding) (issuance := issuance)
        (maxActions := maxActions) i) ≤ ε_nonneg)
    (hbind : A.toOuterMeasure (balanceConservationViolation
        (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding) (issuance := issuance)
        (maxActions := maxActions) i) ≤ ε_bindsig) :
    A.toOuterMeasure (balanceIntegrityPerTxViolation (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) i)
      ≤ ε_nonneg + ε_bindsig :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (balanceIntegrityPerTxViolation_subset (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) i))
    (add_le_add hnn hbind)

/-- An integrity violation at some prefix lands in the all-prefixes relation event
or the all-prefixes conservation violation: a negative pool at prefix `j + 1` lands
in the relation event at step `j` (the empty prefix cannot go negative), and a
conservation violation lands at its own prefix. One bound `k` serves the mixed
step-indexed (`UpTo`) and prefix-indexed (`Before`) right-hand side: the crossing
only produces steps `j` with `j + 1 < k`, so `j < k`. -/
theorem balanceIntegrityViolationBefore_subset_relation (k : ℕ) :
    balanceIntegrityViolationBefore (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding)
        (issuance := issuance) (maxActions := maxActions) k
      ⊆ orchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions k
        ∪ balanceConservationViolationBefore (P := primitives spendAuthVerify bindingVerify)
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) k := by
  rintro ω ⟨i, hik, hω⟩
  rcases not_and_or.mp hω with h | h
  · cases i with
    | zero => exact absurd (shieldedPoolBalance_zero ω.1).symm.le h
    | succ j =>
        exact Or.inl ⟨j, Nat.lt_of_succ_lt hik,
          shieldedBalanceNonNegativeViolation_succ_subset_relation spendAuthVerify bindingVerify
            issuance maxActions j h⟩
  · rcases not_and_or.mp h with h' | h'
    · exact absurd (ω.2.transparent_nonneg i) h'
    · exact Or.inr ⟨i, hik, h'⟩

/-- **Orchard Balance integrity at every prefix, from one bound per shared event.**
Balance integrity (the shielded pool is non-negative and the pools sum to the minted
issuance) holds at every prefix `i < k`, except with probability at most
`ε_sinsemilladlr + ε_bindsig` — the containment adds no factor of `k`. A naive union
bound over the prefixes would pay `k · ε`, but the prefix violations are not
independent: the reduction sends every step's break to a relation among the same fixed
Sinsemilla bases, so a break at any step lands in the one event
`orchardRelationEventUpTo`, on which `ε_sinsemilladlr` is hypothesized once. The
conservation side collapses the same way onto the one all-prefixes conservation event,
whose named bound is `ε_bindsig`. -/
theorem orchardBalanceIntegrity_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions)) (k : ℕ)
    {ε_sinsemilladlr ε_bindsig : ℝ≥0∞}
    (hsin : A.toOuterMeasure
      (orchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions k) ≤ ε_sinsemilladlr)
    (hbind : A.toOuterMeasure (balanceConservationViolationBefore
        (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding) (issuance := issuance)
        (maxActions := maxActions) k) ≤ ε_bindsig) :
    A.toOuterMeasure (balanceIntegrityViolationBefore (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) k)
      ≤ ε_sinsemilladlr + ε_bindsig :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (balanceIntegrityViolationBefore_subset_relation spendAuthVerify bindingVerify issuance maxActions k))
    (add_le_add hsin hbind)

/-! ## The Orchard Spend Authority key-binding arm -/

/-- **The Orchard-protocol Spend Authority key-binding break computes a discrete-log
relation.** The Spend Authority reduction's key-binding break is two valid `Commit^ivk`
openings of the same `ivk` that differ in the extracted `ak` coordinate, `nk`, or
`rivk` (`Witness.breakProjection`). At the Orchard `keyBinding` interface that break is
the `CommitIvkCollision` that `relationOfKeyBindingBreak` consumes, so the Spend
Authority key-binding arm reaches the same discrete-log terminal as the Balance
key-binding arm. The break is computed from the exhibited witness pair, and the
reduction needs no oracle model. -/
def relationOfSpendAuthorityKBBreak (brk : KeyBindingBreakData keyBinding) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  relationOfKeyBindingBreak brk.h

/-- The Orchard Spend Authority reduction with its key-binding arm routed to the
discrete-log terminal: as `spendAuthorityOrBreak`, with a key-binding break converted
to its nontrivial relation at the `CommitIvk` bases by
`relationOfSpendAuthorityKBBreak`. -/
def orchardSpendAuthorityOrRelation
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify) keyBinding
      issuance maxActions ledger)
    {tx} (htx : tx ∈ ledger) {a} (ha : a ∈ tx.actions)
    {wV : KeyBinding.Pool.Witness Fq PallasGroup Fp} (hKB : keyBinding.KB wV)
    (hrecv : a.w.note_old.pkd
      = (primitives spendAuthVerify bindingVerify).emb (keyBinding.ivk wV) • a.w.note_old.gd)
    {Signed : MSG → Prop} (hfresh : ¬ Signed tx.sighash) :
    SpendAuthForgery (primitives spendAuthVerify bindingVerify) (keyBinding.akP wV) Signed
      ⊕' NontrivialRelation (F := Fq) pallasS orchardPoints :=
  match spendAuthorityOrBreak hval htx ha hKB hrecv hfresh with
  | .inl f => .inl f
  | .inr b => .inr (relationOfSpendAuthorityKBBreak b)

/-- The Orchard Spend Authority relation event, for a victim key witness `wV` with
signing history `Signed`: the samples on which the reduction, run on an Action
spending a note addressed to `wV` over an unsigned sighash, computes a nontrivial
discrete-log relation at the `CommitIvk` bases. The firing Action is selected
existentially; #155 tracks the oracle-machine layer that connects the ε named on
this event to an adversary experiment and recovers the Action from the adversary's
announced indices. -/
def orchardSpendAuthorityRelationEvent (wV : KeyBinding.Pool.Witness Fq PallasGroup Fp)
    (hKB : keyBinding.KB wV) (Signed : MSG → Prop) :
    Set (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd
      = (primitives spendAuthVerify bindingVerify).emb (keyBinding.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ r,
    orchardSpendAuthorityOrRelation spendAuthVerify bindingVerify issuance maxActions ω.2 htx ha hKB
      hrecv hfresh = .inr r}

/-- A break-arm sample lands in the relation event: on it, the reduction's key-binding
break converts to a relation, so the composed reduction returns one. -/
theorem spendAuthorityBreakEvent_subset_relation
    (wV : KeyBinding.Pool.Witness Fq PallasGroup Fp) (hKB : keyBinding.KB wV)
    (Signed : MSG → Prop) :
    spendAuthorityBreakEvent (P := primitives spendAuthVerify bindingVerify) wV hKB Signed
      ⊆ orchardSpendAuthorityRelationEvent spendAuthVerify bindingVerify issuance maxActions wV hKB
          Signed := by
  rintro ω ⟨tx, htx, a, ha, hrecv, hfresh, b, hb⟩
  refine ⟨tx, htx, a, ha, hrecv, hfresh, relationOfSpendAuthorityKBBreak b, ?_⟩
  unfold orchardSpendAuthorityOrRelation
  rw [hb]

/-- **The Orchard Spend Authority probability bound.** For any adversary over valid
Orchard ledgers, the probability that some Action spends a note addressed to `wV` over
a sighash the holder of `wV` never signed is at most the forgery arm's ε plus the
discrete-log-relation advantage at the `CommitIvk` bases: the key-binding arm's
hypothesis is named on the relation event — every break-arm sample computes a relation
(`spendAuthorityBreakEvent_subset_relation`) — with no oracle model. The forgery arm's
ε is RedDSA ±-randomized unforgeability, a named hypothesis. -/
theorem orchardSpendAuthority_measure_le
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions))
    (wV : KeyBinding.Pool.Witness Fq PallasGroup Fp) (hKB : keyBinding.KB wV)
    (Signed : MSG → Prop) {ε_forge ε_sinsemilladlr : ℝ≥0∞}
    (hf : A.toOuterMeasure
      (spendAuthorityForgeryEvent (P := primitives spendAuthVerify bindingVerify) wV hKB Signed)
        ≤ ε_forge)
    (hsin : A.toOuterMeasure
      (orchardSpendAuthorityRelationEvent spendAuthVerify bindingVerify issuance maxActions wV hKB
        Signed) ≤ ε_sinsemilladlr) :
    A.toOuterMeasure
      (spendAuthorityViolation (P := primitives spendAuthVerify bindingVerify) wV Signed)
      ≤ ε_forge + ε_sinsemilladlr :=
  spendAuthority_measure_le A wV hKB Signed hf
    (le_trans (MeasureTheory.measure_mono
      (spendAuthorityBreakEvent_subset_relation spendAuthVerify bindingVerify issuance maxActions wV
        hKB Signed)) hsin)

/-! ## The Orchard conservation arm in extractor-plus-knowledge-error form -/

/-- **Orchard value conservation with a fallible extractor.** For any adversary, any
Pedersen `shape` and RedDSA shape `binding` of the binding-signature primitives, and any
candidate `extractor`, the probability that the ledger fails to balance at some
prefix `i < k` is at most `ε_dlr + κ`: the `(Vbase, Rbase)` discrete-log-relation advantage
plus the knowledge error, with no factor of `k`. The no-overflow premiss bounds the
net value against the Pallas scalar order `r_ℙ`. Nothing is assumed of the extractor:
its failures are exhibited on the extraction-failure arm. -/
theorem orchardBalanceConservationBefore_measure_le_kerr
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions))
    (shape : ValueShape (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify))
    (binding : BindingSigShape (primitives spendAuthVerify bindingVerify) shape)
    (hr : maxActions
          * ((primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify).valueBound - 1)
        + (primitives spendAuthVerify bindingVerify).vBalanceBound
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD)
    (extractor : RedDSA.Extractor Fq PallasGroup MSG) (k : ℕ) {ε_dlr κ : ℝ≥0∞}
    (hdlr :
      A.toOuterMeasure (valueRelationEventBefore keyBinding shape binding hr extractor k) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore keyBinding shape binding hr extractor k) ≤ κ) :
    A.toOuterMeasure (balanceConservationViolationBefore
        (P := primitives spendAuthVerify bindingVerify) (kv := keyBinding) (issuance := issuance)
        (maxActions := maxActions) k)
      ≤ ε_dlr + κ :=
  balanceConservationBefore_measure_le_kerr A shape binding hr extractor k hdlr hκ

/-- **Orchard Balance integrity in extractor-plus-knowledge-error form.** Balance
integrity holds at every prefix `i < k`, except with probability at most
`ε_sinsemilladlr + ε_dlr + κ`: the Sinsemilla discrete-log-relation advantage covers
the non-negativity side, and the conservation side is covered by the `(Vbase, Rbase)`
discrete-log-relation advantage plus the extractor's knowledge error, in place of
`orchardBalanceIntegrity_measure_le`'s named `ε_bindsig`. -/
theorem orchardBalanceIntegrity_measure_le_kerr
    (A : PMF (OrchardAnnotated spendAuthVerify bindingVerify issuance maxActions))
    (shape : ValueShape (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify))
    (binding : BindingSigShape (primitives spendAuthVerify bindingVerify) shape)
    (hr : maxActions
          * ((primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify).valueBound - 1)
        + (primitives spendAuthVerify bindingVerify).vBalanceBound
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD)
    (extractor : RedDSA.Extractor Fq PallasGroup MSG) (k : ℕ)
    {ε_sinsemilladlr ε_dlr κ : ℝ≥0∞}
    (hsin : A.toOuterMeasure
      (orchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions k) ≤ ε_sinsemilladlr)
    (hdlr :
      A.toOuterMeasure (valueRelationEventBefore keyBinding shape binding hr extractor k) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore keyBinding shape binding hr extractor k) ≤ κ) :
    A.toOuterMeasure (balanceIntegrityViolationBefore (P := primitives spendAuthVerify bindingVerify)
        (kv := keyBinding) (issuance := issuance) (maxActions := maxActions) k)
      ≤ ε_sinsemilladlr + ε_dlr + κ := by
  rw [add_assoc]
  exact le_trans
    (toOuterMeasure_le_add₂ A
      (balanceIntegrityViolationBefore_subset_relation spendAuthVerify bindingVerify issuance
        maxActions k))
    (add_le_add hsin
      (balanceConservationBefore_measure_le_kerr A shape binding hr extractor k hdlr hκ))

end Zcash.Security.Ledger.Bridge
