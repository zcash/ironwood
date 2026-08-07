import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Probability.Distributions.Uniform
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.Value
import Zcash.Security.RedDSA.Extraction

/-!
# The transaction-balance premiss with a fallible extractor

The transaction-balance premiss discharge, in extractor-plus-knowledge-error form:
the extractor is an arbitrary *function*, its failures are *exhibited*, and the
capstones bound the violation probability by `εdlr + κ` — equivalently, a violation
yields a computed `(Vbase, Rbase)` relation with probability at least `Pr[violation] − κ`.
A total extraction hypothesis would be classically satisfiable and carry no
computational content (see the module doc of `Zcash.Security.Ledger.Value`).

* `BindingSigShape` pins `Primitives.bindingVerify` to an abstract RedDSA scheme
  based at the randomness base `Rbase` (`Zcash.Security.RedDSA.Basic`) — the spec's
  demand that a binding signature "prove knowledge of the discrete logarithm of the
  validating key with respect to the base ℛ" (§5.4.7.2) is then a statement about
  this scheme.
* `ValueShape.premissOrBreakFallible` decides the per-transaction net-value equation
  and, on failure, runs the extractor: *either* it pins `bvk` and the witnessed
  bundle computes the nontrivial `(Vbase, Rbase)` relation, *or* the transaction's verifying
  binding signature is an exhibited `RedDSA.ExtractionFailure` — the knowledge-error
  event, as data.
* `balanceConservation_measure_le_kerr` / `shieldedBalanceCap_measure_le_kerr`
  compose the three-way premiss into the probabilistic capstones:
  violation ≤ `εdlr + κ`, with `εdlr` bounding the relation arm (discharged onward
  against DL hardness via the AGM layer) and `κ` bounding the extraction-failure
  arm.

What stays named: `κ` itself — the RedDSA knowledge error, the probability that an
adversary produces a verifying signature that the extractor misses. The known
discharge routes and their losses are described in the module doc of
`Zcash.Security.RedDSA.Basic`. None is chosen here. The `Extractor` interface
consumes only the verifying triple `(vk, m, σ)`: a straight-line AGM discharge
extracts from an algebraic adversary's representations and a rewinding discharge
re-runs the adversary, so a discharge would widen the interface or restate the
bound per adversary.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature
open scoped ENNReal

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The RedDSA shape of the binding-signature primitive: an abstract scheme based at
the value-commitment randomness base `Rbase` whose verification equation is what
`bindingVerify` computes, with `toSig` decoding the model's opaque signature type.
The signature-side counterpart of the same shape's `ValueShape` commitment side. -/
structure BindingSigShape (P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
    (S : ValueShape P) where
  sch : RedDSA.Scheme (ZMod r) G MSG
  toSig : SIG → RedDSA.Sig (ZMod r) G
  base_eq : sch.base = S.Rbase
  verify_iff : ∀ (bvk : G) (m : MSG) (σ : SIG),
    P.bindingVerify bvk m σ ↔ sch.Verify bvk m (toSig σ)

/-- **The transaction-balance premiss discharge, with a fallible extractor.** Decide
the per-transaction net-value equation. On failure, run the extractor `E` on the
transaction's verifying binding signature. If `E` pins `bvk = [bsk] Rbase`, the witnessed
bundle computes the nontrivial `(Vbase, Rbase)` relation, with the no-overflow bound `hr`.
Otherwise the failure is exhibited as a `RedDSA.ExtractionFailure`: a verifying
signature whose key the extractor misses — the event that the knowledge error `κ`
bounds. Nothing is assumed of `E`. -/
def ValueShape.premissOrBreakFallible [DecidableEq G]
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (S : ValueShape P) (B : BindingSigShape P S)
    (hval : ValidLedger P kv issuance maxActions ledger)
    -- + 1 is for the valueBalance
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth) (htx : tx ∈ ledger) :
    (txNetValue tx = tx.vBalance)
      ⊕' (BindingSignature.NontrivialRelation (F := ZMod r) S.Vbase S.Rbase
          ⊕' RedDSA.ExtractionFailure B.sch E) :=
  if heq : txNetValue tx = tx.vBalance then .inl heq
  else if hex : tx.bvk P = E (tx.bvk P) tx.sighash (B.toSig tx.bindingSig) • S.Rbase then
    .inr (.inl (NontrivialRelation.ofBundleIntImbalance S.Vbase S.Rbase (txBundle tx) [] tx.vBalance
      (E (tx.bvk P) tx.sighash (B.toSig tx.bindingSig))
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        exact sub_ne_zero.mpr heq)
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        have h1 := txNetValue_natAbs_le (P := P) (kv := kv) (hval.satisfied tx htx)
        have h2 := hval.vbalance_bound tx htx
        have hb : tx.actions.length * P.valueBound ≤ maxActions * P.valueBound :=
          Nat.mul_le_mul_right _ (hval.action_bound tx htx)
        calc (txNetValue tx - tx.vBalance).natAbs
            ≤ (txNetValue tx).natAbs + tx.vBalance.natAbs := Int.natAbs_sub_le _ _
          _ < maxActions * P.valueBound + P.valueBound :=
              Nat.add_lt_add_of_le_of_lt (le_trans h1 hb) h2
          _ = (maxActions + 1) * P.valueBound := by ring
          _ ≤ r := hr)
      ((bvk_eq S (hval.satisfied tx htx)).symm.trans hex)))
  else
    .inr (.inr ⟨tx.bvk P, tx.sighash, B.toSig tx.bindingSig,
      (B.verify_iff _ _ _).mp (hval.binding_verified tx htx),
      by rw [B.base_eq]; exact hex⟩)

section Capstone

variable [DecidableEq G]

variable (kv) in
/-- `premissOrBreakFallible` as the per-sample premiss the probabilistic capstones
consume, at the break type `NontrivialRelation ⊕' ExtractionFailure`. -/
def txBalancePremissFallible (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG)
    (ω : ValidAnnotated P kv issuance maxActions)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth) (htx : tx ∈ ω.1) :
    (txNetValue tx = tx.vBalance)
      ⊕' (BindingSignature.NontrivialRelation (F := ZMod r) S.Vbase S.Rbase
          ⊕' RedDSA.ExtractionFailure B.sch E) :=
  S.premissOrBreakFallible B ω.2 hr E tx htx

variable (kv) in
/-- The relation arm: the samples on which the conservation reduction computes a
nontrivial `(Vbase, Rbase)` relation. Bounded onward by DL hardness (via the AGM layer's
relation-to-DL handoff); its named bound is the `εdlr` slot. -/
def valueRelationEvent (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b, balanceConservationOrBreak (issuance := issuance)
    (txBalancePremissFallible kv S B hr E ω) i = .inr (.inl b)}

variable (kv) in
/-- The extraction-failure arm: the samples on which the reduction exhibits a
verifying binding signature whose key the extractor misses
(`RedDSA.ExtractionFailure`, carried as data in the branch). Its named bound is the
knowledge error `κ`. -/
def extractFailEvent (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ e, balanceConservationOrBreak (issuance := issuance)
    (txBalancePremissFallible kv S B hr E ω) i = .inr (.inr e)}

/-- Every sample of the extraction-failure arm exhibits a `RedDSA.ExtractionFailure`:
the arm's named `κ` is a bound on the adversary's probability of beating the
extractor, and nothing else. -/
theorem extractFailEvent_failure (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {ω : ValidAnnotated P kv issuance maxActions}
    (hω : ω ∈ extractFailEvent kv S B hr E i) :
    Nonempty (RedDSA.ExtractionFailure B.sch E) := by
  obtain ⟨e, _⟩ := hω
  exact ⟨e⟩

/-- The transaction-balance premiss arm splits into the relation arm and the
extraction-failure arm. -/
theorem txBalanceBreakEvent_fallible_subset (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    txBalanceBreakEvent (txBalancePremissFallible (issuance := issuance) kv S B hr E) i
      ⊆ valueRelationEvent kv S B hr E i ∪ extractFailEvent kv S B hr E i := by
  rintro ω ⟨b, hb⟩
  cases b with
  | inl rel => exact Or.inl ⟨rel, hb⟩
  | inr e => exact Or.inr ⟨e, hb⟩

/-- **Value conservation in extractor-plus-knowledge-error form.** For any adversary
and any extractor `E`, the probability that the value ledger fails to balance is at
most `εdlr + κ`: the relation arm's bound plus the knowledge error. Read
contrapositively, a violation computes a nontrivial `(Vbase, Rbase)` relation with
probability at least `Pr[violation] − κ` — the extraction succeeds up to the
knowledge error, which is the form a forking discharge of `κ` composes with. -/
theorem balanceConservation_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) {εdlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEvent kv S B hr E i) ≤ εdlr)
    (hκ : A.toOuterMeasure (extractFailEvent kv S B hr E i) ≤ κ) :
    A.toOuterMeasure (balanceConservationViolation i) ≤ εdlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (le_trans (balanceConservationViolation_subset (txBalancePremissFallible kv S B hr E) i)
        (txBalanceBreakEvent_fallible_subset S B hr E i)))
    (add_le_add hdlr hκ)

/-- **Balance-value in extractor-plus-knowledge-error form.** As
`balanceConservation_measure_le_kerr`, for the shielded pool exceeding the minted
issuance. -/
theorem shieldedBalanceCap_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) {εdlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEvent kv S B hr E i) ≤ εdlr)
    (hκ : A.toOuterMeasure (extractFailEvent kv S B hr E i) ≤ κ) :
    A.toOuterMeasure (shieldedBalanceCapViolation i) ≤ εdlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (le_trans (shieldedBalanceCapViolation_subset (txBalancePremissFallible kv S B hr E) i)
        (txBalanceBreakEvent_fallible_subset S B hr E i)))
    (add_le_add hdlr hκ)

/-! ### All prefixes -/

variable (kv) in
/-- The all-prefixes relation arm: at some prefix `i < k`, the conservation reduction
computes a nontrivial `(Vbase, Rbase)` relation. -/
def valueRelationEventBefore (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ valueRelationEvent kv S B hr E i}

variable (kv) in
/-- The all-prefixes extraction-failure arm: at some prefix `i < k`, the reduction
exhibits a verifying binding signature whose key the extractor misses. -/
def extractFailEventBefore (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ extractFailEvent kv S B hr E i}

/-- A conservation violation at some prefix lands in the all-prefixes relation arm or
the all-prefixes extraction-failure arm, at that same prefix. -/
theorem balanceConservationViolationBefore_subset_fallible (S : ValueShape P)
    (B : BindingSigShape P S) (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ valueRelationEventBefore kv S B hr E k
        ∪ extractFailEventBefore kv S B hr E k := by
  rintro ω ⟨i, hik, hω⟩
  rcases txBalanceBreakEvent_fallible_subset S B hr E i
      (balanceConservationViolation_subset (txBalancePremissFallible kv S B hr E) i hω)
    with h | h
  · exact Or.inl ⟨i, hik, h⟩
  · exact Or.inr ⟨i, hik, h⟩

/-- A cap violation at some prefix lands in the same two all-prefixes arms. -/
theorem shieldedBalanceCapViolationBefore_subset_fallible (S : ValueShape P)
    (B : BindingSigShape P S) (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    shieldedBalanceCapViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ valueRelationEventBefore kv S B hr E k
        ∪ extractFailEventBefore kv S B hr E k := by
  rintro ω ⟨i, hik, hω⟩
  rcases txBalanceBreakEvent_fallible_subset S B hr E i
      (shieldedBalanceCapViolation_subset (txBalancePremissFallible kv S B hr E) i hω)
    with h | h
  · exact Or.inl ⟨i, hik, h⟩
  · exact Or.inr ⟨i, hik, h⟩

/-- **All-prefixes value conservation in extractor-plus-knowledge-error form.** The
probability that the ledger fails to balance at some prefix `i < k` is at most
`εdlr + κ`, with no factor of `k`: every prefix's violation lands in the one
all-prefixes relation arm or the one all-prefixes extraction-failure arm. -/
theorem balanceConservationBefore_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) {εdlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEventBefore kv S B hr E k) ≤ εdlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore kv S B hr E k) ≤ κ) :
    A.toOuterMeasure (balanceConservationViolationBefore (P := P) (kv := kv)
        (issuance := issuance) (maxActions := maxActions) k) ≤ εdlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (balanceConservationViolationBefore_subset_fallible S B hr E k))
    (add_le_add hdlr hκ)

/-- **All-prefixes shielded-balance cap in extractor-plus-knowledge-error form.** As
`balanceConservationBefore_measure_le_kerr`, for the shielded pool exceeding the
minted issuance at some prefix. -/
theorem shieldedBalanceCapBefore_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) {εdlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEventBefore kv S B hr E k) ≤ εdlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore kv S B hr E k) ≤ κ) :
    A.toOuterMeasure (shieldedBalanceCapViolationBefore (P := P) (kv := kv)
        (issuance := issuance) (maxActions := maxActions) k) ≤ εdlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (shieldedBalanceCapViolationBefore_subset_fallible S B hr E k))
    (add_le_add hdlr hκ)

end Capstone

end Zcash.Security.Ledger.Model
