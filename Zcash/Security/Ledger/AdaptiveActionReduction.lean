import Zcash.Common.RelationProbabilityCoins
import Zcash.Snark.Soundness.Action.AdaptiveCountReduction

/-!
# Ledger composition for adaptive Action extraction

This is the ledger-side reduction shell for issue #214.  One online-AGM
adversary emits all ledger slots under one random-oracle table and one query
budget.  Each slot may choose its own Action count after arbitrary oracle
queries.  `combinedRelationFinder` returns the first relation exposed by any
actually emitted slot.

The final theorem has the form

`DLOG + 1 / #Fp + sum(slot statistical error)`.

In particular, neither the number of ledger slots nor `maxActions` multiplies
the DLOG advantage.  Those cardinalities can occur only inside the separately
supplied statistical remainder.
-/

namespace Zcash.Security.Ledger.AdaptiveActionReduction

open Classical
open Zcash.Common
open Zcash.Snark
open Zcash.Snark.Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

/-- Outputs for every ledger slot, with each slot carrying its own adaptively
selected Action count. -/
abbrev Outputs (k maxActions : ℕ)
    (components : Fin k → (n : Fin maxActions) →
      ComputedAdaptiveActionStatementFSFamily (adaptiveActionCountParams n))
    (basis : AdaptiveActionCountBasis) :=
  (slot : Fin k) → AdaptiveActionCountOutput maxActions (components slot) basis

/-- One stateful proof-emitting ledger adversary.  Counts and slots share the
same oracle computation and the same global query budget `Q`. -/
structure Family (k maxActions : ℕ) where
  components : Fin k → (n : Fin maxActions) →
    ComputedAdaptiveActionStatementFSFamily (adaptiveActionCountParams n)
  adversary : (basis : AdaptiveActionCountBasis) →
    LabeledOracleComp (AdaptiveActionCountTranscript maxActions) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis)
      (Outputs k maxActions components basis)
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace Family

abbrev Coins {k maxActions : ℕ} (_family : Family k maxActions) :=
  AdaptiveActionCountTranscript maxActions → Fp

/-- Project the shared ledger run to one slot.  This is a view of the same
program and table, not a separately sampled per-slot oracle. -/
def slotFamily {k maxActions : ℕ} (family : Family k maxActions) (slot : Fin k) :
    ComputedAdaptiveActionCountFSFamily maxActions where
  components := family.components slot
  adversary := fun basis => (family.adversary basis).bind fun outputs =>
    .pure (outputs slot)
  Q := family.Q
  queryBound := by
    intro basis
    rw [LabeledOracleComp.QueryBound, LabeledOracleComp.erase_bind]
    simpa only [Nat.add_zero] using
      OracleComp.queryBound_bind (family.queryBound basis)
        (fun outputs => OracleComp.QueryBound.pure (outputs slot) 0)

/-- One relation finder covering every emitted ledger slot. -/
def combinedRelationFinder {k maxActions : ℕ} (family : Family k maxActions) :
    (basis : AdaptiveActionCountBasis) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
      (shape := AdaptiveActionStatementShape (actionProofParamsFor 1))
      (List.ofFn fun slot => (family.slotFamily slot).selectedRelationFinder basis O)

/-- If any slot exposes a relation, the combined finder exposes one. -/
theorem combinedRelationFinder_isSome_of_slot {k maxActions : ℕ}
    (family : Family k maxActions) (slot : Fin k)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (hslot : ((family.slotFamily slot).selectedRelationFinder basis O).isSome) :
    (family.combinedRelationFinder basis O).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  intro hnone
  unfold combinedRelationFinder at hnone
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  have hslotNone := hall
    ((family.slotFamily slot).selectedRelationFinder basis O)
    (List.mem_ofFn.mpr ⟨slot, rfl⟩)
  rw [hslotNone] at hslot
  exact Bool.false_ne_true hslot

/-- Sample space before replacing the sampled scalar basis by group points. -/
abbrev ScalarSample {k maxActions : ℕ} (family : Family k maxActions) :=
  (AugmentedIndex (2 ^ actionCircuit.shape.k) → Fp) × family.Coins

/-- Sample space seen by the algebraic relation finders. -/
abbrev GroupSample {k maxActions : ℕ} (family : Family k maxActions) :=
  AdaptiveActionCountBasis × family.Coins

/-- Pull a group-basis event back to the uniform scalar-basis experiment. -/
def scalarEvent {k maxActions : ℕ} (family : Family k maxActions) (B : VestaG)
    (event : Set family.GroupSample) : Set family.ScalarSample :=
  (fun q => (scalarBasis B q.1, q.2)) ⁻¹' event

/-- The exact relation event of the one combined ledger finder. -/
def combinedRelationEvent {k maxActions : ℕ} (family : Family k maxActions) :
    Set family.GroupSample :=
  {q | (family.combinedRelationFinder q.1 q.2).isSome}

/-- A per-slot relation event is contained in the one combined relation event. -/
theorem slotRelationEvent_subset_combined {k maxActions : ℕ}
    (family : Family k maxActions) (slot : Fin k) :
    {q : family.GroupSample |
      ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} ⊆
        family.combinedRelationEvent := by
  intro q hq
  exact family.combinedRelationFinder_isSome_of_slot slot q.1 q.2 hq

/-- Textbook DLOG prices the combined ledger relation event exactly once. -/
theorem combinedRelationEvent_prob_le_of_textbookDL {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG) {dlBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B family.combinedRelationEvent) ≤
      dlBound + 1 / Fintype.card Fp := by
  simpa [scalarEvent, combinedRelationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B family.combinedRelationFinder hDL)

/-- Union of the extraction failures among the actually emitted ledger slots. -/
def ledgerFailureEvent {k maxActions : ℕ} (family : Family k maxActions)
    (failure : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ slot, failure slot

/-- Union of the per-emitted-slot statistical residuals. -/
def ledgerStatisticalEvent {k maxActions : ℕ} (family : Family k maxActions)
    (statistical : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ slot, statistical slot

/-- Distribution-free composition: if each emitted slot's failure is either a
relation or its statistical residual, every ledger failure is covered by the
single combined relation event plus the union of those residuals. -/
theorem ledgerFailureEvent_subset {k maxActions : ℕ}
    (family : Family k maxActions)
    (failure statistical : Fin k → Set family.GroupSample)
    (hslot : ∀ slot, failure slot ⊆
      {q | ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical slot) :
    family.ledgerFailureEvent failure ⊆
      family.combinedRelationEvent ∪ family.ledgerStatisticalEvent statistical := by
  intro q hq
  obtain ⟨slot, hfailure⟩ := Set.mem_iUnion.mp hq
  rcases hslot slot hfailure with hrelation | hstatistical
  · exact Or.inl (family.slotRelationEvent_subset_combined slot hrelation)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨slot, hstatistical⟩)

/-- **Ledger reduction with no slot/count multiplier on DLOG.**  One textbook
DLOG assumption covers all slots.  Only the statistical remainders are summed. -/
theorem ledgerFailureEvent_prob_le {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG)
    (failure statistical : Fin k → Set family.GroupSample)
    (hslot : ∀ slot, failure slot ⊆
      {q | ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical slot)
    {dlBound : ENNReal} (epsilon : Fin k → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical slot)) ≤ epsilon slot) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerFailureEvent failure)) ≤
      (dlBound + 1 / Fintype.card Fp) + ∑ slot, epsilon slot := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (family.ledgerFailureEvent_subset failure statistical hslot))) ?_
  rw [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  apply add_le_add
  · exact family.combinedRelationEvent_prob_le_of_textbookDL B hDL
  · unfold ledgerStatisticalEvent
    simp only [Set.preimage_iUnion]
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    rw [tsum_fintype]
    exact Finset.sum_le_sum fun slot _ => hstat slot

/-- Uniform per-slot form.  The visible `k` multiplies only the statistical
error; `maxActions` and `k` still do not multiply `dlBound`. -/
theorem ledgerFailureEvent_prob_le_uniform {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG)
    (failure statistical : Fin k → Set family.GroupSample)
    (hslot : ∀ slot, failure slot ⊆
      {q | ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical slot)
    {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical slot)) ≤ epsilon) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerFailureEvent failure)) ≤
      (dlBound + 1 / Fintype.card Fp) + (k : ENNReal) * epsilon := by
  simpa using family.ledgerFailureEvent_prob_le B failure statistical hslot
    (fun _ => epsilon) hDL hstat

/-- The actual Action knowledge-failure union for the emitted ledger slots. -/
def ledgerKnowledgeFailureEvent {k maxActions : ℕ} (family : Family k maxActions) :
    Set family.GroupSample :=
  family.ledgerFailureEvent fun slot =>
    (family.slotFamily slot).selectedKnowledgeFailureEvent

/-- The no-relation statistical residuals for the emitted ledger slots. -/
def ledgerActionStatisticalFailureEvent {k maxActions : ℕ}
    (family : Family k maxActions) : Set family.GroupSample :=
  family.ledgerStatisticalEvent fun slot =>
    (family.slotFamily slot).selectedStatisticalFailureEvent

/-- The Action-specific distribution-free split used by the ledger endpoint. -/
theorem ledgerKnowledgeFailureEvent_subset {k maxActions : ℕ}
    (family : Family k maxActions) :
    family.ledgerKnowledgeFailureEvent ⊆
      family.combinedRelationEvent ∪ family.ledgerActionStatisticalFailureEvent := by
  exact family.ledgerFailureEvent_subset
    (fun slot => (family.slotFamily slot).selectedKnowledgeFailureEvent)
    (fun slot => (family.slotFamily slot).selectedStatisticalFailureEvent)
    (fun slot => (family.slotFamily slot).selectedKnowledgeFailureEvent_subset)

/-- **Action knowledge soundness composed at the ledger reduction layer.**
The caller supplies a bound only for each slot's no-relation statistical
residual.  The conclusion charges the combined DLOG finder once and multiplies
only that residual by the number of emitted ledger slots. -/
theorem ledgerKnowledgeFailureEvent_prob_le {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG) {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilon) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B family.ledgerKnowledgeFailureEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + (k : ENNReal) * epsilon := by
  exact family.ledgerFailureEvent_prob_le_uniform B
    (fun slot => (family.slotFamily slot).selectedKnowledgeFailureEvent)
    (fun slot => (family.slotFamily slot).selectedStatisticalFailureEvent)
    (fun slot => (family.slotFamily slot).selectedKnowledgeFailureEvent_subset)
    hDL hstat

/-- The extraction arm used by a ledger proof: Action knowledge failure or an
explicit ledger-bridge escape at one of the emitted slots. -/
def ledgerExtractionFailureEvent {k maxActions : ℕ} (family : Family k maxActions)
    (escape : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  family.ledgerFailureEvent fun slot =>
    (family.slotFamily slot).selectedKnowledgeFailureEvent ∪ escape slot

/-- The statistical side of ledger extraction: the selected Action surfaces plus
the independently priced ledger-bridge escape for each emitted slot. -/
def ledgerExtractionStatisticalEvent {k maxActions : ℕ} (family : Family k maxActions)
    (escape : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  family.ledgerStatisticalEvent fun slot =>
    (family.slotFamily slot).selectedStatisticalFailureEvent ∪ escape slot

/-- Concrete extraction failures are covered by one combined relation event and
only per-slot statistical/bridge events. -/
theorem ledgerExtractionFailureEvent_subset {k maxActions : ℕ}
    (family : Family k maxActions) (escape : Fin k → Set family.GroupSample) :
    family.ledgerExtractionFailureEvent escape ⊆
      family.combinedRelationEvent ∪ family.ledgerExtractionStatisticalEvent escape := by
  apply family.ledgerFailureEvent_subset
  intro slot q hq
  rcases hq with hknowledge | hescape
  · rcases (family.slotFamily slot).selectedKnowledgeFailureEvent_subset hknowledge with
      hrelation | hstatistical
    · exact Or.inl hrelation
    · exact Or.inr (Or.inl hstatistical)
  · exact Or.inr (Or.inr hescape)

/-- **Ledger extraction with the issue #214 loss removed.** The DLOG term is
charged once. The number of emitted slots multiplies only the Action statistical
surface bound and the ledger-bridge escape bound; `maxActions` is absent. -/
theorem ledgerExtractionFailureEvent_prob_le {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG)
    (escape : Fin k → Set family.GroupSample)
    {dlBound epsilonStat epsilonEscape : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (escape slot)) ≤ epsilonEscape) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerExtractionFailureEvent escape)) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (k : ENNReal) * (epsilonStat + epsilonEscape) := by
  apply family.ledgerFailureEvent_prob_le_uniform B
    (fun slot => (family.slotFamily slot).selectedKnowledgeFailureEvent ∪ escape slot)
    (fun slot => (family.slotFamily slot).selectedStatisticalFailureEvent ∪ escape slot)
  · intro slot q hq
    rcases hq with hknowledge | hesc
    · rcases (family.slotFamily slot).selectedKnowledgeFailureEvent_subset hknowledge with
        hrelation | hstatistical
      · exact Or.inl hrelation
      · exact Or.inr (Or.inl hstatistical)
    · exact Or.inr (Or.inr hesc)
  · exact hDL
  · intro slot
    unfold scalarEvent
    rw [Set.preimage_union]
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    exact add_le_add (hstat slot) (hescape slot)

end Family
end Zcash.Security.Ledger.AdaptiveActionReduction
