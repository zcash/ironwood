import Zcash.Common.RelationProbabilityCoins
import Zcash.Security.Ledger.Capstone
import Zcash.Snark.Soundness.Action.AdaptiveCountReduction

/-!
# Ledger composition for adaptive Action extraction

One online-AGM adversary emits the Action proofs of every ledger slot under one
random-oracle table and one query budget, and each slot may choose its own Action
count after arbitrary oracle queries.

The module follows the recipe of the book's Security Models page ("How the layers
compose"). The computable reductions compose first: `combinedRelationFinder` returns
the first relation that any slot's run exposes, so its event is the union of the slots'
relation events (`combinedRelationEvent_eq_iUnion`), and one discrete-log hypothesis on
that finder covers every slot. The containments come next (the `…_subset` lemmas):
each slot's failure is covered by its relation event and its statistical residual, so
the union of the failures is covered by the one combined relation event and the union
of the residuals; these hold for every sample. Probability enters once, in
`event_prob_le_of_subset`: `scalarEvent` lifts an event from the group basis to the
scalar sample, the lift is a preimage and so preserves inclusions and unions, and the
measure's monotonicity and subadditivity give the bound

`DLOG + 1 / |Fp| + (the sum over slots of that slot's statistical bound)`.

Neither the number of slots nor `maxActions` multiplies the discrete-log advantage;
those cardinalities can enter only through the separately supplied statistical bounds.
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

/-- The sample space before replacing the sampled scalar basis by group points. -/
abbrev ScalarSample {k maxActions : ℕ} (family : Family k maxActions) :=
  (ActionBasisIndex → Fp) × family.Coins

/-- The sample space seen by the algebraic relation finders. -/
abbrev GroupSample {k maxActions : ℕ} (family : Family k maxActions) :=
  AdaptiveActionCountBasis × family.Coins

/-- The lift of a group-basis event to the uniform scalar-basis experiment: a preimage,
so it preserves inclusions and unions. -/
def scalarEvent {k maxActions : ℕ} (family : Family k maxActions) (B : VestaG)
    (event : Set family.GroupSample) : Set family.ScalarSample :=
  (fun q => (scalarBasis B q.1, q.2)) ⁻¹' event

/-- The exact relation event of the one combined ledger finder. -/
def combinedRelationEvent {k maxActions : ℕ} (family : Family k maxActions) :
    Set family.GroupSample :=
  {q | (family.combinedRelationFinder q.1 q.2).isSome}

/-- The combined finder's event is the union of the slots' relation events: the finder
takes the first relation that any slot exposes, so it exposes one exactly when some slot
does. -/
theorem combinedRelationEvent_eq_iUnion {k maxActions : ℕ}
    (family : Family k maxActions) :
    family.combinedRelationEvent =
      ⋃ slot, {q : family.GroupSample |
        ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} := by
  ext q
  simp only [combinedRelationEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hsome
    by_contra hnone
    rw [not_exists] at hnone
    have hall : ∀ r ∈ List.ofFn fun slot =>
        (family.slotFamily slot).selectedRelationFinder q.1 q.2, r = none := by
      intro r hr
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hr
      exact Option.not_isSome_iff_eq_none.mp (hnone slot)
    have hcombined : family.combinedRelationFinder q.1 q.2 = none :=
      (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).2 hall
    rw [hcombined] at hsome
    exact Bool.false_ne_true hsome
  · rintro ⟨slot, hslot⟩
    exact family.combinedRelationFinder_isSome_of_slot slot q.1 q.2 hslot

/-- A per-slot relation event is contained in the one combined relation event. -/
theorem slotRelationEvent_subset_combined {k maxActions : ℕ}
    (family : Family k maxActions) (slot : Fin k) :
    {q : family.GroupSample |
      ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome} ⊆
        family.combinedRelationEvent := by
  rw [family.combinedRelationEvent_eq_iUnion]
  exact Set.subset_iUnion (fun slot => {q : family.GroupSample |
    ((family.slotFamily slot).selectedRelationFinder q.1 q.2).isSome}) slot

/-- Under the uniform scalar sample, the probability of the combined ledger relation
event is at most the textbook discrete-log bound on the combined finder plus `1 / |Fp|`,
with no factor for the number of slots. -/
theorem combinedRelationEvent_prob_le_of_textbookDL {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG) {dlBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B family.combinedRelationEvent) ≤
      dlBound + 1 / Fintype.card Fp := by
  rw [show family.scalarEvent B family.combinedRelationEvent =
      ↑(relSetWithCoins B family.combinedRelationFinder) from
    Set.ext fun q => by
      simp only [scalarEvent, combinedRelationEvent, relSetWithCoins, Set.mem_preimage,
        Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]]
  exact relationWithCoins_prob_le_of_textbookDL B family.combinedRelationFinder hDL

/-- Union of the extraction failures among the actually emitted ledger slots. -/
def ledgerFailureEvent {k maxActions : ℕ} (family : Family k maxActions)
    (failure : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ slot, failure slot

/-- Union of the per-emitted-slot statistical residuals. -/
def ledgerStatisticalEvent {k maxActions : ℕ} (family : Family k maxActions)
    (statistical : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ slot, statistical slot

/-- A set inclusion, holding for every sample without reference to a distribution: if
each emitted slot's failure event is covered by that slot's relation event together
with its statistical residual, then the union of the slots' failures is covered by the
single combined relation event together with the union of the residuals. -/
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

/-- **The one pricing step.** Any event covered by the combined relation event and a union
of per-slot residuals costs one textbook DLOG bound plus the sum of the residuals' bounds.
Every ledger bound below is this step applied to a distribution-free `…_subset` inclusion:
the inclusions are what compose, and the probability bound is taken once, here. -/
theorem event_prob_le_of_subset {k maxActions : ℕ}
    (family : Family k maxActions) (B : VestaG)
    (E : Set family.GroupSample) (statistical : Fin k → Set family.GroupSample)
    (hE : E ⊆ family.combinedRelationEvent ∪ family.ledgerStatisticalEvent statistical)
    {dlBound : ENNReal} (epsilon : Fin k → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical slot)) ≤ epsilon slot) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure (family.scalarEvent B E) ≤
      (dlBound + 1 / Fintype.card Fp) + ∑ slot, epsilon slot := by
  refine le_trans (Model.toOuterMeasure_le_add₂ _
    (show family.scalarEvent B E ⊆ family.scalarEvent B family.combinedRelationEvent ∪
      family.scalarEvent B (family.ledgerStatisticalEvent statistical) from
      Set.preimage_union ▸ Set.preimage_mono hE)) ?_
  apply add_le_add
  · exact family.combinedRelationEvent_prob_le_of_textbookDL B hDL
  · unfold ledgerStatisticalEvent scalarEvent
    simp only [Set.preimage_iUnion]
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    rw [tsum_fintype]
    exact Finset.sum_le_sum fun slot _ => hstat slot

/-- **The ledger bound, with the discrete-log term taken once.** One textbook discrete-log
hypothesis on the combined finder covers every slot; only the slots' statistical bounds
are summed. -/
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
      (dlBound + 1 / Fintype.card Fp) + ∑ slot, epsilon slot :=
  family.event_prob_le_of_subset B _ statistical
    (family.ledgerFailureEvent_subset failure statistical hslot) epsilon hDL hstat

/-- `ledgerFailureEvent_prob_le` with one bound `epsilon` for every slot's residual, so
that the sum becomes `k * epsilon`. The number of slots `k` multiplies only the
statistical bound; neither `maxActions` nor `k` multiplies `dlBound`. -/
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

/-- The union over the emitted slots of the selected-count knowledge-failure events:
the selected proof is accepted and the selected knowledge extractor returns nothing. -/
def ledgerKnowledgeFailureEvent {k maxActions : ℕ} (family : Family k maxActions) :
    Set family.GroupSample :=
  family.ledgerFailureEvent fun slot =>
    (family.slotFamily slot).selectedKnowledgeFailureEvent

/-- The union over the emitted slots of the statistical residuals: the samples on which
the selected finder returns no relation and the selected run lands on one of the four
statistical surfaces. -/
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

/-- **Action knowledge soundness composed at the ledger reduction layer.** The caller
supplies one bound `epsilon` for each slot's statistical residual (the samples on which
the selected finder returns no relation and the selected run lands on a statistical
surface). The conclusion pays the discrete-log term once, for the combined finder, and
multiplies only `epsilon` by the number of emitted slots. -/
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
  simpa using family.event_prob_le_of_subset B _ _
    family.ledgerKnowledgeFailureEvent_subset (fun _ => epsilon) hDL hstat

/-- The extraction arm used by a ledger proof: Action knowledge failure or an
explicit ledger-bridge escape at one of the emitted slots. -/
def ledgerExtractionFailureEvent {k maxActions : ℕ} (family : Family k maxActions)
    (escape : Fin k → Set family.GroupSample) : Set family.GroupSample :=
  family.ledgerFailureEvent fun slot =>
    (family.slotFamily slot).selectedKnowledgeFailureEvent ∪ escape slot

/-- The statistical side of ledger extraction: for each emitted slot, the selected
count's statistical surfaces together with that slot's ledger-bridge escape event, whose
probability the caller bounds separately (`hescape`). -/
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

/-- **Ledger extraction failure, with the discrete-log term charged once.** The number
of emitted slots multiplies only the Action statistical surface bound and the
ledger-bridge escape bound; no term is multiplied by `maxActions`. -/
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
  have h := family.event_prob_le_of_subset B _ _
    (family.ledgerExtractionFailureEvent_subset escape)
    (fun _ => epsilonStat + epsilonEscape) hDL fun slot => by
      unfold scalarEvent
      rw [Set.preimage_union]
      exact le_trans (MeasureTheory.measure_union_le _ _)
        (add_le_add (hstat slot) (hescape slot))
  simpa [mul_add] using h

end Family
end Zcash.Security.Ledger.AdaptiveActionReduction
