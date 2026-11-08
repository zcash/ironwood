import Zcash.Common.RelationProbabilityCoins
import Zcash.Security.Ledger.Capstone
import Zcash.Snark.Soundness.Action.AdaptiveCountReduction

/-!
# Ledger composition for adaptive Action extraction

One online-AGM adversary emits the Action proofs of every chain position under one
random-oracle table and one query budget, and each position may choose its own Action
count after arbitrary oracle queries.

The module follows the recipe of the book's Security Models page ("How the layers
compose"). The computable reductions compose first: `combinedRelationFinder` returns
the first relation that any chain position's run exposes, so its event is the union of
the positions' relation events (`combinedRelationEvent_eq_iUnion`), and one
discrete-log hypothesis on that finder covers every position. The containments come
next (the `…_subset` lemmas): each position's failure is covered by its relation event
and its statistical residual, so the union of the failures is covered by the one
combined relation event and the union of the residuals; these hold for every sample.
Probability enters once, in `event_prob_le_of_subset`: `scalarEvent` lifts an event
from the group basis to the scalar sample, the lift is a preimage and so preserves
inclusions and unions, and the measure's monotonicity and subadditivity give the bound

`DLOG + 1 / |Fp| + (the sum over chain positions of that position's statistical bound)`.

Neither the number of chain positions nor `maxActions` multiplies the discrete-log
advantage; those cardinalities can enter only through the separately supplied
statistical bounds.
-/

namespace Zcash.Security.Ledger.AdaptiveActionReduction

open Classical
open Zcash.Common
open Zcash.Snark
open Zcash.Snark.Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

/-- Outputs for every chain position, with each position carrying its own adaptively
selected Action count. -/
abbrev Outputs (numChainPositions maxActions : ℕ)
    (components : Fin numChainPositions → (n : Fin maxActions) →
      ComputedAdaptiveActionStatementFSFamily (adaptiveActionCountParams n))
    (basis : AdaptiveActionCountBasis) :=
  (position : Fin numChainPositions) →
    AdaptiveActionCountOutput maxActions (components position) basis

/-- One stateful proof-emitting ledger adversary. Counts and chain positions share the
same oracle computation and the same global query budget `Q`. -/
structure Family (numChainPositions maxActions : ℕ) where
  components : Fin numChainPositions → (n : Fin maxActions) →
    ComputedAdaptiveActionStatementFSFamily (adaptiveActionCountParams n)
  adversary : (basis : AdaptiveActionCountBasis) →
    LabeledOracleComp (AdaptiveActionCountTranscript maxActions) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis)
      (Outputs numChainPositions maxActions components basis)
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace Family

abbrev Coins {numChainPositions maxActions : ℕ}
    (_family : Family numChainPositions maxActions) :=
  AdaptiveActionCountTranscript maxActions → Fp

/-- Project the shared ledger run to one chain position. This is a view of the same
program and table, not a separately sampled per-position oracle. -/
def positionFamily {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (position : Fin numChainPositions) :
    ComputedAdaptiveActionCountFSFamily maxActions where
  components := family.components position
  adversary := fun basis => (family.adversary basis).bind fun outputs =>
    .pure (outputs position)
  Q := family.Q
  queryBound := by
    intro basis
    rw [LabeledOracleComp.QueryBound, LabeledOracleComp.erase_bind]
    simpa only [Nat.add_zero] using
      OracleComp.queryBound_bind (family.queryBound basis)
        (fun outputs => OracleComp.QueryBound.pure (outputs position) 0)

/-- One relation finder covering every emitted chain position. -/
def combinedRelationFinder {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) :
    (basis : AdaptiveActionCountBasis) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
      (shape := AdaptiveActionStatementShape (actionProofParamsFor 1))
      (List.ofFn fun position => (family.positionFamily position).selectedRelationFinder basis O)

/-- If any chain position exposes a relation, the combined finder exposes one. -/
theorem combinedRelationFinder_isSome_of_position {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (position : Fin numChainPositions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (hposition : ((family.positionFamily position).selectedRelationFinder basis O).isSome) :
    (family.combinedRelationFinder basis O).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  intro hnone
  unfold combinedRelationFinder at hnone
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  have hpositionNone := hall
    ((family.positionFamily position).selectedRelationFinder basis O)
    (List.mem_ofFn.mpr ⟨position, rfl⟩)
  rw [hpositionNone] at hposition
  exact Bool.false_ne_true hposition

/-- The sample space before replacing the sampled scalar basis by group points. -/
abbrev ScalarSample {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) :=
  (ActionBasisIndex → Fp) × family.Coins

/-- The sample space seen by the algebraic relation finders. -/
abbrev GroupSample {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) :=
  AdaptiveActionCountBasis × family.Coins

/-- The lift of a group-basis event to the uniform scalar-basis experiment: a preimage,
so it preserves inclusions and unions. -/
def scalarEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG)
    (event : Set family.GroupSample) : Set family.ScalarSample :=
  (fun q => (scalarBasis B q.1, q.2)) ⁻¹' event

/-- The exact relation event of the one combined ledger finder. -/
def combinedRelationEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) : Set family.GroupSample :=
  {q | (family.combinedRelationFinder q.1 q.2).isSome}

/-- The combined finder's event is the union of the chain positions' relation events:
the finder takes the first relation that any position exposes, so it exposes one
exactly when some position does. -/
theorem combinedRelationEvent_eq_iUnion {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) :
    family.combinedRelationEvent =
      ⋃ position, {q : family.GroupSample |
        ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome} := by
  ext q
  simp only [combinedRelationEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hsome
    by_contra hnone
    rw [not_exists] at hnone
    have hall : ∀ r ∈ List.ofFn fun position =>
        (family.positionFamily position).selectedRelationFinder q.1 q.2, r = none := by
      intro r hr
      obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hr
      exact Option.not_isSome_iff_eq_none.mp (hnone position)
    have hcombined : family.combinedRelationFinder q.1 q.2 = none :=
      (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).2 hall
    rw [hcombined] at hsome
    exact Bool.false_ne_true hsome
  · rintro ⟨position, hposition⟩
    exact family.combinedRelationFinder_isSome_of_position position q.1 q.2 hposition

/-- A chain position's relation event is contained in the one combined relation event. -/
theorem positionRelationEvent_subset_combined {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (position : Fin numChainPositions) :
    {q : family.GroupSample |
      ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome} ⊆
        family.combinedRelationEvent := by
  rw [family.combinedRelationEvent_eq_iUnion]
  exact Set.subset_iUnion (fun position => {q : family.GroupSample |
    ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome}) position

/-- Under the uniform scalar sample, the probability of the combined ledger relation
event is at most the textbook discrete-log bound on the combined finder plus `1 / |Fp|`,
with no factor for the number of chain positions. -/
theorem combinedRelationEvent_prob_le_of_textbookDL {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG) {dlBound : ENNReal}
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

/-- Union of the extraction failures among the actually emitted chain positions. -/
def ledgerFailureEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (failure : Fin numChainPositions → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ position, failure position

/-- Union of the emitted chain positions' statistical residuals. -/
def ledgerStatisticalEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (statistical : Fin numChainPositions → Set family.GroupSample) : Set family.GroupSample :=
  ⋃ position, statistical position

/-- A set inclusion, holding for every sample without reference to a distribution: if
each emitted chain position's failure event is covered by that position's relation
event together with its statistical residual, then the union of the positions'
failures is covered by the single combined relation event together with the union of
the residuals. -/
theorem ledgerFailureEvent_subset {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (failure statistical : Fin numChainPositions → Set family.GroupSample)
    (hposition : ∀ position, failure position ⊆
      {q | ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical position) :
    family.ledgerFailureEvent failure ⊆
      family.combinedRelationEvent ∪ family.ledgerStatisticalEvent statistical := by
  intro q hq
  obtain ⟨position, hfailure⟩ := Set.mem_iUnion.mp hq
  rcases hposition position hfailure with hrelation | hstatistical
  · exact Or.inl (family.positionRelationEvent_subset_combined position hrelation)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨position, hstatistical⟩)

/-- **The one pricing step.** Any event covered by the combined relation event and a
union of residuals, one per chain position, costs one textbook DLOG bound plus the sum
of the residuals' bounds. Every ledger bound below is this step applied to a
distribution-free `…_subset` inclusion: the inclusions are what compose, and the
probability bound is taken once, here. -/
theorem event_prob_le_of_subset {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG)
    (E : Set family.GroupSample) (statistical : Fin numChainPositions → Set family.GroupSample)
    (hE : E ⊆ family.combinedRelationEvent ∪ family.ledgerStatisticalEvent statistical)
    {dlBound : ENNReal} (epsilon : Fin numChainPositions → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical position)) ≤ epsilon position) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure (family.scalarEvent B E) ≤
      (dlBound + 1 / Fintype.card Fp) + ∑ position, epsilon position := by
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
    exact Finset.sum_le_sum fun position _ => hstat position

/-- **The ledger bound, with the discrete-log term taken once.** One textbook
discrete-log hypothesis on the combined finder covers every chain position; only the
positions' statistical bounds are summed. -/
theorem ledgerFailureEvent_prob_le {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG)
    (failure statistical : Fin numChainPositions → Set family.GroupSample)
    (hposition : ∀ position, failure position ⊆
      {q | ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical position)
    {dlBound : ENNReal} (epsilon : Fin numChainPositions → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical position)) ≤ epsilon position) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerFailureEvent failure)) ≤
      (dlBound + 1 / Fintype.card Fp) + ∑ position, epsilon position :=
  family.event_prob_le_of_subset B _ statistical
    (family.ledgerFailureEvent_subset failure statistical hposition) epsilon hDL hstat

/-- `ledgerFailureEvent_prob_le` with one bound `epsilon` for every chain position's
residual, so that the sum becomes `numChainPositions * epsilon`. The number of chain
positions multiplies only the statistical bound; neither `maxActions` nor
`numChainPositions` multiplies `dlBound`. -/
theorem ledgerFailureEvent_prob_le_uniform {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG)
    (failure statistical : Fin numChainPositions → Set family.GroupSample)
    (hposition : ∀ position, failure position ⊆
      {q | ((family.positionFamily position).selectedRelationFinder q.1 q.2).isSome} ∪
        statistical position)
    {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (statistical position)) ≤ epsilon) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerFailureEvent failure)) ≤
      (dlBound + 1 / Fintype.card Fp) + (numChainPositions : ENNReal) * epsilon := by
  simpa using family.ledgerFailureEvent_prob_le B failure statistical hposition
    (fun _ => epsilon) hDL hstat

/-- The union over the emitted chain positions of the selected-count knowledge-failure
events: the selected proof is accepted and the selected knowledge extractor returns
nothing. -/
def ledgerKnowledgeFailureEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) : Set family.GroupSample :=
  family.ledgerFailureEvent fun position =>
    (family.positionFamily position).selectedKnowledgeFailureEvent

/-- The union over the emitted chain positions of the statistical residuals: the
samples on which the selected finder returns no relation and the selected run lands on
one of the four statistical surfaces. -/
def ledgerActionStatisticalFailureEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) : Set family.GroupSample :=
  family.ledgerStatisticalEvent fun position =>
    (family.positionFamily position).selectedStatisticalFailureEvent

/-- The Action-specific distribution-free split used by the ledger endpoint. -/
theorem ledgerKnowledgeFailureEvent_subset {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) :
    family.ledgerKnowledgeFailureEvent ⊆
      family.combinedRelationEvent ∪ family.ledgerActionStatisticalFailureEvent := by
  exact family.ledgerFailureEvent_subset
    (fun position => (family.positionFamily position).selectedKnowledgeFailureEvent)
    (fun position => (family.positionFamily position).selectedStatisticalFailureEvent)
    (fun position => (family.positionFamily position).selectedKnowledgeFailureEvent_subset)

/-- **Action knowledge soundness composed at the ledger reduction layer.** The caller
supplies one bound `epsilon` for each chain position's statistical residual (the
samples on which the selected finder returns no relation and the selected run lands on
a statistical surface). The conclusion pays the discrete-log term once, for the
combined finder, and multiplies only `epsilon` by the number of emitted positions. -/
theorem ledgerKnowledgeFailureEvent_prob_le {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG) {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.positionFamily position).selectedStatisticalFailureEvent) ≤ epsilon) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B family.ledgerKnowledgeFailureEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + (numChainPositions : ENNReal) * epsilon := by
  simpa using family.event_prob_le_of_subset B _ _
    family.ledgerKnowledgeFailureEvent_subset (fun _ => epsilon) hDL hstat

/-- The extraction arm used by a ledger proof: Action knowledge failure or an
explicit ledger-bridge escape at one of the emitted chain positions. -/
def ledgerExtractionFailureEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (escape : Fin numChainPositions → Set family.GroupSample) : Set family.GroupSample :=
  family.ledgerFailureEvent fun position =>
    (family.positionFamily position).selectedKnowledgeFailureEvent ∪ escape position

/-- The statistical side of ledger extraction: for each emitted chain position, the
selected count's statistical surfaces together with that position's ledger-bridge
escape event, whose probability the caller bounds separately (`hescape`). -/
def ledgerExtractionStatisticalEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (escape : Fin numChainPositions → Set family.GroupSample) : Set family.GroupSample :=
  family.ledgerStatisticalEvent fun position =>
    (family.positionFamily position).selectedStatisticalFailureEvent ∪ escape position

/-- Concrete extraction failures are covered by one combined relation event together
with each chain position's statistical and bridge events. -/
theorem ledgerExtractionFailureEvent_subset {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    (escape : Fin numChainPositions → Set family.GroupSample) :
    family.ledgerExtractionFailureEvent escape ⊆
      family.combinedRelationEvent ∪ family.ledgerExtractionStatisticalEvent escape := by
  apply family.ledgerFailureEvent_subset
  intro position q hq
  rcases hq with hknowledge | hescape
  · rcases (family.positionFamily position).selectedKnowledgeFailureEvent_subset hknowledge with
      hrelation | hstatistical
    · exact Or.inl hrelation
    · exact Or.inr (Or.inl hstatistical)
  · exact Or.inr (Or.inr hescape)

/-- **Ledger extraction failure, with the discrete-log term charged once.** The number
of emitted chain positions multiplies only the Action statistical surface bound and the
ledger-bridge escape bound; no term is multiplied by `maxActions`. -/
theorem ledgerExtractionFailureEvent_prob_le {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) (B : VestaG)
    (escape : Fin numChainPositions → Set family.GroupSample)
    {dlBound epsilonStat epsilonEscape : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.positionFamily position).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (escape position)) ≤ epsilonEscape) :
    (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (family.ledgerExtractionFailureEvent escape)) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (numChainPositions : ENNReal) * (epsilonStat + epsilonEscape) := by
  have h := family.event_prob_le_of_subset B _ _
    (family.ledgerExtractionFailureEvent_subset escape)
    (fun _ => epsilonStat + epsilonEscape) hDL fun position => by
      unfold scalarEvent
      rw [Set.preimage_union]
      exact le_trans (MeasureTheory.measure_union_le _ _)
        (add_le_add (hstat position) (hescape position))
  simpa [mul_add] using h

end Family
end Zcash.Security.Ledger.AdaptiveActionReduction
