import Zcash.Snark.Soundness.Action.AdaptiveCountModel
import Zcash.Snark.Soundness.Action.AdaptiveStatementCached

/-!
# Reduction layer for adaptively selected Action counts

This module consumes one shared execution of
`ComputedAdaptiveActionCountFSFamily`, narrows its annotation log only after the
output count is known, and runs the existing fixed-count reduction stages over
that selected output.  The resulting relation finder is a single function of
the shared basis and oracle table.  A DLOG assumption therefore applies to this
finder once; no union over unused Action counts is involved.
-/

namespace Zcash.Snark

open Classical Halo2 CompPoly.CPolynomial
open Zcash.Common
open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ComputedAdaptiveActionCountFSFamily

/-- Retained annotations from the one shared adaptive-count execution. -/
abbrev AnnotationLog {maxActions : ℕ} (basis : AdaptiveActionCountBasis) :=
  List (LabeledOracleComp.QueryAnnotation (AdaptiveActionCountTranscript maxActions)
    (AlgebraicTranscriptQuery (F := Fp) basis))

/-- A shared-domain transcript fits the selected count's original bounded
domain exactly when its raw transcript meets that smaller length bound. -/
def narrowAdaptiveActionCountTranscript? {maxActions : ℕ} (n : Fin maxActions)
    (t : AdaptiveActionCountTranscript maxActions) :
    Option (AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) :=
  if h : t.val.length ≤ adaptiveActionCountTranscriptLimit (n + 1) then
    some ⟨t.val, by
      rw [adaptiveActionStatementTranscriptLimit_eq]
      exact h⟩
  else none

@[simp] theorem narrowAdaptiveActionCountTranscript?_widen {maxActions : ℕ}
    (n : Fin maxActions)
    (t : AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) :
    narrowAdaptiveActionCountTranscript? n (widenAdaptiveActionCountTranscript n t) = some t := by
  have h : t.val.length ≤ adaptiveActionCountTranscriptLimit (n + 1) := by
    rw [← adaptiveActionStatementTranscriptLimit_eq]
    exact t.prop
  simp only [narrowAdaptiveActionCountTranscript?, widenAdaptiveActionCountTranscript_val, h,
    dite_true]
  congr

/-- Restrict one shared-domain AGM annotation to a selected fixed-count domain.
The restriction changes only the transcript subtype; its represented points and
coefficients remain literal data. -/
def narrowAdaptiveActionCountAnnotation? {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis}
    (entry : LabeledOracleComp.QueryAnnotation (AdaptiveActionCountTranscript maxActions)
      (AlgebraicTranscriptQuery (F := Fp) basis)) :
    Option (LabeledOracleComp.QueryAnnotation
      (AdaptiveActionStatementTranscript (adaptiveActionCountParams n))
      (AlgebraicTranscriptQuery (F := Fp) basis)) :=
  match h : narrowAdaptiveActionCountTranscript? n entry.point with
  | none => none
  | some t => some
      { point := t
        label :=
          { representedPoints := entry.label.representedPoints
            points_eq := by
              have ht : t.val = entry.point.val := by
                unfold narrowAdaptiveActionCountTranscript? at h
                split at h
                · simp only [Option.some.injEq] at h
                  exact (congrArg Subtype.val h).symm
                · contradiction
              simpa only [ht] using entry.label.points_eq } }

/-- Keep precisely the annotations that fit the count selected at the end of the
shared run. -/
def narrowAdaptiveActionCountAnnotations {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis}
    (annotations : AnnotationLog (maxActions := maxActions) basis) :
    ComputedAdaptiveActionStatementFSFamily.AnnotationLog
      (pp := adaptiveActionCountParams n) basis :=
  annotations.filterMap (narrowAdaptiveActionCountAnnotation? n)

/-- Run once and retain the adaptive output together with the exact shared AGM
annotation log. -/
def cachedExecution {maxActions : ℕ} (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    AdaptiveActionCountOutput maxActions family.components basis ×
      AnnotationLog (maxActions := maxActions) basis :=
  (family.adversary basis).runWithAnnotations O

@[simp] theorem cachedExecution_output_eq {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    (family.cachedExecution basis O).1 = family.runOutput basis O := by
  simp [cachedExecution, runOutput]

@[simp] theorem cachedExecution_annotations_eq {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    (family.cachedExecution basis O).2 = (family.adversary basis).annotations O := by
  simp [cachedExecution]

/-- Feed the selected output, the selected portion of the shared annotation log,
and the selected canonical challenge reads into the existing fixed-count cached
reduction. -/
def selectedCachedRun {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    let selected := (family.cachedExecution basis O).1
    ComputedAdaptiveActionStatementFSFamily.CachedRun
      (adaptiveActionCountParams selected.count)
      (family.components selected.count) basis := by
  let execution := family.cachedExecution basis O
  let selected := execution.1
  let component := family.components selected.count
  exact
    { output := selected.output
      annotations := narrowAdaptiveActionCountAnnotations selected.count execution.2
      pre := fun i => O (widenAdaptiveActionCountTranscript selected.count
        (selected.output.prefixesPre (component.vkTranscriptRepr basis) i))
      rounds := fun j => O (widenAdaptiveActionCountTranscript selected.count
        (selected.output.prefixes (component.vkTranscriptRepr basis) j)) }

/-- The selected Action shape has the same constant pair-count bound used by all
fixed-count Action capstones. -/
theorem selectedCachedRun_pairCount_lt {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    let selected := (family.cachedExecution basis O).1
    let cache := family.selectedCachedRun basis O
    deployedX4PairCount
        (adaptiveActionStatementVk (adaptiveActionCountParams selected.count) basis)
        (adaptiveActionStatementInstanceCommitment
          (adaptiveActionCountParams selected.count) basis cache.output.inputs)
        cache.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape
          (adaptiveActionCountParams selected.count)).k) cache.pre cache.rounds) <
      Zcash.Arithmetic.scalarFieldOrder := by
  dsimp only
  refine lt_of_le_of_lt (deployedX4PairCount_le_numPointSets _ _ _ _) ?_
  rw [CircuitShape.withProofParams_numPointSets]
  norm_num [adaptiveActionCountParams, actionProofParamsFor,
    Zcash.Arithmetic.scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- Compare a selected fixed-count query against the first annotation at the
same literal transcript in the shared-domain execution.  Widening changes only
the transcript subtype, so the represented point list is unchanged. -/
def selectedQueryRepresentationRelationFromSharedAnnotations?
    {maxActions : ℕ} (_family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis)
    (annotations : AnnotationLog (maxActions := maxActions) basis)
    (n : Fin maxActions)
    (t : AdaptiveActionStatementTranscript (adaptiveActionCountParams n))
    (final : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  selectedQueryRepresentationRelationFromAnnotations?
    (widenAdaptiveActionCountTranscript n t) annotations final (by
      intro ap hap
      simpa only [widenAdaptiveActionCountTranscript_val] using hcovered ap hap)

/-- Canonical-coordinate and first-query checks for the selected instance
commitments, evaluated directly against the shared annotation log. -/
def selectedInstanceRepresentationRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) := by
  let execution := family.cachedExecution basis O
  let selected := execution.1
  let component := family.components selected.count
  exact match component.canonicalInstanceRepresentationRelationFinderOfOutput
      basis selected.output with
    | some relation => some relation
    | none => family.selectedQueryRepresentationRelationFromSharedAnnotations?
        basis execution.2 selected.count
        (component.thetaPoint basis selected.output)
        (adaptiveStatementInstanceRepresentationList
          selected.output.instanceRepresentations)
        (selected.output.instanceRepresentations_coveredAtTheta
          (component.vkTranscriptRepr basis))

/-- One selected pre-IPA coordinate comparison over the shared annotation log. -/
def selectedPreIpaRepresentationRelationAt? {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (i : Fin 11) (h5i : 5 ≤ (i : ℕ)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) := by
  let execution := family.cachedExecution basis O
  let selected := execution.1
  let component := family.components selected.count
  exact family.selectedQueryRepresentationRelationFromSharedAnnotations?
    basis execution.2 selected.count (component.preIpaPoint basis i selected.output)
    (ComputedAdaptiveActionStatementFSFamily.preIpaRepresentationTarget
      selected.output i) (by
      intro ap hap
      have hap' := List.mem_append.mp hap
      rcases hap' with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (preIpaSqueezePoints
            (selected.output.init (component.vkTranscriptRepr basis))
            selected.output.proofData.algebraicProof.erase i)
        exact selected.output.proofData.algebraicProof.representationsBefore_covered
          (selected.output.init (component.vkTranscriptRepr basis))
          selected.output.proofData.wellFormed i h5i ap hproof
      · exact selected.output.instanceRepresentations_coveredPre
          (component.vkTranscriptRepr basis) i ap hinstance)

/-- All six selected pre-IPA provenance comparisons. -/
def selectedPreIpaRepresentationRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (shape := AdaptiveActionStatementShape (actionProofParamsFor 1))
    [family.selectedPreIpaRepresentationRelationAt? basis O 5 (by omega),
     family.selectedPreIpaRepresentationRelationAt? basis O 6 (by omega),
     family.selectedPreIpaRepresentationRelationAt? basis O 7 (by omega),
     family.selectedPreIpaRepresentationRelationAt? basis O 8 (by omega),
     family.selectedPreIpaRepresentationRelationAt? basis O 9 (by omega),
     family.selectedPreIpaRepresentationRelationAt? basis O 10 (by omega)]

/-- One selected IPA-round coordinate comparison over the shared annotation log. -/
def selectedIpaRepresentationRelationAt? {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (j : Fin actionCircuit.shape.k) :
    Option (AlgebraicRelationWitness (F := Fp) basis) := by
  let execution := family.cachedExecution basis O
  let selected := execution.1
  let component := family.components selected.count
  exact family.selectedQueryRepresentationRelationFromSharedAnnotations?
    basis execution.2 selected.count (component.ipaPoint basis j selected.output)
    (ComputedAdaptiveActionStatementFSFamily.ipaRepresentationTarget
      selected.output j) (by
      intro ap hap
      have hap' := List.mem_append.mp hap
      rcases hap' with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (roundTranscriptFin
            (preIpaTranscript
              (selected.output.init (component.vkTranscriptRepr basis))
              selected.output.proofData.algebraicProof.erase)
            selected.output.proofData.algebraicProof.erase.ipaRounds j)
        exact selected.output.proofData.algebraicProof.representationsBeforeRound_covered
          (selected.output.init (component.vkTranscriptRepr basis))
          selected.output.proofData.wellFormed j ap hproof
      · exact selected.output.instanceRepresentations_coveredRound
          (component.vkTranscriptRepr basis) j ap hinstance)

/-- Every selected IPA-round provenance comparison. -/
def selectedIpaRepresentationRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (shape := AdaptiveActionStatementShape (actionProofParamsFor 1))
    (List.ofFn fun j => family.selectedIpaRepresentationRelationAt? basis O j)

/-- One selected Action semantic coordinate comparison over the shared log. -/
def selectedSemanticRepresentationRelationAt? {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) (n : Fin 5) :
    Option (AlgebraicRelationWitness (F := Fp) basis) := by
  let execution := family.cachedExecution basis O
  let selected := execution.1
  let component := family.components selected.count
  let n11 : Fin 11 := Fin.castLE (by omega) n
  exact family.selectedQueryRepresentationRelationFromSharedAnnotations?
    basis execution.2 selected.count (component.preIpaPoint basis n11 selected.output)
    (ComputedAdaptiveActionStatementFSFamily.semanticRepresentationTarget
      selected.output n) (by
      intro ap hap
      have hap' := List.mem_append.mp hap
      rcases hap' with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (preIpaSqueezePoints
            (selected.output.init (component.vkTranscriptRepr basis))
            selected.output.proofData.algebraicProof.erase n11)
        exact selected.output.proofData.algebraicProof.actionRepresentationsBefore_covered
          (selected.output.init (component.vkTranscriptRepr basis))
          selected.output.proofData.wellFormed n ap hproof
      · exact selected.output.instanceRepresentations_coveredPre
          (component.vkTranscriptRepr basis) n11 ap hinstance)

/-- All five selected semantic-squeeze provenance comparisons. -/
def selectedSemanticRepresentationRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (shape := AdaptiveActionStatementShape (actionProofParamsFor 1))
    (List.ofFn fun n => family.selectedSemanticRepresentationRelationAt? basis O n)

/-- One provenance pass over the shared execution.  In particular, none of
the query-coordinate checks is reconstructed from a separately sampled
fixed-count adversary. -/
def selectedProvenanceRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  exact ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (shape := AdaptiveActionStatementShape (adaptiveActionCountParams selected.count))
    [family.selectedInstanceRepresentationRelationFinder basis O,
     family.selectedPreIpaRepresentationRelationFinder basis O,
     family.selectedIpaRepresentationRelationFinder basis O,
     family.selectedSemanticRepresentationRelationFinder basis O,
     component.semanticSourceMismatchRelationFinderOfOutput basis selected.output]

/-- Empty shared provenance exposes the component-wise empty results used by
the cached terminal and by the statistical surface split. -/
theorem selectedProvenanceRelationFinder_eq_none_iff {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    family.selectedProvenanceRelationFinder basis O = none ↔
      family.selectedInstanceRepresentationRelationFinder basis O = none ∧
      family.selectedPreIpaRepresentationRelationFinder basis O = none ∧
      family.selectedIpaRepresentationRelationFinder basis O = none ∧
      family.selectedSemanticRepresentationRelationFinder basis O = none ∧
      let selected := (family.cachedExecution basis O).1
      let component := family.components selected.count
      component.semanticSourceMismatchRelationFinderOfOutput basis selected.output = none := by
  unfold selectedProvenanceRelationFinder
  dsimp only
  let checks :=
    [family.selectedInstanceRepresentationRelationFinder basis O,
     family.selectedPreIpaRepresentationRelationFinder basis O,
     family.selectedIpaRepresentationRelationFinder basis O,
     family.selectedSemanticRepresentationRelationFinder basis O,
     (family.components (family.cachedExecution basis O).1.count)
      |>.semanticSourceMismatchRelationFinderOfOutput basis
        (family.cachedExecution basis O).1.output]
  have hiff := ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff
    (shape := AdaptiveActionStatementShape
      (adaptiveActionCountParams (family.cachedExecution basis O).1.count)) checks
  constructor
  · intro hnone
    have hall := hiff.mp hnone
    exact ⟨hall _ List.mem_cons_self,
      hall _ (List.mem_cons_of_mem _ List.mem_cons_self),
      hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))),
      hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))⟩
  · rintro ⟨hinstance, hpre, hipa, hsemantic, hsource⟩
    apply hiff.mpr
    intro check hcheck
    rcases List.mem_cons.mp hcheck with rfl | hcheck
    · exact hinstance
    rcases List.mem_cons.mp hcheck with rfl | hcheck
    · exact hpre
    rcases List.mem_cons.mp hcheck with rfl | hcheck
    · exact hipa
    rcases List.mem_cons.mp hcheck with rfl | hcheck
    · exact hsemantic
    rcases List.mem_cons.mp hcheck with rfl | hcheck
    · exact hsource
    · cases hcheck

/-- The semantic facts certified by the selected shared run's provenance pass. -/
theorem selectedCachedRun_semanticStageFacts {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (hnone : family.selectedProvenanceRelationFinder basis O = none) :
    let selected := (family.cachedExecution basis O).1
    let component := family.components selected.count
    component.SemanticStageFacts basis (family.selectedCachedRun basis O).toRunView := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let cache := family.selectedCachedRun basis O
  apply component.semanticStageFacts_of_sourceFinderV_none basis cache.toRunView
  exact (family.selectedProvenanceRelationFinder_eq_none_iff basis O).1 hnone |>.2.2.2.2

/-- The complete fixed-count reduction, selected only after the shared adaptive
execution finishes. -/
def selectedRelationFinderWithCalls {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    Option (AlgebraicRelationWitness (F := Fp) basis) × Nat := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let cache := family.selectedCachedRun basis O
  exact match hprovenance : family.selectedProvenanceRelationFinder basis O with
    | some relation => (some relation, 1)
    | none => component.relationFinderAfterCachedProvenance basis cache
        (family.selectedCachedRun_pairCount_lt basis O)
        (family.selectedCachedRun_semanticStageFacts basis O hprovenance)

/-- No result from the selected reduction implies that every shared provenance
comparison was empty. -/
theorem selectedRelationFinderWithCalls_none_provenance {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (hnone : (family.selectedRelationFinderWithCalls basis O).1 = none) :
    family.selectedProvenanceRelationFinder basis O = none := by
  unfold selectedRelationFinderWithCalls at hnone
  split at hnone
  · simp_all
  · assumption

/-- Once shared provenance is empty, an empty selected finder means that all
three remaining fixed-count stages were empty on the very same run view. -/
theorem selectedRelationFinderWithCalls_none_later {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (hnone : (family.selectedRelationFinderWithCalls basis O).1 = none) :
    let selected := (family.cachedExecution basis O).1
    let component := family.components selected.count
    let cache := family.selectedCachedRun basis O
    let hchar := family.selectedCachedRun_pairCount_lt basis O
    let hprovenance := family.selectedRelationFinderWithCalls_none_provenance basis O hnone
    let facts := family.selectedCachedRun_semanticStageFacts basis O hprovenance
    component.statementQuotientRelationFinderV basis cache.toRunView = none ∧
      component.identityRelationFinderV basis cache.toRunView hchar none
          (fun _ => facts) = none ∧
        component.terminalRelationFinderV basis cache.toRunView hchar = none := by
  dsimp only
  have hprovenance :=
    family.selectedRelationFinderWithCalls_none_provenance basis O hnone
  have hafter :
      (ComputedAdaptiveActionStatementFSFamily.relationFinderAfterCachedProvenance
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O)
          (family.selectedCachedRun_pairCount_lt basis O)
          (family.selectedCachedRun_semanticStageFacts basis O hprovenance)).1 = none := by
    unfold selectedRelationFinderWithCalls at hnone
    split at hnone <;> rename_i hprovenanceCase
    · simp_all
    · simpa only using hnone
  have hquotient :
      (ComputedAdaptiveActionStatementFSFamily.statementQuotientRelationFinderV
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O).toRunView) = none := by
    cases heq : (ComputedAdaptiveActionStatementFSFamily.statementQuotientRelationFinderV
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O).toRunView) with
    | none => rfl
    | some relation =>
        unfold ComputedAdaptiveActionStatementFSFamily.relationFinderAfterCachedProvenance at hafter
        rw [heq] at hafter
        simp at hafter
  have hidentity :
      (ComputedAdaptiveActionStatementFSFamily.identityRelationFinderV
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O).toRunView
          (family.selectedCachedRun_pairCount_lt basis O) none
          (fun _ => family.selectedCachedRun_semanticStageFacts basis O hprovenance)) = none := by
    cases heq : (ComputedAdaptiveActionStatementFSFamily.identityRelationFinderV
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O).toRunView
          (family.selectedCachedRun_pairCount_lt basis O) none
          (fun _ => family.selectedCachedRun_semanticStageFacts basis O hprovenance)) with
    | none => rfl
    | some relation =>
        unfold ComputedAdaptiveActionStatementFSFamily.relationFinderAfterCachedProvenance at hafter
        rw [hquotient, heq] at hafter
        simp at hafter
  have hterminal :
      (ComputedAdaptiveActionStatementFSFamily.terminalRelationFinderV
          (family.components (family.cachedExecution basis O).1.count) basis
          (family.selectedCachedRun basis O).toRunView
          (family.selectedCachedRun_pairCount_lt basis O)) = none := by
    unfold ComputedAdaptiveActionStatementFSFamily.relationFinderAfterCachedProvenance at hafter
    rw [hquotient, hidentity] at hafter
    exact hafter
  exact ⟨hquotient, hidentity, hterminal⟩

/-- A relation returned by the zero-difference semantic branch is visible to the
view-level identity finder used by the shared-count reduction. -/
theorem identityRelationFinderV_isSome_of
    {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : ComputedAdaptiveActionStatementFSFamily.RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.SemanticStageFacts basis view)
    (witness : family.BatchWitnessV basis view)
    (hout : family.batchOutcomeV basis view = PSum.inl witness)
    (hroots : family.BatchGoodRootsV basis view witness)
    (haccepts : family.acceptsV basis view)
    (hz : view.pre 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds)
    (hidentity :
      let hshifted := family.shiftedValueV_of_accept_not_attack
        basis view haccepts hz hattack
      let rawDecode := family.rawDecodeOfBatchGoodRootsV basis view witness hroots hshifted
      (family.preXIdentityRelation?V basis view facts witness rawDecode rfl
        haccepts hcharV).isSome) :
    (family.identityRelationFinderV basis view hcharV none (fun _ => facts)).isSome := by
  let hshifted := family.shiftedValueV_of_accept_not_attack
    basis view haccepts hz hattack
  let rawDecode := family.rawDecodeOfBatchGoodRootsV basis view witness hroots hshifted
  have hacceptsSome := family.accepts?V_isSome_of basis view haccepts
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.batchGoodRoots?V_isSome_of basis view witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  obtain ⟨relation, hrelationEq⟩ := Option.isSome_iff_exists.mp hidentity
  unfold ComputedAdaptiveActionStatementFSFamily.identityRelationFinderV
    ComputedAdaptiveActionStatementFSFamily.identityRelationFinderWithAcceptanceV
  rw [hacceptsEq]
  dsimp only
  rw [dif_pos hz, dif_neg hattack, hout]
  dsimp only
  rw [hrootsEq]
  dsimp only
  rw [hrelationEq]
  rfl

set_option maxRecDepth 10000 in
/-- If every concrete statistical surface is avoided and each relation stage is
empty, the view-level Action extractor returns a witness. -/
theorem ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeExtractorV_isSome_of_good
    {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : ComputedAdaptiveActionStatementFSFamily.RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (finderResult : Option (AlgebraicRelationWitness (F := Fp) basis))
    (hfacts : finderResult = none → family.SemanticStageFacts basis view)
    (hfinderNone : finderResult = none)
    (hquotientNone : family.statementQuotientRelationFinderV basis view = none)
    (hidentityNone : family.identityRelationFinderV basis view hcharV none
      (fun _ => hfacts hfinderNone) = none)
    (hterminalNone : family.terminalRelationFinderV basis view hcharV = none)
    (haccepts : family.acceptsV basis view)
    (hz : view.pre 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds)
    (hgoodRoots : ∀ witness,
      family.batchOutcomeV basis view = PSum.inl witness →
        family.BatchGoodRootsV basis view witness)
    (hsurface : ∀ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      view.pre n11 ∉ adaptiveActionSurfaceAt pp basis view.output.inputs n
        view.output.toAlgebraicWfProof.proof.1
        (ComputedAdaptiveActionStatementFSFamily.semanticRepresentationTarget
          view.output n ++ family.fixedRepresentations basis)
        (fun i => view.pre (i.castLE (le_of_lt n11.isLt)))) :
    (family.adaptiveStatementKnowledgeExtractorV basis view hcharV finderResult hfacts).isSome := by
  let facts := hfacts hfinderNone
  cases hout : family.batchOutcomeV basis view with
  | inr relation =>
      have hacceptsSome := family.accepts?V_isSome_of basis view haccepts
      obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
      unfold ComputedAdaptiveActionStatementFSFamily.terminalRelationFinderV
        ComputedAdaptiveActionStatementFSFamily.terminalRelationFinderWithAcceptanceV at hterminalNone
      rw [hacceptsEq] at hterminalNone
      dsimp only at hterminalNone
      rw [dif_pos hz, dif_neg hattack, hout] at hterminalNone
      simp at hterminalNone
  | inl witness =>
      have hroots := hgoodRoots witness hout
      let hshifted := family.shiftedValueV_of_accept_not_attack basis view haccepts hz hattack
      let rawDecode := family.rawDecodeOfBatchGoodRootsV basis view witness hroots hshifted
      have hbatches : rawDecode.batches = witness.batches := by rfl
      have hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := haccepts
      have hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
            Zcash.Arithmetic.scalarFieldOrder := hcharV
      have hexclusions := family.statementExclusionsV_of_no_surface basis view facts
        witness rawDecode hbatches hacceptsFull hcharFull hsurface
      have hacceptsSome := family.accepts?V_isSome_of basis view haccepts
      obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
      have hrootsSome := family.batchGoodRoots?V_isSome_of basis view witness hroots
      obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
      let output := view.output
      let data := output.proofData
      let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis
      let source := data.algebraicProof.preX1AssemblySource fixed
      let difference := adaptiveActionPreXDifference pp basis output.inputs
        data.algebraicProof.erase source
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
      by_cases hsupport : difference = 0
      · have houtcomeSome := family.preXIdentityOutcomeV_isSome_of basis view facts
          witness rawDecode hbatches hacceptsFull hcharFull
          (by simpa only [difference, source, fixed, data, output] using hsupport)
          hexclusions.2.1 hexclusions.2.2.1 hexclusions.2.2.2
        obtain ⟨outcome, houtcomeEq⟩ := Option.isSome_iff_exists.mp houtcomeSome
        cases outcome with
        | inr relation =>
            have hrelationSome : (family.preXIdentityRelation?V basis view facts witness
                rawDecode hbatches hacceptsFull hcharFull).isSome := by
              unfold ComputedAdaptiveActionStatementFSFamily.preXIdentityRelation?V
              rw [houtcomeEq]
              rfl
            have hfinderSome := identityRelationFinderV_isSome_of family basis view hcharV
              facts witness hout hroots haccepts hz hattack hrelationSome
            rw [hidentityNone] at hfinderSome
            simp at hfinderSome
        | inl extracted =>
            unfold ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeExtractorV
            rw [family.adaptiveStatementKnowledgeOutcomeV_eq_core_of_none
              basis view hcharV hfacts hfinderNone]
            unfold ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeOutcomeCoreV
              ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeOutcomeCoreWithAcceptanceV
            rw [hacceptsEq]
            dsimp only
            rw [dif_pos hz, dif_neg hattack, hout]
            dsimp only
            rw [hrootsEq]
            dsimp only
            rw [dif_pos (by simpa only [difference, source, fixed, data, output]
              using hsupport)]
            rw [houtcomeEq]
            rfl
      · have heval := family.statementAcceptedDifferenceV_eval_eq_preX basis view facts
          hquotientNone witness rawDecode hbatches hacceptsFull hcharFull
        dsimp only at heval
        have hpreEval : difference.eval
            (chRecord (k := (AdaptiveActionStatementShape pp).k)
              view.pre view.rounds).x ≠ 0 :=
          (not_mem_szBadSet.mp (by
            simpa only [difference, source, fixed, data, output] using hexclusions.1)) hsupport
        let chV := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
        let decode := rawDecode.reRound view.rounds
        let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hcharFull i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) hacceptsFull
        let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hcharFull i hi) hacceptsFull
        have hactionGood : chV.x ∉ szBadSet
            (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
              model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
              chV.y model.chunkLen model.l0 model.lLast model.lBlind -
                polynomial .vanishingH * (X ^ actionCircuit.n - 1)) := by
          apply not_mem_szBadSet.mpr
          intro _
          rw [heval]
          simpa only [difference, source, fixed, data, output, chV] using hpreEval
        let run : family.DecodedRunV basis view :=
          { hchar := hcharV
            decode := family.decodeOfBatchGoodRootsV basis view witness hroots hshifted
            accepts := haccepts }
        have hdecode : run.decode = decode := by rfl
        let good : family.SemanticExclusionsV basis view run :=
          { xGood := by simpa only [run, hdecode, model, polynomial, chV] using hactionGood
            yGood := by simpa only [run, hdecode, model, polynomial] using hexclusions.2.1
            permutation := by
              simpa only [run, hdecode, model, polynomial] using hexclusions.2.2.1
            lookup := by
              simpa only [run, hdecode, model, polynomial] using hexclusions.2.2.2 }
        have houtcomeSome := family.semanticOutcome?V_isSome_of basis view run good
        obtain ⟨outcome, houtcomeEq⟩ := Option.isSome_iff_exists.mp houtcomeSome
        cases outcome with
        | inr relation =>
            have hsemanticSome : (family.semanticRelation?V basis view run).isSome := by
              unfold ComputedAdaptiveActionStatementFSFamily.semanticRelation?V
              rw [houtcomeEq]
              rfl
            have hterminalSome := family.terminalRelationFinderV_isSome_of basis view hcharV
              witness hout hroots haccepts hz hattack
              (by simpa only [run] using hsemanticSome)
            rw [hterminalNone] at hterminalSome
            simp at hterminalSome
        | inl extracted =>
            unfold ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeExtractorV
            rw [family.adaptiveStatementKnowledgeOutcomeV_eq_core_of_none
              basis view hcharV hfacts hfinderNone]
            unfold ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeOutcomeCoreV
              ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeOutcomeCoreWithAcceptanceV
            rw [hacceptsEq]
            dsimp only
            rw [dif_pos hz, dif_neg hattack, hout]
            dsimp only
            rw [hrootsEq]
            dsimp only
            rw [dif_neg (by simpa only [difference, source, fixed, data, output]
              using hsupport)]
            rw [show family.semanticOutcome?V basis view _ = some (Sum.inl extracted) by
              simpa only [run] using houtcomeEq]
            rfl

/-- A single DLOG relation finder for the adaptively selected Action count. -/
def selectedRelationFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions) :
    (basis : AdaptiveActionCountBasis) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O => (family.selectedRelationFinderWithCalls basis O).1

/-- Verification acceptance for the count and proof selected by the one shared
execution. -/
def selectedAccepts {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) : Prop := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let cache := family.selectedCachedRun basis O
  exact component.acceptsV basis cache.toRunView

/-- Witness-only projection for the adaptively selected count.  It consumes the
same retained output, annotations, and challenge vectors as
`selectedRelationFinder`; no fixed-count adversary is run on a separate table. -/
def selectedKnowledgeExtractor {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    let selected := (family.cachedExecution basis O).1
    Option (ActionTerminal.ActionBundleWitness selected.output.inputs) := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let cache := family.selectedCachedRun basis O
  let hchar := family.selectedCachedRun_pairCount_lt basis O
  let finder := family.selectedRelationFinderWithCalls basis O
  exact component.adaptiveStatementKnowledgeExtractorV basis cache.toRunView hchar finder.1
    (fun hnone => family.selectedCachedRun_semanticStageFacts basis O
      (family.selectedRelationFinderWithCalls_none_provenance basis O hnone))

/-- Acceptance with no extracted Action-bundle witness at the count selected by
the shared adversary. -/
def selectedKnowledgeFailureEvent {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions) :
    Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | family.selectedAccepts q.1 q.2 ∧
    family.selectedKnowledgeExtractor q.1 q.2 = none}

/-- The four concrete statistical failure surfaces on the count selected by the
shared run: `z = 0`, the guarded IPA binding discrepancy, a failed deployed-root
check, or one of the five Action semantic challenge surfaces. -/
def selectedStatisticalSurface {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) : Prop := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let view := (family.selectedCachedRun basis O).toRunView
  exact view.pre 10 = 0 ∨
    fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk (adaptiveActionCountParams selected.count) basis)
      (adaptiveActionStatementInstanceCommitment
        (adaptiveActionCountParams selected.count) basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds ∨
    (∃ witness,
      component.batchOutcomeV basis view = PSum.inl witness ∧
        ¬component.BatchGoodRootsV basis view witness) ∨
    (∃ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      view.pre n11 ∈ adaptiveActionSurfaceAt
        (adaptiveActionCountParams selected.count) basis view.output.inputs n
        view.output.toAlgebraicWfProof.proof.1
        (ComputedAdaptiveActionStatementFSFamily.semanticRepresentationTarget
          view.output n ++ component.fixedRepresentations basis)
        (fun i => view.pre (i.castLE (le_of_lt n11.isLt))))

/-- Away from the concrete selected-count surfaces, an accepting shared run with
no relation yields an Action-bundle witness. -/
theorem selectedKnowledgeExtractor_isSome_of_no_surface {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins)
    (haccepts : family.selectedAccepts basis O)
    (hrelation : family.selectedRelationFinder basis O = none)
    (hnosurface : ¬family.selectedStatisticalSurface basis O) :
    (family.selectedKnowledgeExtractor basis O).isSome := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let cache := family.selectedCachedRun basis O
  let view := cache.toRunView
  let hcharV := family.selectedCachedRun_pairCount_lt basis O
  let finder := family.selectedRelationFinderWithCalls basis O
  let hfacts : finder.1 = none → component.SemanticStageFacts basis view := fun hnone =>
    family.selectedCachedRun_semanticStageFacts basis O
      (family.selectedRelationFinderWithCalls_none_provenance basis O hnone)
  have hfinderNone : finder.1 = none := by
    simpa only [finder, selectedRelationFinder] using hrelation
  have hstages := family.selectedRelationFinderWithCalls_none_later basis O hfinderNone
  have hquotientNone : component.statementQuotientRelationFinderV basis view = none := by
    simpa only [selected, component, cache, view] using hstages.1
  have hidentityNone : component.identityRelationFinderV basis view hcharV none
      (fun _ => hfacts hfinderNone) = none := by
    simpa only [selected, component, cache, view, hcharV, hfacts] using hstages.2.1
  have hterminalNone : component.terminalRelationFinderV basis view hcharV = none := by
    simpa only [selected, component, cache, view, hcharV] using hstages.2.2
  have hacceptsV : component.acceptsV basis view := by
    simpa only [selectedAccepts, selected, component, cache, view] using haccepts
  have hno : ¬(view.pre 10 = 0 ∨
      fullAlgebraicBindingAttackZ basis
        (adaptiveActionStatementVk (adaptiveActionCountParams selected.count) basis)
        (adaptiveActionStatementInstanceCommitment
          (adaptiveActionCountParams selected.count) basis view.output.inputs)
        view.output.toAlgebraicWfProof view.pre view.rounds ∨
      (∃ witness,
        component.batchOutcomeV basis view = PSum.inl witness ∧
          ¬component.BatchGoodRootsV basis view witness) ∨
      (∃ n : Fin 5,
        let n11 : Fin 11 := Fin.castLE (by omega) n
        view.pre n11 ∈ adaptiveActionSurfaceAt
          (adaptiveActionCountParams selected.count) basis view.output.inputs n
          view.output.toAlgebraicWfProof.proof.1
          (ComputedAdaptiveActionStatementFSFamily.semanticRepresentationTarget
            view.output n ++ component.fixedRepresentations basis)
          (fun i => view.pre (i.castLE (le_of_lt n11.isLt))))) := by
    simpa only [selectedStatisticalSurface, selected, component, cache, view] using hnosurface
  have hz : view.pre 10 ≠ 0 := fun h => hno (Or.inl h)
  have hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk (adaptiveActionCountParams selected.count) basis)
      (adaptiveActionStatementInstanceCommitment
        (adaptiveActionCountParams selected.count) basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds :=
    fun h => hno (Or.inr (Or.inl h))
  have hgoodRoots : ∀ witness,
      component.batchOutcomeV basis view = PSum.inl witness →
        component.BatchGoodRootsV basis view witness := by
    intro witness hout
    by_contra hbad
    exact hno (Or.inr (Or.inr (Or.inl ⟨witness, hout, hbad⟩)))
  have hsurface : ∀ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      view.pre n11 ∉ adaptiveActionSurfaceAt
        (adaptiveActionCountParams selected.count) basis view.output.inputs n
        view.output.toAlgebraicWfProof.proof.1
        (ComputedAdaptiveActionStatementFSFamily.semanticRepresentationTarget
          view.output n ++ component.fixedRepresentations basis)
        (fun i => view.pre (i.castLE (le_of_lt n11.isLt))) := by
    intro n
    dsimp only
    intro hbad
    exact hno (Or.inr (Or.inr (Or.inr ⟨n, hbad⟩)))
  change (component.adaptiveStatementKnowledgeExtractorV basis view hcharV finder.1 hfacts).isSome
  exact ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeExtractorV_isSome_of_good
    component basis view hcharV finder.1 hfacts hfinderNone hquotientNone hidentityNone
    hterminalNone hacceptsV hz hattack hgoodRoots hsurface

/-- The purely statistical residual after the single relation finder has returned
no relation.  Unlike a generic "failure and no relation" remainder, this event is
the explicit union of the four selected-count statistical surfaces. -/
def selectedStatisticalFailureEvent {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions) :
    Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | family.selectedRelationFinder q.1 q.2 = none ∧
    family.selectedStatisticalSurface q.1 q.2}

/-- Distribution-free reduction-layer split for an adaptively selected count. -/
theorem selectedKnowledgeFailureEvent_subset {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions) :
    family.selectedKnowledgeFailureEvent ⊆
      {q | (family.selectedRelationFinder q.1 q.2).isSome} ∪
        family.selectedStatisticalFailureEvent := by
  intro q hfailure
  by_cases hrelation : (family.selectedRelationFinder q.1 q.2).isSome
  · exact Or.inl hrelation
  · right
    have hnone := Option.not_isSome_iff_eq_none.mp hrelation
    refine ⟨hnone, ?_⟩
    by_contra hnosurface
    have hextracted := family.selectedKnowledgeExtractor_isSome_of_no_surface
      q.1 q.2 hfailure.1 hnone hnosurface
    rw [hfailure.2] at hextracted
    contradiction

end ComputedAdaptiveActionCountFSFamily
end Zcash.Snark
