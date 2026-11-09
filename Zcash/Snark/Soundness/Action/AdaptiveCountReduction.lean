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
  split at hnone <;> rename_i hprovenance
  · simp_all
  · exact hprovenance

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

/-- The four statistical bad sets of the count selected by the shared run, at the selected run's
own challenges: `z = 0`; a root of one IPA round quadratic; a root of one of the six multiopen
and IPA-shift polynomials (`outputRootSurface`); or one of the five Action semantic bad sets
(`outputSemanticSurface`). These are the fixed-count families' priced events, read at the
selected output, and `AdaptiveCountSurfaces` prices them over the shared table. -/
def selectedStatisticalSurface {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) : Prop := by
  let selected := (family.cachedExecution basis O).1
  let component := family.components selected.count
  let view := (family.selectedCachedRun basis O).toRunView
  exact view.pre 10 = 0 ∨
    (∃ j, view.rounds j ∈
      szBadSet (view.output.toAlgebraicWfProof.straightLineIpaRootPolynomial
        view.pre view.rounds j)) ∨
    (∃ i : Fin 6,
      view.pre (deployedRootChallengeIndex i) ∈
        component.outputRootSurface basis (deployedRootChallengeIndex i) view.output
          (fun j => view.pre (j.castLE (le_of_lt (deployedRootChallengeIndex i).isLt)))) ∨
    (∃ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      view.pre n11 ∈ component.outputSemanticSurface basis n view.output
        (fun i => view.pre (i.castLE (le_of_lt n11.isLt))))

/-- Away from the four selected-count bad sets, an accepting shared run with no relation yields
an Action-bundle witness: the IPA binding attack would have a round root
(`terminalRelationFinderV_none_attack_root`), bad batch roots would lie on a root surface
(`goodRoots_of_not_rootSurface`), and the semantic surfaces are excluded directly. -/
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
  obtain ⟨hquotientStage, hidentityStage, hterminalStage⟩ :=
    family.selectedRelationFinderWithCalls_none_later basis O hfinderNone
  have hquotientNone : component.statementQuotientRelationFinderV basis view = none := by
    simpa only [selected, component, cache, view] using hquotientStage
  have hidentityNone : component.identityRelationFinderV basis view hcharV none
      (fun _ => hfacts hfinderNone) = none := by
    simpa only [selected, component, cache, view, hcharV, hfacts] using hidentityStage
  have hterminalNone : component.terminalRelationFinderV basis view hcharV = none := by
    simpa only [selected, component, cache, view, hcharV] using hterminalStage
  have hacceptsV : component.acceptsV basis view := by
    simpa only [selectedAccepts, selected, component, cache, view] using haccepts
  have hno : ¬(view.pre 10 = 0 ∨
      (∃ j, view.rounds j ∈
        szBadSet (view.output.toAlgebraicWfProof.straightLineIpaRootPolynomial
          view.pre view.rounds j)) ∨
      (∃ i : Fin 6,
        view.pre (deployedRootChallengeIndex i) ∈
          component.outputRootSurface basis (deployedRootChallengeIndex i) view.output
            (fun j => view.pre (j.castLE (le_of_lt (deployedRootChallengeIndex i).isLt)))) ∨
      (∃ n : Fin 5,
        let n11 : Fin 11 := Fin.castLE (by omega) n
        view.pre n11 ∈ component.outputSemanticSurface basis n view.output
          (fun i => view.pre (i.castLE (le_of_lt n11.isLt))))) := by
    simpa only [selectedStatisticalSurface, selected, component, cache, view] using hnosurface
  have hz : view.pre 10 ≠ 0 := fun h => hno (Or.inl h)
  have hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk (adaptiveActionCountParams selected.count) basis)
      (adaptiveActionStatementInstanceCommitment
        (adaptiveActionCountParams selected.count) basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds := fun hattack =>
    hno (Or.inr (Or.inl (component.terminalRelationFinderV_none_attack_root basis view hcharV
      hterminalNone hacceptsV hz hattack)))
  have hgoodRoots : ∀ witness,
      component.batchOutcomeV basis view = PSum.inl witness →
        component.BatchGoodRootsV basis view witness := fun witness _ =>
    witness.goodRoots_of_not_rootSurface component basis view fun i hmem =>
      hno (Or.inr (Or.inr (Or.inl ⟨i, hmem⟩)))
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
the explicit union of the four selected-count bad sets. -/
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
