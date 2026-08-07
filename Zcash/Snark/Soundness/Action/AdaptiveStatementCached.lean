import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge

/-!
# One-execution adaptive-statement reduction

The original executable stages are individually cached, but composing them by their table-level
entry points re-evaluates the adversary once per stage.  This module retains one adversary output,
one annotation log, and one pair of challenge vectors, then feeds that shared data through every
relation-finder and knowledge-extractor branch.

The cached finder is proved pointwise equal to the existing finder, so all probability and
correctness theorems transfer without changing the adversary game.  Its operational shape has one
adversary execution rather than four finder executions (or five for knowledge extraction); that
is the reuse fact needed by the costed profile.
-/

namespace Zcash.Snark

open Keygen

local instance adaptiveStatementCachedVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- All data shared by the complete relation finder and witness extractor. -/
structure CachedRun (pp : ProofParams) (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) where
  output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)
  annotations : AnnotationLog basis
  pre : Fin 11 → Fp
  rounds : Fin (AdaptiveActionStatementShape pp).k → Fp

/-- Build the shared cache from one already-materialized adversary output and annotation log.
This separates the single adversary traversal from the group-free challenge-vector reads that
consume its result. -/
def cachedRunOfExecution {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (execution : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis) ×
      AnnotationLog basis) : CachedRun pp family basis :=
  let output := execution.1
  let pre := family.preIpaReadVectorOfOutput basis O output
  let rounds := family.ipaReadVectorOfOutput basis O output
  { output := output
    annotations := execution.2
    pre := fun i => pre.get i
    rounds := fun j => rounds.get j }

/-- Run the adversary and materialize all later random-oracle reads exactly once. -/
def cachedRun {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : CachedRun pp family basis :=
  family.cachedRunOfExecution basis O ((family.adversary basis).runWithAnnotations O)

/-- The non-provenance view of a shared execution. -/
def CachedRun.toRunView {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    (cache : CachedRun pp family basis) : RunView pp family basis :=
  { output := cache.output, pre := cache.pre, rounds := cache.rounds }

@[simp] theorem cachedRun_output_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedRun basis O).output = family.runOutput basis O := by
  simp [cachedRun, cachedRunOfExecution, runOutput]

@[simp] theorem cachedRun_annotations_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedRun basis O).annotations = (family.adversary basis).annotations O := by
  simp [cachedRun, cachedRunOfExecution]

@[simp] theorem cachedRun_pre_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedRun basis O).pre = family.runPreIpaReads basis O := by
  funext i
  simp [cachedRun, cachedRunOfExecution, runPreIpaReads, runOutput, preIpaReadsOfOutput]

@[simp] theorem cachedRun_rounds_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedRun basis O).rounds = family.runIpaReads basis O := by
  funext j
  simp [cachedRun, cachedRunOfExecution, runIpaReads, runOutput, ipaReadsOfOutput]

@[simp] theorem cachedRun_toRunView_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedRun basis O).toRunView = runView family basis O := by
  let left := (family.cachedRun basis O).toRunView
  let right := runView family basis O
  have houtput : left.output = right.output := family.cachedRun_output_eq basis O
  have hpre : left.pre = right.pre := family.cachedRun_pre_eq basis O
  have hrounds : left.rounds = right.rounds := family.cachedRun_rounds_eq basis O
  calc
    left = RunView.mk left.output left.pre left.rounds := by cases left; rfl
    _ = RunView.mk right.output right.pre right.rounds :=
      congr (congr (congrArg (fun output => RunView.mk output) houtput) hpre) hrounds
    _ = right := by cases right; rfl

/-- The complete provenance pass over the shared output and annotation log. -/
def provenanceRelationFinderOfCachedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    [family.instanceRepresentationRelationFinderFromAnnotations basis cache.annotations
      cache.output,
     family.preIpaRepresentationRelationFinderFromAnnotations basis cache.annotations
      cache.output,
     family.ipaRepresentationRelationFinderFromAnnotations basis cache.annotations cache.output,
     family.semanticRepresentationRelationFinderFromAnnotations basis cache.annotations
      cache.output,
     family.semanticSourceMismatchRelationFinderOfOutput basis cache.output]

@[simp] theorem provenanceRelationFinderOfCachedRun_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.provenanceRelationFinderOfCachedRun basis (family.cachedRun basis O) =
      family.provenanceRelationFinder basis O := by
  simp [provenanceRelationFinderOfCachedRun, provenanceRelationFinder]

/-- The scalar-characteristic premise transported to the shared view. -/
theorem cachedRun_pairCount_lt {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis
        (family.cachedRun basis O).output.inputs)
      (family.cachedRun basis O).output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k)
        (family.cachedRun basis O).pre (family.cachedRun basis O).rounds) <
        Zcash.Arithmetic.scalarFieldOrder := by
  rw [family.cachedRun_output_eq basis O, family.cachedRun_pre_eq basis O,
    family.cachedRun_rounds_eq basis O]
  simpa only [family.runRecord_eq_chRecord] using hchar basis O

/-- An empty cached provenance pass supplies the semantic facts for the same shared view. -/
theorem semanticStageFacts_of_cachedProvenance_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.provenanceRelationFinderOfCachedRun basis
      (family.cachedRun basis O) = none) :
    family.SemanticStageFacts basis (family.cachedRun basis O).toRunView := by
  rw [family.cachedRun_toRunView_eq basis O]
  apply family.semanticStageFacts_of_sourceFinder_none basis O
  have hprovenance : family.provenanceRelationFinder basis O = none := by
    simpa only [family.provenanceRelationFinderOfCachedRun_eq basis O] using hnone
  exact ((family.provenanceRelationFinder_eq_none_iff basis O).1 hprovenance).2.2.2.2

@[simp] theorem statementQuotientRelationFinderV_cachedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.statementQuotientRelationFinderV basis (family.cachedRun basis O).toRunView =
      family.statementQuotientRelationFinder basis O := by
  rw [family.cachedRun_toRunView_eq basis O]

@[simp] theorem terminalRelationFinderV_cachedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.terminalRelationFinderV basis (family.cachedRun basis O).toRunView
        (family.cachedRun_pairCount_lt hchar basis O) =
      family.terminalRelationFinder hchar basis O := by
  let HasPairCount := fun view : RunView pp family basis =>
    deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder
  let left : {view : RunView pp family basis // HasPairCount view} :=
    ⟨(family.cachedRun basis O).toRunView,
      family.cachedRun_pairCount_lt hchar basis O⟩
  let right : {view : RunView pp family basis // HasPairCount view} :=
    ⟨runView family basis O, by
      simpa only [runView_output, runView_pre, runView_rounds,
        family.runRecord_eq_chRecord] using hchar basis O⟩
  have hready : left = right :=
    Subtype.ext (family.cachedRun_toRunView_eq basis O)
  have hresult := congrArg
    (fun ready => family.terminalRelationFinderV basis ready.1 ready.2) hready
  simpa only [left, right] using hresult

/-- Once the shared provenance pass is empty, the cached identity branch is the existing
table-level identity branch.  Only proof arguments differ after the shared view is identified. -/
theorem identityRelationFinderV_cachedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hprovenance : family.provenanceRelationFinderOfCachedRun basis
      (family.cachedRun basis O) = none) :
    family.identityRelationFinderV basis (family.cachedRun basis O).toRunView
        (family.cachedRun_pairCount_lt hchar basis O) none
        (fun _ => family.semanticStageFacts_of_cachedProvenance_none basis O hprovenance) =
      family.identityRelationFinder hchar basis O := by
  have hprovenanceOld : family.provenanceRelationFinder basis O = none := by
    simpa only [family.provenanceRelationFinderOfCachedRun_eq basis O] using hprovenance
  let HasPairCount := fun view : RunView pp family basis =>
    deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder
  let Ready := fun view : RunView pp family basis =>
    HasPairCount view ∧ family.SemanticStageFacts basis view
  let left : {view : RunView pp family basis // Ready view} :=
    ⟨(family.cachedRun basis O).toRunView,
      family.cachedRun_pairCount_lt hchar basis O,
      family.semanticStageFacts_of_cachedProvenance_none basis O hprovenance⟩
  let oldFacts : family.SemanticStageFacts basis (runView family basis O) :=
    family.semanticStageFacts_of_sourceFinder_none basis O
      ((family.provenanceRelationFinder_eq_none_iff basis O).1 hprovenanceOld).2.2.2.2
  let right : {view : RunView pp family basis // Ready view} :=
    ⟨runView family basis O,
      by simpa only [runView_output, runView_pre, runView_rounds,
        family.runRecord_eq_chRecord] using hchar basis O,
      oldFacts⟩
  have hready : left = right :=
    Subtype.ext (family.cachedRun_toRunView_eq basis O)
  have hresult := congrArg (fun ready =>
    family.identityRelationFinderV basis ready.1 ready.2.1 none
      (fun _ => ready.2.2)) hready
  calc
    _ = family.identityRelationFinderV basis (runView family basis O) right.2.1 none
        (fun _ => right.2.2) := by simpa only [left, right] using hresult
    _ = family.identityRelationFinderAfterProvenanceNone hchar basis O hprovenanceOld := by
      unfold identityRelationFinderAfterProvenanceNone
      congr
    _ = family.identityRelationFinder hchar basis O :=
      family.identityRelationFinderAfterProvenanceNone_eq hchar basis O hprovenanceOld

/-- The last three short-circuiting stages once provenance has been discharged. -/
def relationFinderAfterCachedProvenance {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.SemanticStageFacts basis cache.toRunView) :
    Option (AlgebraicRelationWitness (F := Fp) basis) × Nat :=
  match family.statementQuotientRelationFinderV basis cache.toRunView with
  | some relation => (some relation, 2)
  | none =>
      match family.identityRelationFinderV basis cache.toRunView hcharV none
          (fun _ => facts) with
      | some relation => (some relation, 3)
      | none => (family.terminalRelationFinderV basis cache.toRunView hcharV, 4)

/-- Four short-circuiting reduction stages over a caller-supplied shared run. -/
def relationFinderWithCallsOfCachedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (hfacts : family.provenanceRelationFinderOfCachedRun basis cache = none →
      family.SemanticStageFacts basis cache.toRunView) :
    Option (AlgebraicRelationWitness (F := Fp) basis) × Nat :=
  match hprovenance : family.provenanceRelationFinderOfCachedRun basis cache with
  | some relation => (some relation, 1)
  | none => family.relationFinderAfterCachedProvenance basis cache hcharV
      (hfacts hprovenance)

theorem relationFinderWithCallsOfCachedRun_of_some {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) (hcharV) (hfacts)
    (relation : AlgebraicRelationWitness (F := Fp) basis)
    (hprovenance : family.provenanceRelationFinderOfCachedRun basis cache = some relation) :
    family.relationFinderWithCallsOfCachedRun basis cache hcharV hfacts =
      (some relation, 1) := by
  unfold relationFinderWithCallsOfCachedRun
  split
  · rename_i found hfound
    rw [hprovenance] at hfound
    cases hfound
    rfl
  · rename_i hnone
    rw [hprovenance] at hnone
    cases hnone

theorem relationFinderWithCallsOfCachedRun_of_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) (hcharV) (hfacts)
    (hprovenance : family.provenanceRelationFinderOfCachedRun basis cache = none) :
    family.relationFinderWithCallsOfCachedRun basis cache hcharV hfacts =
      family.relationFinderAfterCachedProvenance basis cache hcharV
        (hfacts hprovenance) := by
  unfold relationFinderWithCallsOfCachedRun
  split
  · rename_i relation hfound
    rw [hprovenance] at hfound
    cases hfound
  · congr

/-- No cached finder result implies that its shared provenance pass was empty. -/
theorem relationFinderWithCallsOfCachedRun_none_provenance {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) (hcharV) (hfacts)
    (hnone : (family.relationFinderWithCallsOfCachedRun basis cache hcharV hfacts).1 = none) :
    family.provenanceRelationFinderOfCachedRun basis cache = none := by
  unfold relationFinderWithCallsOfCachedRun at hnone
  split at hnone
  · simp_all
  · assumption

/-- The complete one-execution relation finder paired with its exact stage count. -/
def cachedRelationFinderWithCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) × Nat :=
  let cache := family.cachedRun basis O
  family.relationFinderWithCallsOfCachedRun basis cache
    (family.cachedRun_pairCount_lt hchar basis O)
    (family.semanticStageFacts_of_cachedProvenance_none basis O)

/-- The complete one-execution relation projection. -/
def cachedRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O => (family.cachedRelationFinderWithCalls hchar basis O).1

/-- The cached reduction is pointwise equal to the existing four-stage reduction. -/
theorem cachedRelationFinder_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.cachedRelationFinder hchar basis O = family.relationFinder hchar basis O := by
  rw [family.relationFinder_eq_stages hchar basis O]
  unfold cachedRelationFinder cachedRelationFinderWithCalls
  dsimp only
  cases hcached : family.provenanceRelationFinderOfCachedRun basis
      (family.cachedRun basis O) with
  | some relation =>
      have hprovenance : family.provenanceRelationFinder basis O = some relation := by
        simpa only [family.provenanceRelationFinderOfCachedRun_eq basis O] using hcached
      rw [family.relationFinderWithCallsOfCachedRun_of_some basis
        (family.cachedRun basis O) _ _ relation hcached]
      simp [
        ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?, hprovenance]
  | none =>
      have hprovenance : family.provenanceRelationFinder basis O = none := by
        simpa only [family.provenanceRelationFinderOfCachedRun_eq basis O] using hcached
      rw [family.relationFinderWithCallsOfCachedRun_of_none basis
        (family.cachedRun basis O) _ _ hcached]
      unfold relationFinderAfterCachedProvenance
      rw [family.statementQuotientRelationFinderV_cachedRun basis O]
      cases hquotient : family.statementQuotientRelationFinder basis O with
      | some relation =>
          simp [ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?, hprovenance]
      | none =>
          simp only
          rw [family.identityRelationFinderV_cachedRun hchar basis O hcached]
          cases hidentity : family.identityRelationFinder hchar basis O with
          | some relation =>
              simp [ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?, hprovenance]
          | none =>
              simp only
              rw [family.terminalRelationFinderV_cachedRun hchar basis O]
              cases hterminal : family.terminalRelationFinder hchar basis O <;>
                simp [ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?, hprovenance]

/-- Functional equality used to transport the DLOG advantage statement. -/
theorem cachedRelationFinder_fun_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    family.cachedRelationFinder hchar = family.relationFinder hchar := by
  funext basis O
  exact family.cachedRelationFinder_eq hchar basis O

/-- The shared execution consumed by both the cost model and the witness-only projection.  Keeping
the finder result and its stage count in this object prevents the cost layer from re-running the
finder or attaching an unrelated trace after the fact. -/
structure CachedKnowledgeExecution {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) where
  value : Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)
  finderResult : Option (AlgebraicRelationWitness (F := Fp) basis)
  finderCalls : Nat

/-- Witness extraction and its retained finder accounting over one shared cache.  The final
transport only changes the selected-input index along `cachedRun_output_eq`; it has no runtime
content. -/
def cachedKnowledgeExecution {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : CachedKnowledgeExecution family basis O := by
  let cache := family.cachedRun basis O
  let hcharV := family.cachedRun_pairCount_lt hchar basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none basis O
  let finder := family.relationFinderWithCallsOfCachedRun basis cache hcharV facts
  let extracted := family.adaptiveStatementKnowledgeExtractorV basis cache.toRunView hcharV
    finder.1 (fun hnone => facts
      (family.relationFinderWithCallsOfCachedRun_none_provenance basis cache hcharV facts hnone))
  have hinputs : cache.output.inputs = (family.runOutput basis O).inputs :=
    congrArg AdaptiveActionStatementOutput.inputs (family.cachedRun_output_eq basis O)
  exact
    { value := hinputs ▸ extracted
      finderResult := finder.1
      finderCalls := finder.2 }

/-- Witness-only projection of the execution object used by the cost layer. -/
def cachedKnowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs) :=
  (family.cachedKnowledgeExecution hchar basis O).value

@[simp] theorem cachedKnowledgeExecution_finderResult {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedKnowledgeExecution hchar basis O).finderResult =
      (family.cachedRelationFinderWithCalls hchar basis O).1 := by
  rfl

@[simp] theorem cachedKnowledgeExecution_finderCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedKnowledgeExecution hchar basis O).finderCalls =
      (family.cachedRelationFinderWithCalls hchar basis O).2 := by
  rfl

private theorem Option.isSome_transport {ι : Type} {α : ι → Type} {i j : ι}
    (h : i = j) (value : Option (α i)) :
    (h ▸ value : Option (α j)).isSome = value.isSome := by
  cases h
  rfl

/-- Cached extraction succeeds on exactly the tables where the existing extractor succeeds. -/
theorem cachedKnowledgeExtractor_isSome_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedKnowledgeExtractor hchar basis O).isSome =
      (family.adaptiveStatementKnowledgeExtractor hchar basis O).isSome := by
  let cache := family.cachedRun basis O
  let hcharV := family.cachedRun_pairCount_lt hchar basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none basis O
  let finder := family.relationFinderWithCallsOfCachedRun basis cache hcharV facts
  let Base := RunView pp family basis × Option (AlgebraicRelationWitness (F := Fp) basis)
  let Ready := fun data : Base =>
    (deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis data.1.output.inputs)
        data.1.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) data.1.pre data.1.rounds) <
      Zcash.Arithmetic.scalarFieldOrder) ∧
    (data.2 = none → family.SemanticStageFacts basis data.1)
  let left : {data : Base // Ready data} :=
    ⟨(cache.toRunView, finder.1), hcharV,
      fun hnone => facts
        (family.relationFinderWithCallsOfCachedRun_none_provenance basis cache hcharV facts
          hnone)⟩
  let right : {data : Base // Ready data} :=
    ⟨(runView family basis O, family.relationFinder hchar basis O),
      by simpa only [runView_output, runView_pre, runView_rounds,
        family.runRecord_eq_chRecord] using hchar basis O,
      fun hnone => family.semanticStageFacts_of_sourceFinder_none basis O
        (family.relationFinder_none_provenance hchar basis O hnone).2.2.2.2.1⟩
  have hfinder : finder.1 = family.relationFinder hchar basis O := by
    simpa only [finder, cachedRelationFinder, cachedRelationFinderWithCalls, cache, hcharV,
      facts] using family.cachedRelationFinder_eq hchar basis O
  have hdata : left.1 = right.1 :=
    Prod.ext (family.cachedRun_toRunView_eq basis O) hfinder
  have hready : left = right := Subtype.ext hdata
  have hsuccess := congrArg (fun ready =>
    (family.adaptiveStatementKnowledgeExtractorV basis ready.1.1 ready.2.1
      ready.1.2 ready.2.2).isSome) hready
  unfold cachedKnowledgeExtractor cachedKnowledgeExecution
  dsimp only
  rw [Option.isSome_transport]
  simpa only [left, right, cache, hcharV, facts, finder] using hsuccess

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
