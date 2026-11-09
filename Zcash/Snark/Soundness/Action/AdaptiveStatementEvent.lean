import Zcash.Snark.Soundness.Action.AdaptiveStatementComplete
import Zcash.Snark.Soundness.Action.AdaptiveStatementProvenance

/-!
# Adaptive-statement Action event composition

The relation finder combines the load-bearing pre-`theta` instance-coordinate comparison with the
complete one-run Action terminal.  Probability composition keeps the still-to-be-priced
statistical residual explicit; this prevents either silently assuming that residual away or
wrapping an already adaptive theorem in a second query factor.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementEventVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- The identity stage after a completed provenance pass.  The empty provenance result already
certifies that the source-mismatch finder is empty, so this form does not rerun that finder. -/
def identityRelationFinderAfterProvenanceNone {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (hprovenance : family.provenanceRelationFinder basis O = none) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let view := runView family basis O
  family.identityRelationFinderV basis view
    (by simpa only [runView_output, runView_pre, runView_rounds,
      family.runRecord_eq_chRecord] using hchar basis O)
    none
    (fun _ => family.semanticStageFacts_of_sourceFinder_none basis O
      ((family.provenanceRelationFinder_eq_none_iff basis O).1 hprovenance).2.2.2.2)

@[simp] theorem identityRelationFinderAfterProvenanceNone_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (hprovenance : family.provenanceRelationFinder basis O = none) :
    family.identityRelationFinderAfterProvenanceNone hchar basis O hprovenance =
      family.identityRelationFinder hchar basis O := by
  have hsource :=
    ((family.provenanceRelationFinder_eq_none_iff basis O).1 hprovenance).2.2.2.2
  unfold identityRelationFinderAfterProvenanceNone identityRelationFinder
  simp only [hsource]

/-- One combined relation finder paired with its exact stage-traversal count.  Its nested matches
are operationally short-circuiting:
provenance, quotient agreement, the pre-`x` identity branch, and the decoded Action terminal each
run at most once, and later stages are skipped after the first relation. -/
def relationFinderWithCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) × Nat :=
  match hprovenance : family.provenanceRelationFinder basis O with
    | some relation => (some relation, 1)
    | none =>
        match family.statementQuotientRelationFinder basis O with
        | some relation => (some relation, 2)
        | none =>
            match family.identityRelationFinderAfterProvenanceNone hchar basis O hprovenance with
            | some relation => (some relation, 3)
            | none => (family.terminalRelationFinder hchar basis O, 4)

/-- Executable relation projection. -/
def relationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O => (family.relationFinderWithCalls hchar basis O).1

@[simp] theorem relationFinderWithCalls_fst {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.relationFinderWithCalls hchar basis O).1 =
      family.relationFinder hchar basis O := rfl

/-- The short-circuiting implementation is extensionally the original four-check stage list. -/
theorem relationFinder_eq_stages {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.relationFinder hchar basis O =
      ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
        [family.provenanceRelationFinder basis O,
         family.statementQuotientRelationFinder basis O,
         family.identityRelationFinder hchar basis O,
         family.terminalRelationFinder hchar basis O] := by
  unfold relationFinder relationFinderWithCalls
  split <;> rename_i hprovenance
  · simp [hprovenance, ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?]
  · simp only [family.identityRelationFinderAfterProvenanceNone_eq]
    split <;> rename_i hquotient
    · simp [hprovenance, hquotient,
        ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?]
    · split <;> rename_i hidentity
      · simp [hprovenance, hquotient, hidentity,
          ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?]
      · cases hterminal : family.terminalRelationFinder hchar basis O <;>
          simp [hprovenance, hquotient, hidentity,
            ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?]

/-- No result from the combined finder means every coordinate-provenance subfinder was empty. -/
theorem relationFinder_none_provenance {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.relationFinder hchar basis O = none) :
    family.instanceRepresentationRelationFinder basis O = none ∧
      family.preIpaRepresentationRelationFinder basis O = none ∧
      family.ipaRepresentationRelationFinder basis O = none ∧
      family.semanticRepresentationRelationFinder basis O = none ∧
      family.semanticSourceMismatchRelationFinder basis O = none ∧
      family.statementQuotientRelationFinder basis O = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1
    (by simpa only [family.relationFinder_eq_stages hchar basis O] using hnone)
  simp only [List.mem_cons, forall_eq_or_imp] at hall
  have hprovenance :=
    (family.provenanceRelationFinder_eq_none_iff basis O).1 hall.1
  exact ⟨hprovenance.1, hprovenance.2.1, hprovenance.2.2.1,
    hprovenance.2.2.2.1, hprovenance.2.2.2.2, hall.2.1⟩

/-- No result from the combined finder also means the pointwise terminal returned no relation. -/
theorem relationFinder_none_terminal {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.relationFinder hchar basis O = none) :
    family.terminalRelationFinder hchar basis O = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1
    (by simpa only [family.relationFinder_eq_stages hchar basis O] using hnone)
  apply hall
  simp

/-- No result from the combined finder also excludes the zero pre-`x` identity branch. -/
theorem relationFinder_none_identity {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.relationFinder hchar basis O = none) :
    family.identityRelationFinder hchar basis O = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1
    (by simpa only [family.relationFinder_eq_stages hchar basis O] using hnone)
  apply hall
  simp

/-- The exact DLOG-reduction event of the combined adaptive-statement finder. -/
def relationEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | (family.relationFinder hchar q.1 q.2).isSome}

/-! ## Concrete statistical surface events -/

/-- The selected statement's `z = 0` slice. -/
def zeroEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | family.runPreIpaReads q.1 q.2 10 = 0}

/-- The union of the selected statement's round-local IPA discrepancy roots. -/
def ipaEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
    let output := family.runOutput q.1 q.2
    let t := family.ipaPoint q.1 j output
    q.2 t ∈ outputIpaFallbackBad family q.1 j output t q.2 ∧
      family.ipaRepresentationRelationFinder q.1 q.2 = none}

/-- The union of the six selected-statement deployed-root surfaces. -/
def rootEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ i : Fin 6,
    let n := deployedRootChallengeIndex i
    let output := family.runOutput q.1 q.2
    let t := family.preIpaPoint q.1 n output
    q.2 t ∈ outputRootBad family q.1 n output t q.2 ∧
      family.preIpaRepresentationRelationFinder q.1 q.2 = none}

/-- The union of the five selected-statement Action semantic surfaces. -/
def semanticEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ n : Fin 5,
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let output := family.runOutput q.1 q.2
    let t := family.preIpaPoint q.1 n11 output
    q.2 t ∈ outputSemanticBad family q.1 n output t q.2 ∧
      family.semanticRepresentationRelationFinder q.1 q.2 = none}

/-- Every directly priced statistical failure for one adaptive selected statement. -/
def statisticalSurfaceEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  family.zeroEvent ∪ (family.ipaEvent ∪ (family.rootEvent ∪ family.semanticEvent))

/-! ## Deterministic surface exhaustion -/

/-- A batch witness whose six root challenges avoid the output's root surfaces, read at the
view's own earlier challenges, has good roots. -/
theorem BatchWitnessV.goodRoots_of_not_rootSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (witness : family.BatchWitnessV basis view)
    (hroot : ∀ i : Fin 6,
      view.pre (deployedRootChallengeIndex i) ∉
        outputRootSurface family basis (deployedRootChallengeIndex i) view.output
          (fun j => view.pre (j.castLE (le_of_lt (deployedRootChallengeIndex i).isLt)))) :
    family.BatchGoodRootsV basis view witness := by
  obtain ⟨hx1Set, hx2Set, hx3Set, hx4Set, hxiSet, hzSet⟩ := witness.rootSets_eq
  constructor
  · intro hx1
    apply hroot 5
    show view.pre 5 ∈ outputRootSurface family basis 5 view.output
      (fun j => view.pre (j.castLE (le_of_lt (5 : Fin 11).isLt)))
    rw [outputRootSurface_five]
    change view.pre 5 ∈ adaptiveX1AllRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      view.output.proofData.adaptivePreX1MembersCovered (adaptiveStrictPrefixRecord 5 view.pre)
    rw [adaptiveX1AllRootSet_strictPrefix, hx1Set]
    simpa using hx1
  · intro hx2
    apply hroot 4
    show view.pre 6 ∈ outputRootSurface family basis 6 view.output
      (fun j => view.pre (j.castLE (le_of_lt (6 : Fin 11).isLt)))
    rw [outputRootSurface_six]
    change view.pre 6 ∈ adaptiveX2RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      view.output.proofData.adaptivePreX1MembersCovered (adaptiveStrictPrefixRecord 6 view.pre)
    rw [adaptiveX2RootSet_strictPrefix, hx2Set]
    simpa using hx2
  · intro hx3
    apply hroot 3
    show view.pre 7 ∈ outputRootSurface family basis 7 view.output
      (fun j => view.pre (j.castLE (le_of_lt (7 : Fin 11).isLt)))
    rw [outputRootSurface_seven]
    change view.pre 7 ∈ adaptiveX3RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      view.output.proofData.adaptivePreX1MembersCovered
      ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
      (adaptiveStrictPrefixRecord 7 view.pre)
    rw [adaptiveX3RootSet_strictPrefix, hx3Set]
    simpa using hx3
  · intro hx4
    apply hroot 2
    show view.pre 8 ∈ outputRootSurface family basis 8 view.output
      (fun j => view.pre (j.castLE (le_of_lt (8 : Fin 11).isLt)))
    rw [outputRootSurface_eight]
    change view.pre 8 ∈ adaptiveX4RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      view.output.proofData.adaptivePreX1MembersCovered
      ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
      (adaptiveStrictPrefixRecord 8 view.pre)
    rw [adaptiveX4RootSet_strictPrefix, hx4Set]
    simpa using hx4
  · intro hxi
    apply hroot 0
    show view.pre 9 ∈ outputRootSurface family basis 9 view.output
      (fun j => view.pre (j.castLE (le_of_lt (9 : Fin 11).isLt)))
    rw [outputRootSurface_nine]
    change view.pre 9 ∈ adaptiveXiRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      [view.output.proofData.algebraicProof.ipaS]
      view.output.proofData.adaptivePreX1MembersCovered
      ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨view.output.proofData.algebraicProof.ipaS, by simp, rfl⟩
      (adaptiveStrictPrefixRecord 9 view.pre)
    rw [adaptiveXiRootSet_strictPrefix, hxiSet]
    simpa using hxi
  · intro hz
    apply hroot 1
    show view.pre 10 ∈ outputRootSurface family basis 10 view.output
      (fun j => view.pre (j.castLE (le_of_lt (10 : Fin 11).isLt)))
    rw [outputRootSurface_ten]
    change view.pre 10 ∈ adaptiveZRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      [view.output.proofData.algebraicProof.ipaS]
      view.output.proofData.adaptivePreX1MembersCovered
      ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨view.output.proofData.algebraicProof.ipaS, by simp, rfl⟩
      (adaptiveStrictPrefixRecord 10 view.pre)
    rw [adaptiveZRootSet_strictPrefix, hzSet]
    simpa using hz

/-- At one table, a batch witness has good roots outside `rootEvent` when the pre-IPA provenance
finder found no relation: each root fallback at the run's own point is the root surface
(`outputRootBad_actual`), so avoiding the event is avoiding the surfaces. -/
theorem BatchWitnessV.goodRoots_of_not_rootEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hroot : (basis, O) ∉ family.rootEvent)
    (hpre : family.preIpaRepresentationRelationFinder basis O = none) :
    family.BatchGoodRoots basis O witness := by
  apply witness.goodRoots_of_not_rootSurface family basis (runView family basis O)
  intro i hmem
  apply hroot
  refine ⟨i, ?_⟩
  change O (family.preIpaPoint basis (deployedRootChallengeIndex i) (family.runOutput basis O)) ∈
      outputRootBad family basis (deployedRootChallengeIndex i) (family.runOutput basis O)
        (family.preIpaPoint basis (deployedRootChallengeIndex i) (family.runOutput basis O)) O ∧ _
  refine ⟨?_, hpre⟩
  rw [outputRootBad_actual]
  simpa only [runView_output, runView_pre, runPreIpaReads_apply] using hmem

/-! ## Surface pricing -/

/-- The selected-statement zero slice keeps the ordinary one-field query price. -/
theorem zeroEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | family.runPreIpaReads basis O 10 = 0} ≤
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  have hzero := fsAdvantageFull_zero_slice_le (family.adversary basis).erase
    (fun _ _ _ => True)
    (fun (output : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis)) i =>
      output.prefixesPre (family.vkTranscriptRepr basis) i)
    (fun (output : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis)) j =>
      output.prefixes (family.vkTranscriptRepr basis) j)
    10 (family.queryBound basis)
  simpa only [fsWinsFull, true_and, runPreIpaReads, runOutput] using hzero

/-- Union the round-local IPA prices without another adaptive-query loss. -/
theorem ipaEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
        let output := family.runOutput basis O
        let t := family.ipaPoint basis j output
        O t ∈ outputIpaFallbackBad family basis j output t O ∧
          family.ipaRepresentationRelationFinder basis O = none} ≤
      (AdaptiveActionStatementShape pp).k *
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
  have hsub : {O | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
      let output := family.runOutput basis O
      let t := family.ipaPoint basis j output
      O t ∈ outputIpaFallbackBad family basis j output t O ∧
        family.ipaRepresentationRelationFinder basis O = none} ⊆
      ⋃ j : Fin (AdaptiveActionStatementShape pp).k,
        {O | let output := family.runOutput basis O
          let t := family.ipaPoint basis j output
          O t ∈ outputIpaFallbackBad family basis j output t O ∧
            family.ipaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ j : Fin (AdaptiveActionStatementShape pp).k,
        (PMF.uniformOfFintype family.Coins).toOuterMeasure
          {O | let output := family.runOutput basis O
            let t := family.ipaPoint basis j output
            O t ∈ outputIpaFallbackBad family basis j output t O ∧
              family.ipaRepresentationRelationFinder basis O = none} ≤
      ∑ _j : Fin (AdaptiveActionStatementShape pp).k,
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
          gcongr with j
          exact family.ipaBadWithoutRelation_table_le basis j
    _ = _ := by simp

/-- Union the six deployed-root prices into the existing shape-level root budget. -/
theorem rootEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ i : Fin 6,
        let n := deployedRootChallengeIndex i
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n output
        O t ∈ outputRootBad family basis n output t O ∧
          family.preIpaRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * algebraicRootBudget
        (AdaptiveActionStatementShape pp) (AdaptiveActionStatementShape pp).k := by
  have hsub : {O | ∃ i : Fin 6,
      let n := deployedRootChallengeIndex i
      let output := family.runOutput basis O
      let t := family.preIpaPoint basis n output
      O t ∈ outputRootBad family basis n output t O ∧
        family.preIpaRepresentationRelationFinder basis O = none} ⊆
      ⋃ i : Fin 6, {O |
        let n := deployedRootChallengeIndex i
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n output
        O t ∈ outputRootBad family basis n output t O ∧
          family.preIpaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ i : Fin 6, (PMF.uniformOfFintype family.Coins).toOuterMeasure
        {O | let n := deployedRootChallengeIndex i
          let output := family.runOutput basis O
          let t := family.preIpaPoint basis n output
          O t ∈ outputRootBad family basis n output t O ∧
            family.preIpaRepresentationRelationFinder basis O = none} ≤
      ∑ i : Fin 6, (family.Q + 1 : Nat) *
        deployedRootEventBudget (AdaptiveActionStatementShape pp) i := by
          gcongr with i
          let n := deployedRootChallengeIndex i
          have h5n : 5 ≤ (n : Nat) := by
            fin_cases i <;> norm_num [n, deployedRootChallengeIndex]
          simpa only [n, adaptiveRootEventIndex_deployedRootChallengeIndex] using
            (family.rootBadWithoutRelation_table_le basis n h5n)
    _ = (family.Q + 1 : Nat) * ∑ i : Fin 6,
        deployedRootEventBudget (AdaptiveActionStatementShape pp) i := by
          rw [Finset.mul_sum]
    _ ≤ _ := by
      gcongr
      exact deployedRootEventBudget_sum_le (AdaptiveActionStatementShape pp)

/-- Union the five semantic surfaces under their existing pointwise bounds. -/
theorem semanticEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀ (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ n : Fin 5,
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n11 output
        O t ∈ outputSemanticBad family basis n output t O ∧
          family.semanticRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
  have hsub : {O | ∃ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      let output := family.runOutput basis O
      let t := family.preIpaPoint basis n11 output
      O t ∈ outputSemanticBad family basis n output t O ∧
        family.semanticRepresentationRelationFinder basis O = none} ⊆
      ⋃ n : Fin 5, {O |
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n11 output
        O t ∈ outputSemanticBad family basis n output t O ∧
          family.semanticRepresentationRelationFinder basis O = none} := by
    rintro O ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ n : Fin 5, (PMF.uniformOfFintype family.Coins).toOuterMeasure
        {O | let n11 : Fin 11 := Fin.castLE (by omega) n
          let output := family.runOutput basis O
          let t := family.preIpaPoint basis n11 output
          O t ∈ outputSemanticBad family basis n output t O ∧
            family.semanticRepresentationRelationFinder basis O = none} ≤
      ∑ n : Fin 5, (family.Q + 1 : Nat) * epsilon n := by
        gcongr with n
        exact family.semanticBadWithoutRelation_table_le basis n (hsurface n)
    _ = _ := by rw [Finset.mul_sum]

/-- The complete statistical surface union has one shared `(Q + 1)` loss. -/
theorem statisticalSurfaceEvent_prob_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
      (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.statisticalSurfaceEvent) ≤
      (family.Q + 1 : Nat) *
        (1 / Fintype.card Fp +
          (AdaptiveActionStatementShape pp).k *
            (2 / (Fintype.card Fp : ENNReal)) +
          algebraicRootBudget (AdaptiveActionStatementShape pp)
            (AdaptiveActionStatementShape pp).k +
          ∑ n : Fin 5, epsilon n) := by
  have hzero :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.zeroEvent) ≤
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.zeroEvent})
    intro logs
    exact family.zeroEvent_table_le (scalarBasis B logs)
  have hipa :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.ipaEvent) ≤
        (AdaptiveActionStatementShape pp).k *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.ipaEvent})
    intro logs
    exact family.ipaEvent_table_le (scalarBasis B logs)
  have hroot :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.rootEvent) ≤
        (family.Q + 1 : Nat) * algebraicRootBudget
          (AdaptiveActionStatementShape pp) (AdaptiveActionStatementShape pp).k := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.rootEvent})
    intro logs
    exact family.rootEvent_table_le (scalarBasis B logs)
  have hsemantic :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.semanticEvent) ≤
        (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.semanticEvent})
    intro logs
    exact family.semanticEvent_table_le (scalarBasis B logs) epsilon
      (hsurface (scalarBasis B logs))
  unfold statisticalSurfaceEvent
  simp only [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine le_trans (add_le_add hzero (MeasureTheory.measure_union_le _ _)) ?_
  refine le_trans (add_le_add_right (add_le_add hipa
    (MeasureTheory.measure_union_le _ _)) _) ?_
  refine le_trans (add_le_add_right (add_le_add_right (add_le_add hroot hsemantic) _) _) ?_
  ring_nf
  exact le_rfl

/-- The combined adaptive-statement finder has the standard textbook-DLOG reduction. -/
theorem relation_prob_le_of_textbookDL {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.relationEvent hchar) ≤
      bound + 1 / Fintype.card Fp := by
  simpa [relationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B (family.relationFinder hchar) hDL)

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
