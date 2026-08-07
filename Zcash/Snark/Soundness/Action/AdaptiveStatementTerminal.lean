import Zcash.Snark.Soundness.Action.AdaptiveStatementAccounting
import Zcash.Snark.Soundness.Action.AdaptiveTerminal

/-!
# Pointwise terminal for adaptive Action statements

This module feeds the statement and proof selected by one adaptive-statement run into the shared
Action semantic terminal.  In particular, every terminal type is indexed by the selected public
inputs rather than by an input fixed outside the random-oracle experiment.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance adaptiveStatementTerminalVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- The represented proof selected by one adaptive-statement run. -/
abbrev runProof {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  (family.runOutput basis O).toAlgebraicWfProof

/-- The eleven pre-IPA answers read at the selected statement's canonical prefixes. -/
def runPreIpaReads {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Fin 11 → Fp :=
  let output := family.runOutput basis O
  family.preIpaReadsOfOutput basis O output

@[simp] theorem runPreIpaReads_apply {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (i : Fin 11) :
    family.runPreIpaReads basis O i =
      O ((family.runOutput basis O).prefixesPre (family.vkTranscriptRepr basis) i) := by
  simp [runPreIpaReads, preIpaReadsOfOutput, preIpaReadVectorOfOutput]

/-- The IPA-round answers used to transport a pre-IPA decode to the full verifier record. -/
def runIpaReads {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Fin (AdaptiveActionStatementShape pp).k → Fp :=
  let output := family.runOutput basis O
  family.ipaReadsOfOutput basis O output

@[simp] theorem runIpaReads_apply {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    family.runIpaReads basis O j =
      O ((family.runOutput basis O).prefixes (family.vkTranscriptRepr basis) j) := by
  simp [runIpaReads, ipaReadsOfOutput, ipaReadVectorOfOutput]

@[simp] theorem runRecord_eq_chRecord {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.runRecord basis O = chRecord (family.runPreIpaReads basis O)
      (family.runIpaReads basis O) := by
  rfl

/-- The pre-IPA challenge record used by the direct multiopen decoder. -/
def runPreIpaRecord {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Challenges (AdaptiveActionStatementShape pp).k Fp :=
  chRecord (family.runPreIpaReads basis O) (fun _ => 0)

/-- Everything the non-provenance finder stages read from one execution: the selected output and
the two materialized canonical challenge vectors.  Provenance separately retains the annotation
log alongside the same kind of output cache. -/
structure RunView (pp : ProofParams) (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) where
  output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)
  pre : Fin 11 → Fp
  rounds : Fin (AdaptiveActionStatementShape pp).k → Fp

/-- The run view of one table.  The adversary runs once, then every canonical challenge is read
once and retained behind its finite lookup function. -/
def runView {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : RunView pp family basis :=
  let output := family.runOutput basis O
  let pre := family.preIpaReadVectorOfOutput basis O output
  let rounds := family.ipaReadVectorOfOutput basis O output
  ⟨output, (fun i => pre.get i), (fun j => rounds.get j)⟩

@[simp] theorem runView_output {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    (O : family.Coins) :
    (runView family basis O).output = family.runOutput basis O := rfl
@[simp] theorem runView_pre {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    (O : family.Coins) :
    (runView family basis O).pre = family.runPreIpaReads basis O := rfl
@[simp] theorem runView_rounds {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    (O : family.Coins) :
    (runView family basis O).rounds = family.runIpaReads basis O := rfl

/-- The selected proof's exact direct `x₄` online-coordinate source, over one run view. -/
abbrev batchX4SourceV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :=
  deployedX4ColumnRepresentationsOfCovered
    view.output.toAlgebraicWfProof
    (adaptiveStatementInstanceRepresentationList
        view.output.instanceRepresentations ++
      family.fixedRepresentations basis)
    view.output.proofData.membersCovered
    view.pre

/-- The selected proof's exact direct `x₄` online-coordinate source. -/
abbrev batchX4Source {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  family.batchX4SourceV basis (runView family basis O)

/-- The direct unbatcher's successful branch, retaining the online-coordinate equalities needed
to identify both the six root surfaces and the later semantic resolver with the selected proof.
Unlike `DeployedBatchWitness`, this record is indexed directly by the adaptive statement output,
so its instance commitment may vary with the oracle table. -/
structure BatchWitnessV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) where
  batches : DeployedAlgebraicBatches
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
    (view.output.toAlgebraicWfProof.aMulti view.pre)
    (view.output.toAlgebraicWfProof.multiU view.pre)
    (view.output.toAlgebraicWfProof.multiBlind view.pre)
  x4Coeffs : batches.x4.coeffs = (family.batchX4SourceV basis view).coeffs
  x4U : batches.x4.uComp = (family.batchX4SourceV basis view).uComp
  x4W : batches.x4.wComp = (family.batchX4SourceV basis view).wComp
  memberCoeffs : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))),
    (batches.x1 i hi).coeffs =
      (deployedMemberRepresentationsOfCovered view.output.toAlgebraicWfProof
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis)
        view.output.proofData.membersCovered
        view.pre i hi).coeffs
  memberU : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))),
    (batches.x1 i hi).uComp =
      (deployedMemberRepresentationsOfCovered view.output.toAlgebraicWfProof
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis)
        view.output.proofData.membersCovered
        view.pre i hi).uComp
  memberW : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))),
    (batches.x1 i hi).wComp =
      (deployedMemberRepresentationsOfCovered view.output.toAlgebraicWfProof
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis)
        view.output.proofData.membersCovered
        view.pre i hi).wComp

/-- The direct unbatcher's successful branch at one table. -/
abbrev BatchWitness {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  family.BatchWitnessV basis (runView family basis O)

/-- The retained direct `x₄` columns reconstruct the selected proof's canonical aggregate. -/
theorem BatchWitnessV.x4Source_reconstruct {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view) :
    (∑ j : Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) + 1),
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x4 ^ (j : Nat) •
        (family.batchX4SourceV basis view).coeffs j) =
      view.output.toAlgebraicWfProof.aMulti view.pre := by
  rw [← witness.x4Coeffs]
  exact witness.batches.x4.reconstruct.symm

/-- The same retained columns reconstruct the aggregate `u` coordinate. -/
theorem BatchWitnessV.x4Source_reconstructU {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view) :
    (∑ j : Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) + 1),
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x4 ^ (j : Nat) *
        (family.batchX4SourceV basis view).uComp j) =
      view.output.toAlgebraicWfProof.multiU view.pre := by
  rw [← witness.x4U]
  exact witness.batches.x4.reconstructU.symm

/-- Construct the direct deployed batches for the selected statement, or expose the first
nontrivial AGM relation encountered while unbatching.

The body repeats the `family.run*` selectors instead of `let`-binding them: the `letToHave`
elaboration pass re-analyzes each local `let` against the full batch record, which used to
exhaust the default heartbeat budget here. -/
def batchOutcomeV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    family.BatchWitnessV basis view ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w :=
  match deployedX4BatchOfCoveredWithSourceOrRelation view.output.toAlgebraicWfProof
      (adaptiveStatementInstanceRepresentationList
          view.output.instanceRepresentations ++
        family.fixedRepresentations basis)
      view.output.proofData.membersCovered view.pre with
  | PSum.inr relation => PSum.inr relation
  | PSum.inl x4Result =>
      match finForallOrRelationWitness (fun i :
          Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis
              view.output.inputs)
            view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))) =>
          deployedX1BatchOfCoveredWithSourceOrRelation view.output.toAlgebraicWfProof
            (adaptiveStatementInstanceRepresentationList
                view.output.instanceRepresentations ++
              family.fixedRepresentations basis)
            view.output.proofData.membersCovered
            view.pre x4Result.batch i i.isLt) with
      | PSum.inr relation => PSum.inr relation
      | PSum.inl results => PSum.inl
          { batches :=
              { x4 := x4Result.batch
                x1 := fun i hi => (results ⟨i, hi⟩).batch }
            x4Coeffs := x4Result.coeffs_eq
            x4U := x4Result.uComp_eq
            x4W := x4Result.wComp_eq
            memberCoeffs := fun i hi => (results ⟨i, hi⟩).coeffs_eq
            memberU := fun i hi => (results ⟨i, hi⟩).uComp_eq
            memberW := fun i hi => (results ⟨i, hi⟩).wComp_eq }

/-- Construct the direct deployed batches at one table. -/
abbrev batchOutcome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  family.batchOutcomeV basis (runView family basis O)


/-- The six direct root exclusions for one successfully constructed batch set. -/
structure BatchGoodRootsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (witness : family.BatchWitnessV basis view) : Prop where
  x1 : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x1 ∉ deployedX1AllRootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) witness.batches
  x2 : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x2 ∉ deployedX2RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) witness.batches
  x3 : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x3 ∉ deployedX3RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) witness.batches
  x4 : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x4 ∉ deployedX4RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)) witness.batches
  xi : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).xi ∉ szBadSet (ipaShiftXiPolynomial
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x3)
      (view.output.toAlgebraicWfProof.aMulti view.pre) -
        multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)))
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x3) view.output.toAlgebraicWfProof.s))
  z : (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).z ∉ szBadSet (ipaShiftZPolynomial
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x3)
      (view.output.toAlgebraicWfProof.aMulti view.pre) -
        multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)))
    (view.output.toAlgebraicWfProof.multiU view.pre)
    view.output.toAlgebraicWfProof.sU
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x3) view.output.toAlgebraicWfProof.s)
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).xi)

/-- The six direct root exclusions at one table. -/
abbrev BatchGoodRoots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O) : Prop :=
  family.BatchGoodRootsV basis (runView family basis O) witness

/-- The shifted aggregate equality obtained from acceptance outside the IPA binding event. -/
def ShiftedValueV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Prop :=
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)
  ch.z ≠ 0 ∧
    commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
        (view.output.toAlgebraicWfProof.aMulti view.pre) =
      multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1 ch +
        ch.z⁻¹ * (view.output.toAlgebraicWfProof.multiU view.pre +
          ch.xi * view.output.toAlgebraicWfProof.sU) -
        ch.xi * commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
          view.output.toAlgebraicWfProof.s

/-- The shifted aggregate equality at one table. -/
abbrev ShiftedValue {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Prop :=
  family.ShiftedValueV basis (runView family basis O)

/-- Good direct roots and the shifted verifier equality decode the selected proof, then transport
the decode across the actual IPA-round challenges. -/
def decodeOfBatchGoodRootsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (witness : family.BatchWitnessV basis view)
    (hgood : family.BatchGoodRootsV basis view witness)
    (hshifted : family.ShiftedValueV basis view) :
    DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
      (view.output.toAlgebraicWfProof.aMulti view.pre)
      (view.output.toAlgebraicWfProof.multiU view.pre)
      (view.output.toAlgebraicWfProof.multiBlind view.pre) := by
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)
  have hvalue : commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      (view.output.toAlgebraicWfProof.aMulti view.pre) =
      multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1 ch :=
    rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _
      hshifted.1 hshifted.2 hgood.xi hgood.z
  have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1 ch witness.batches hgood.x1
  exact (deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 ch witness.batches hvalue hgood.x4 hgood.x3 hgood.x2 hgood1).reRound
      view.rounds

/-- Good direct roots and the shifted equality decode the selected proof at one table. -/
abbrev decodeOfBatchGoodRoots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness)
    (hshifted : family.ShiftedValue basis O) :=
  family.decodeOfBatchGoodRootsV basis (runView family basis O) witness hgood hshifted

/-- Checked Halo2 acceptance over one run view. -/
def acceptsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Prop :=
  DeployedAccepts (AdaptiveActionStatementShape pp)
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)

instance acceptsVDecidable {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Decidable (family.acceptsV basis view) := by
  unfold acceptsV DeployedAccepts
  split <;> infer_instance

/-- Executable deployed-acceptance certificate for the selected statement and proof. -/
def accepts?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Option (PLift (family.acceptsV basis view)) :=
  if haccepts : family.acceptsV basis view then some ⟨haccepts⟩ else none

/-- The field-valued half of the binding-attack predicate.  Once `accepts?V` has established the
verifier equation, deciding the full attack through this predicate avoids evaluating that group
equation a second time. -/
def bindingValueMismatchV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Prop :=
  let proof := view.output.toAlgebraicWfProof
  let nu := view.pre
  innerProduct (proof.aMulti nu) (evalVector (AdaptiveActionStatementShape pp).k (nu 7)) ≠
    multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        proof.proof.1 (chRecord nu (fun _ => 0)) +
      (nu 10)⁻¹ * (proof.multiU nu + nu 9 * proof.sU) -
      nu 9 * innerProduct proof.s
        (evalVector (AdaptiveActionStatementShape pp).k (nu 7))

instance bindingValueMismatchVDecidable {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Decidable (family.bindingValueMismatchV basis view) := by
  unfold bindingValueMismatchV
  infer_instance

/-- Under an already-checked acceptance equation and `z ≠ 0`, the full binding-attack decision
is exactly its field-valued mismatch. -/
theorem fullAlgebraicBindingAttackZ_iff_bindingValueMismatchV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (haccepts : family.acceptsV basis view) (hz : view.pre 10 ≠ 0) :
    fullAlgebraicBindingAttackZ basis (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof view.pre view.rounds ↔
      family.bindingValueMismatchV basis view := by
  have hverifier : DeployedIpaVerifierEq
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := by
    simpa using deployedAccepts_verifierEq
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) haccepts
  simp [fullAlgebraicBindingAttackZ, fullAlgebraicBindingAttack, bindingValueMismatchV,
    hverifier, hz]

/-- Executable deployed-acceptance certificate at one table. -/
abbrev accepts? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (PLift (family.accepts basis O)) :=
  family.accepts?V basis (runView family basis O)


/-- Run all six finite deployed-root checks for one selected batch set. -/
def batchGoodRoots?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (witness : family.BatchWitnessV basis view) :
    Option (PLift (family.BatchGoodRootsV basis view witness)) :=
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let delta := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      (view.output.toAlgebraicWfProof.aMulti view.pre) -
    multiopenValue (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1 ch
  let sEval := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
    view.output.toAlgebraicWfProof.s
  match deployedX1RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1 ch witness.batches with
  | none => none
  | some hx1 =>
      match deployedX2RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1 ch witness.batches with
      | none => none
      | some hx2 =>
          match deployedX3RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis
                view.output.inputs)
              view.output.toAlgebraicWfProof.proof.1 ch witness.batches with
          | none => none
          | some hx3 =>
              match deployedX4RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
                  (adaptiveActionStatementInstanceCommitment pp basis
                    view.output.inputs)
                  view.output.toAlgebraicWfProof.proof.1 ch witness.batches with
              | none => none
              | some hx4 =>
                  match deployedXiRootAvoidance? delta sEval ch.xi with
                  | none => none
                  | some hxi =>
                      match deployedZRootAvoidance? delta
                          (view.output.toAlgebraicWfProof.multiU view.pre)
                          view.output.toAlgebraicWfProof.sU sEval ch.xi ch.z with
                      | none => none
                      | some hz => some ⟨{
                          x1 := by simpa only using hx1.down
                          x2 := by simpa only using hx2.down
                          x3 := by simpa only using hx3.down
                          x4 := by simpa only using hx4.down
                          xi := by simpa only using hxi.down
                          z := by simpa only using hz.down }⟩

/-- Run all six finite deployed-root checks at one table. -/
abbrev batchGoodRoots? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O) :
    Option (PLift (family.BatchGoodRoots basis O witness)) :=
  family.batchGoodRoots?V basis (runView family basis O) witness


/-- Over the scalar field, a generator combination is the inner product with its coefficients. -/
private theorem commitGen_eq_innerProduct {n : ℕ} (g a : Fin n → Fp) :
    commitGen g a = innerProduct a g :=
  Finset.sum_congr rfl fun _ _ => smul_eq_mul _ _

/-- Acceptance and absence of the guarded IPA binding attack imply the shifted decoder equality. -/
theorem shiftedValueV_of_accept_not_attack {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (haccept : family.acceptsV basis view)
    (hz : view.pre 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre
      view.rounds) :
    family.ShiftedValueV basis view := by
  let proof := view.output.toAlgebraicWfProof
  let nu := view.pre
  let rounds := view.rounds
  have hdeployed : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      proof.proof.1 (chRecord nu rounds) := by
    simpa only [acceptsV, nu, rounds, proof] using haccept
  have hacceptFull : fullAlgebraicAccept basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      proof nu rounds :=
    fullAlgebraicAccept_of_deployed basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      proof nu rounds hdeployed
  have heq : innerProduct (proof.aMulti nu)
      (evalVector (AdaptiveActionStatementShape pp).k (nu 7)) =
      multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        proof.proof.1 (chRecord nu (fun _ => 0)) +
      (nu 10)⁻¹ * (proof.multiU nu + nu 9 * proof.sU) -
        nu 9 * innerProduct proof.s
          (evalVector (AdaptiveActionStatementShape pp).k (nu 7)) := by
    by_contra hmismatch
    exact hnot ⟨⟨hacceptFull, hmismatch⟩, hz⟩
  constructor
  · simpa only [ShiftedValueV, runPreIpaRecord, chRecord, nu, proof] using hz
  · simpa only [ShiftedValueV, runPreIpaRecord, chRecord, nu, proof,
      commitGen_eq_innerProduct] using heq

/-- Acceptance and no guarded IPA attack give the shifted equality, at one table. -/
theorem shiftedValue_of_accept_not_attack {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (haccept : family.accepts basis O)
    (hz : family.runPreIpaReads basis O 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O) (family.runPreIpaReads basis O)
      (family.runIpaReads basis O)) :
    family.ShiftedValue basis O :=
  family.shiftedValueV_of_accept_not_attack basis (runView family basis O) haccept hz hnot


/-- Decode and acceptance evidence for the exact statement selected by one run. -/
structure DecodedRunV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) where
  hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) < scalarFieldOrder
  decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
    (view.output.toAlgebraicWfProof.aMulti view.pre)
    (view.output.toAlgebraicWfProof.multiU view.pre)
    (view.output.toAlgebraicWfProof.multiBlind view.pre)
  accepts : family.acceptsV basis view

/-- Decode and acceptance evidence at one table. -/
abbrev DecodedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  family.DecodedRunV basis (runView family basis O)


/-- The four finite semantic exclusions consumed by the shared Action terminal. -/
structure SemanticExclusionsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (run : family.DecodedRunV basis view) where
  xGood :
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) run.accepts
    let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).x ∉ szBadSet
      (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).y model.chunkLen model.l0 model.lLast model.lBlind -
          polynomial .vanishingH * (X ^ actionCircuit.n - 1))
  yGood :
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) run.accepts
    ∀ j, (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).y ∉
      szBadSet (foldSplitWitness model.constraints actionCircuit.n j)
  permutation : ResolverPermutationChallengeExclusions pp.numProofs
    (adaptiveActionStatementVk pp basis) (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
    (CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts)
    actionActiveRows
  lookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
    (CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts)

/-- The four finite semantic exclusions at one table. -/
abbrev SemanticExclusions {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) :=
  family.SemanticExclusionsV basis (runView family basis O) run


/-- Execute the semantic terminal at the adversary-selected statement. -/
def semanticOutcome?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (run : family.DecodedRunV basis view) :
    Option (ActionTerminal.ActionBundleWitness view.output.inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  ActionTerminal.actionWitnessOrRelationOfDecode? pp basis
    view.output.inputs view.output.toAlgebraicWfProof.proof.1
    (view.output.toAlgebraicWfProof.aMulti view.pre)
    (view.output.toAlgebraicWfProof.multiU view.pre)
    (view.output.toAlgebraicWfProof.multiBlind view.pre)
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) run.hchar run.decode run.accepts

/-- Semantic outcome at one table. -/
abbrev semanticOutcome? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) :=
  family.semanticOutcome?V basis (runView family basis O) run


/-- Project explicit relation data from the pointwise semantic outcome. -/
def semanticRelation?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (run : family.DecodedRunV basis view) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.semanticOutcome?V basis view run with
  | some (Sum.inr relation) => some relation
  | _ => none

set_option maxRecDepth 10000 in
/-- Semantic relation projection at one table. -/
abbrev semanticRelation? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) :=
  family.semanticRelation?V basis (runView family basis O) run


/-- Successful semantic exclusions produce witness data or relation data, over one run view. -/
theorem semanticOutcome?V_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (run : family.DecodedRunV basis view)
    (good : family.SemanticExclusionsV basis view run) :
    (family.semanticOutcome?V basis view run).isSome := by
  exact ActionTerminal.actionWitnessOrRelationOfDecode?_isSome_of pp basis
    view.output.inputs view.output.toAlgebraicWfProof.proof.1
    (view.output.toAlgebraicWfProof.aMulti view.pre)
    (view.output.toAlgebraicWfProof.multiU view.pre)
    (view.output.toAlgebraicWfProof.multiBlind view.pre)
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
    run.hchar run.decode run.accepts
    good.xGood good.yGood good.permutation good.lookup

/-- Successful semantic exclusions produce witness data or relation data, at one table. -/
theorem semanticOutcome?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O)
    (good : family.SemanticExclusions basis O run) :
    (family.semanticOutcome? basis O run).isSome :=
  family.semanticOutcome?V_isSome_of basis (runView family basis O) run good

/-- On a false selected statement, the outcome cannot be the witness branch, over one view. -/
theorem semanticRelation?V_isSome_of_false {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (run : family.DecodedRunV basis view)
    (good : family.SemanticExclusionsV basis view run)
    (hfalse : ¬BundleStatement view.output.inputs) :
    (family.semanticRelation?V basis view run).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp
    (family.semanticOutcome?V_isSome_of basis view run good)
  cases outcome with
  | inl witness => exact False.elim (hfalse witness.statement)
  | inr relation =>
      unfold semanticRelation?V
      rw [houtcome]
      rfl

/-- On a false selected statement, the outcome cannot be the witness branch, at one table. -/
theorem semanticRelation?_isSome_of_false {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O)
    (good : family.SemanticExclusions basis O run)
    (hfalse : ¬BundleStatement (family.runOutput basis O).inputs) :
    (family.semanticRelation? basis O run).isSome :=
  family.semanticRelation?V_isSome_of_false basis (runView family basis O) run good hfalse

/-- The terminal relation finder from a supplied acceptance result.  The costed reduction uses
this entry point so the reified verifier MSM controls the remaining branches directly. -/
def terminalRelationFinderWithAcceptanceV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (acceptance : Option (PLift (family.acceptsV basis view))) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
    let proof := view.output.toAlgebraicWfProof
    let nu := view.pre
    let rounds := view.rounds
    match acceptance with
    | none => none
    | some hacceptsProof =>
        let haccepts : family.acceptsV basis view := hacceptsProof.down
        if hz : nu 10 ≠ 0 then
          letI : Decidable (fullAlgebraicBindingAttackZ basis
              (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
              proof nu rounds) :=
            decidable_of_iff (family.bindingValueMismatchV basis view)
              (family.fullAlgebraicBindingAttackZ_iff_bindingValueMismatchV
                basis view haccepts hz).symm
          if hattack : fullAlgebraicBindingAttackZ basis
              (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis
                view.output.inputs)
              proof nu rounds then
            match proof.straightLineBindingAttackZIndexedRootOrRelation nu rounds hattack with
            | PSum.inl _ => none
            | PSum.inr relation =>
                some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
          else
            match family.batchOutcomeV basis view with
            | PSum.inr relation =>
                some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
            | PSum.inl witness =>
                match family.batchGoodRoots?V basis view witness with
                | none => none
                | some hroots =>
                    let hshifted := family.shiftedValueV_of_accept_not_attack
                      basis view haccepts hz hattack
                    let run : family.DecodedRunV basis view :=
                      { hchar := hcharV
                        decode := family.decodeOfBatchGoodRootsV basis view witness
                          hroots.down hshifted
                        accepts := haccepts }
                    family.semanticRelation?V basis view run
        else none

/-- The computed relation finder for one adaptive-statement run.  Acceptance, batch construction,
root checks, decoding, and semantic checks all use the statement selected in that same run. -/
def terminalRelationFinderV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  family.terminalRelationFinderWithAcceptanceV basis view hcharV
    (family.accepts?V basis view)


/-- Terminal relation finder at one table. -/
abbrev terminalRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O => family.terminalRelationFinderV basis (runView family basis O) (hchar basis O)

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
