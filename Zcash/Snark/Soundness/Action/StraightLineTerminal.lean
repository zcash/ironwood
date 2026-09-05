import Zcash.Circuits.Integration.ActionCorrectness
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.StraightLine.Terminal

/-!
# The rewind-free decode at the Action terminal

This bridge feeds one straight-line decode into `ActionTerminal`. The shared executable outcome
retains either all private witnesses or relation coefficients; `StraightLineEvent` prices
the remaining challenge exclusions.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]

/-- The concrete inhabitant every straight-line module uses; public so importers
composing with the terminal share the same instance term. -/
instance vestaInhabitedStraightLineActionTerminal : Inhabited VestaG := ⟨0⟩

/-- Type-valued private witnesses for every Action in the accepted bundle. -/
abbrev ActionBundleWitness {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Type :=
  TopLevelExternalBundleWitness actionCircuit inputs

namespace ActionBundleWitness

/-- An extracted Action witness bundle entails the ordinary existential statement. -/
theorem statement
    {numProofs : ℕ} {inputs : Fin numProofs → PublicInputs Fp}
    (witness : ActionBundleWitness inputs) : BundleStatement inputs :=
  fun proofIndex => TopLevelSemanticWitness.statement (witness proofIndex)

end ActionBundleWitness

/-- Check every potentially nonzero fold-split witness by direct evaluation.  Witnesses at
indices `j ≥ n` are zero by degree, so this finite traversal returns the full specification-level
avoidance certificate without computing any root set. -/
def foldSplitAvoidance?
    (cs : List (CPoly)) (n : Nat) (hn : n ≠ 0) (y : Fp) :
    Option (PLift (∀ j, y ∉ szBadSet (foldSplitWitness cs n j))) :=
  match finForallOption (fun j : Fin n =>
      szBadSetAvoidance? (foldSplitWitness cs n j.1) y) with
  | none => none
  | some hgood => some ⟨fun j =>
      if hj : j < n then (hgood ⟨j, hj⟩).down
      else not_mem_szBadSet.mpr fun hne =>
        False.elim (hne (foldSplitWitness_zero_of_le hn (Nat.le_of_not_gt hj)))⟩

/-- Complete fold-split avoidance makes the executable check succeed. -/
theorem foldSplitAvoidance?_isSome_of
    (cs : List (CPoly)) (n : Nat) (hn : n ≠ 0) (y : Fp)
    (hgood : ∀ j, y ∉ szBadSet (foldSplitWitness cs n j)) :
    (foldSplitAvoidance? cs n hn y).isSome := by
  have hfinite : ∀ j : Fin n,
      (szBadSetAvoidance? (foldSplitWitness cs n j.1) y).isSome :=
    fun j => (szBadSetAvoidance?_isSome_iff _ _).2 (hgood j.1)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hfinite)
  simp [foldSplitAvoidance?, hfound]

/-- **The Action bundle statement from a rewind-free decode.**  The decode supplies the batch
openings, the member decodes, the `x₄` designation and the member-binding premise; the caller
supplies acceptance and the challenge exclusions.

The member-binding premise never takes its relation branch here: a decode already carries the
value equations, so `memberBinding` lands on the left for every slot and point. -/
def action_bundleStatement_or_relation_of_decode
    (pp : ProofParams) (urs : URS G)
    (hk : (actionCircuit.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
        (actionCircuit.toVerifierKey urs)
        (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hxgood :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding :=
            actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts) .vanishingH *
          (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      ∀ j, ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          actionCircuit.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        pp.numProofs (actionCircuit.toVerifierKey urs) ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
  let polynomial :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  exact topLevelStatements_or_relation_of_decode
    actionCircuit pp urs hk inputs ps ch pU pW a decode hchar haccepts
    ActionConstraintBounds.domainExponent_lt
    hxgood hgoodY
    (fun hsatisfied =>
      ActionCorrectness.ofAcceptedCircuitSat
        pp urs hk inputs ps ch pU pW a
        (decode.toOpenedBatch hchar) memberDecode haccepts
        (polynomial .vanishingH)
        (by
          simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
        (by
          simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
        permutationExclusions lookupExclusions)

/-- The Action endpoint when a pre-`x` constraint identity has already supplied canonical circuit
satisfaction.  This avoids re-testing the `x`-dependent reassembled quotient polynomial. -/
def action_bundleStatement_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (actionCircuit.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat ch.y hpoly
          actionCircuit.n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts).constraints
        actionCircuit.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  exact topLevelStatements_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    hpoly
    (by simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
    (by simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- The pre-`x` Action endpoint retaining the extracted private witnesses as data. -/
def action_bundleWitness_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (actionCircuit.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat ch.y hpoly
          actionCircuit.n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts).constraints
        actionCircuit.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    ActionBundleWitness inputs ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  exact topLevelWitnesses_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    hpoly
    (by simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
    (by simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- The run's decode at the Action circuit's artifacts: extracted from the event, re-rounded to
the run's complete challenge record, and transported along the key and instance identifications. -/
def actionRunDecode
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O)
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O))) :=
  hI ▸ hvk ▸ (straightLineDecode family static basis O hdecoded).reRound
    (runRounds family.toFamily basis O)

/-- The run's acceptance at the Action circuit's artifacts. -/
theorem actionRunAccepts
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
  hI ▸ hvk ▸ straightLineAccepts_of_decoded family static basis O hdecoded

/-- **The Action terminal reached from the straight-line constraint event.**  A family at the
Action shape supplies the decode and the acceptance from its own accepting run, so the terminal
is reached without a rewind.

`hvk` and `hI` identify the family's verifying key and instance commitment with the Action
circuit's, and the run data is transported along them.  Everything is stated at the run's
complete challenge record — acceptance reads the IPA rounds, so the root layer's zero-round
record cannot carry it.  The challenge exclusions are still open, exactly as in
`action_bundleStatement_or_relation_of_decode`. -/
def action_bundleStatement_or_relation_of_straightLineDecoded
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
    (ursOfAugmentedBasis_k _ _).symm inputs
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (actionRunDecode pp family static basis O inputs hvk hI hdecoded)
    hchar
    (actionRunAccepts pp family static basis O inputs hvk hI hdecoded)

/-- Checks terminal exclusions and returns private witnesses or explicit relation coefficients
from the reconstructed run. -/
def actionTerminalWitnessOrRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let pnu := (wrappedAdversary family.toFamily basis).run O
    let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
    let ch := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
    match family.straightLineConstraintOutcome? static basis O with
    | none => none
    | some (PSum.inr relation) =>
        some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
          (actionCircuit.shape.withProofParams pp).k basis ▸ relation))
    | some (PSum.inl success) =>
        let decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs rfl
            (actionCircuit.toVerifierKey urs)
            (actionCircuit.instanceCommitment urs inputs) pnu.1.proof.1 ch
            (pnu.1.aMulti (wrappedPreIpaReads pnu))
            (pnu.1.multiU (wrappedPreIpaReads pnu))
            (pnu.1.multiBlind (wrappedPreIpaReads pnu)) := hI basis ▸ hvk basis ▸
          success.witness.decode.reRound (runRounds family.toFamily basis O)
        let haccepts : DeployedAccepts (actionCircuit.shape.withProofParams pp) urs rfl
            (actionCircuit.toVerifierKey urs)
            (actionCircuit.instanceCommitment urs inputs) pnu.1.proof.1 ch :=
          hI basis ▸ hvk basis ▸ success.accepts
        let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs) haccepts
        let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts
        match hxgood : szBadSetAvoidance?
            (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
                model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
                ch.y model.chunkLen model.l0 model.lLast model.lBlind
              - polynomial CommitmentId.vanishingH
                  * (X ^ actionCircuit.n - 1)) ch.x with
        | some hxgoodProof =>
          let hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
          match hgoodY : foldSplitAvoidance? model.constraints
              actionCircuit.n hn ch.y with
          | some hgoodYProof =>
            match hpermutation : resolverPermutationChallengeExclusions?
                pp.numProofs (actionCircuit.toVerifierKey urs) ch polynomial actionActiveRows with
            | some hpermutationProof =>
              match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
                actionCircuit pp urs ch polynomial with
              | some hlookupProof =>
                let hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs
                let hnFp : (actionCircuit.n : Fp) ≠ 0 :=
                  TopLevelAssignment.domainSizeCastNeZero
                    ActionConstraintBounds.domainExponent_lt
                match acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
                    urs rfl (actionCircuit.toVerifierKey urs)
                    (actionCircuit.instanceCommitment urs inputs) pnu.1.proof.1 ch
                    (fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts hblinding
                    (polynomial .vanishingH) rfl
                    (actionCircuit.toVerifierKey_fixedQueryCount urs)
                    (actionCircuit.toVerifierKey_adviceQueryCount urs)
                    (actionCircuit.toVerifierKey_instanceQueryCount urs)
                    (fun slot point hpoint =>
                      PSum.inl (decode.memberBinding (hchar basis O) slot point hpoint))
                    (actionCircuit.permutationChunkRoutingCoherent urs)
                    (TopLevelAssignment.toVerifierKey_domainRowsInjective
                      urs ActionConstraintBounds.domainExponent_lt)
                    (TopLevelAssignment.toVerifierKey_domainRoot
                      urs ActionConstraintBounds.domainExponent_lt)
                    hnFp
                    (by exact hxgoodProof.down) with
                | PSum.inr relation =>
                    some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
                      (actionCircuit.shape.withProofParams pp).k basis ▸ relation))
                | PSum.inl hsatisfied =>
                    match action_bundleWitness_or_relation_of_decode_circuitSat pp urs rfl
                        inputs pnu.1.proof.1 ch
                        (pnu.1.multiU (wrappedPreIpaReads pnu))
                        (pnu.1.multiBlind (wrappedPreIpaReads pnu))
                        (pnu.1.aMulti (wrappedPreIpaReads pnu)) decode (hchar basis O) haccepts
                        (polynomial .vanishingH) hsatisfied hgoodYProof.down
                        hpermutationProof.down hlookupProof.down with
                    | PSum.inl witness => some (Sum.inl witness)
                    | PSum.inr relation =>
                        some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
                          (actionCircuit.shape.withProofParams pp).k basis ▸ relation))
              | none => none
            | none => none
          | none => none
        | none => none

/-- One executable straight-line outcome shared by the witness extractor and DLOG projection. -/
def actionKnowledgeOutcome
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match family.straightLineConstraintRelationFinder basis O with
  | some relation => some (Sum.inr relation)
  | none => actionTerminalWitnessOrRelationFinder pp family static inputs hvk hI hchar basis O

/-- Executable private-witness extractor for the straight-line/sequential presentation. -/
def actionKnowledgeExtractor
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs) := fun basis O =>
  match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
  | some (Sum.inl witness) => some witness
  | _ => none

/-- The single relation finder priced by the final Action capstone: the existing IPA/unbatching/
quotient finder first, followed by the executable Action-terminal finder. -/
def actionRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
    | some (Sum.inr relation) => some relation
    | _ => none

/-- The witness projection preserves the left branch of the shared outcome exactly. -/
theorem actionKnowledgeExtractor_eq_some_of_outcome_eq_inl
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder)
    (basis) (O) (witness : ActionBundleWitness inputs)
    (houtcome : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
      some (Sum.inl witness)) :
    actionKnowledgeExtractor pp family static inputs hvk hI hchar basis O = some witness := by
  unfold actionKnowledgeExtractor
  rw [houtcome]

/-- The relation projection preserves the right branch of the shared outcome exactly. -/
theorem actionRelationFinder_eq_some_of_outcome_eq_inr
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder)
    (basis) (O) (relation : AlgebraicRelationWitness (F := Fp) basis)
    (houtcome : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
      some (Sum.inr relation)) :
    actionRelationFinder pp family static inputs hvk hI hchar basis O = some relation := by
  unfold actionRelationFinder
  rw [houtcome]

end ActionTerminal

end Zcash.Snark
