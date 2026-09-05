import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.AGM.ExecutableDeployedRoots

/-!
# Shared Action terminal support

This module retains the adaptive-run abbreviations used by the stage-local surface reconstruction
and provides the statement-independent terminal checker shared by adaptive-statement extraction.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance vestaInhabitedAdaptiveActionTerminal : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The adaptive adversary's one wrapped run. -/
abbrev adaptiveActionRunOutput
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :=
  (wrappedAdversary family.toFamily basis).run O

/-- The complete challenge record of the one adaptive run. -/
abbrev adaptiveActionRunRecord
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
    (runRounds family.toFamily basis O)

/-- Execute the Action terminal checks for one represented proof while retaining either the
extracted private witnesses or explicit relation data.  This semantic core is independent of how
the statement and proof were selected. -/
def actionWitnessOrRelationOfDecode?
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (a : Fin (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp)
    (pU pW : Fp)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch < scalarFieldOrder)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch a pU pW)
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch) :
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs) haccepts
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  match hxgood : szBadSetAvoidance?
      ((combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind)
        - polynomial CommitmentId.vanishingH
          * (X ^ actionCircuit.n - 1)) ch.x with
  | none => none
  | some hxgoodProof =>
      let hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
      match hgoodY : foldSplitAvoidance? model.constraints
          actionCircuit.n hn ch.y with
      | none => none
      | some hgoodYProof =>
          match hpermutation : resolverPermutationChallengeExclusions?
              pp.numProofs (actionCircuit.toVerifierKey urs) ch polynomial actionActiveRows with
          | none => none
          | some hpermutationProof =>
              match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
                  actionCircuit pp urs ch polynomial with
              | none => none
              | some hlookupProof =>
                  let hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs
                  let hnFp : (actionCircuit.n : Fp) ≠ 0 :=
                    TopLevelAssignment.domainSizeCastNeZero
                      ActionConstraintBounds.domainExponent_lt
                  match acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
                      urs rfl (actionCircuit.toVerifierKey urs)
                      (actionCircuit.instanceCommitment urs inputs) ps ch
                      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hblinding
                      (polynomial .vanishingH) rfl
                      (actionCircuit.toVerifierKey_fixedQueryCount urs)
                      (actionCircuit.toVerifierKey_adviceQueryCount urs)
                      (actionCircuit.toVerifierKey_instanceQueryCount urs)
                      (fun slot point hpoint =>
                        PSum.inl (decode.memberBinding hchar slot point hpoint))
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
                          inputs ps ch pU pW a decode hchar haccepts
                          (polynomial .vanishingH) hsatisfied hgoodYProof.down
                          hpermutationProof.down
                          hlookupProof.down with
                      | PSum.inl witness => some (Sum.inl witness)
                      | PSum.inr relation =>
                          some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
                            (actionCircuit.shape.withProofParams pp).k basis ▸ relation))

/-- The pointwise semantic terminal is complete whenever all of its finite exclusions hold. -/
theorem actionWitnessOrRelationOfDecode?_isSome_of
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (a : Fin (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp)
    (pU pW : Fp)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch < scalarFieldOrder)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch a pU pW)
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps ch)
    (hxgood :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
      ch.x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind - polynomial .vanishingH *
            (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      ∀ j, ch.y ∉ szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : ResolverPermutationChallengeExclusions pp.numProofs
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (hlookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    (actionWitnessOrRelationOfDecode?
      pp basis inputs ps a pU pW ch hchar decode haccepts).isSome := by
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
  dsimp only at hxgood hgoodY
  have hxSome := (szBadSetAvoidance?_isSome_iff _ _).2 hxgood
  have hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
  have hySome := foldSplitAvoidance?_isSome_of model.constraints _ hn _ hgoodY
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of _ _ _ _ _ hpermutation
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      _ _ hlookup
  obtain ⟨hxProof, hxEq⟩ := Option.isSome_iff_exists.mp hxSome
  obtain ⟨hyProof, hyEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpProof, hpEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlProof, hlEq⟩ := Option.isSome_iff_exists.mp hlSome
  unfold actionWitnessOrRelationOfDecode?
  dsimp only
  rw [hxEq, hyEq, hpEq, hlEq]
  dsimp only
  split
  · rfl
  · split <;> rfl

end ActionTerminal

end Zcash.Snark
