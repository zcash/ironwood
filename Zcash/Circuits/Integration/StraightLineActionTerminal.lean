import Zcash.Circuits.Integration.ActionTerminal
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply

/-!
# The rewind-free decode at the Action terminal

This bridge feeds one straight-line decode into `ActionTerminal`. The shared executable outcome
retains either all private witnesses or relation coefficients; `StraightLineActionEvent` prices
the remaining challenge exclusions.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]

local instance vestaInhabitedStraightLineActionTerminal : Inhabited VestaG := ⟨0⟩

/-- Type-valued private witnesses for every Action in the accepted bundle. -/
abbrev ActionBundleWitness {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Type :=
  TopLevelExternalBundleWitness actionCircuit inputs

namespace ActionBundleWitness

/-- An extracted Action witness bundle entails the ordinary existential statement. -/
theorem statement
    {numProofs : ℕ} {inputs : Fin numProofs → PublicInputs Fp}
    (witness : ActionBundleWitness inputs) : BundleStatement inputs :=
  fun proofIndex => (witness proofIndex).statement

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
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch) :=
  action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq
    pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi)
    haccepts _ rfl
    (fun slot point hpoint => PSum.inl (decode.memberBinding hchar slot point hpoint))

/-- The Action endpoint when a pre-`x` constraint identity has already supplied canonical circuit
satisfaction.  This avoids re-testing the `x`-dependent reassembled quotient polynomial. -/
def action_bundleStatement_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
        haccepts).CircuitSat ch.y hpoly
          (actionCircuit.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
          haccepts).constraints
        (actionCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      (actionCircuit.toVerifierKey pp urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  exact TopLevelAcceptedModel.statements_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    (ActionPermutationDomain.blindingFactors_lt pp urs) hpoly hsatisfied hgoodY
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- The pre-`x` Action endpoint retaining the extracted private witnesses as data. -/
def action_bundleWitness_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
        haccepts).CircuitSat ch.y hpoly
          (actionCircuit.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
          haccepts).constraints
        (actionCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      (actionCircuit.toVerifierKey pp urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    ActionBundleWitness inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  exact TopLevelAcceptedModel.witnesses_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    (ActionPermutationDomain.blindingFactors_lt pp urs) hpoly hsatisfied hgoodY
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- The run's decode at the Action circuit's artifacts: extracted from the event, re-rounded to
the run's complete challenge record, and transported along the key and instance identifications. -/
def actionRunDecode
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAlgebraicDecode
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
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
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
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
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl inputs
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
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let pnu := (wrappedAdversary family.toFamily basis).run O
    let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
    let ch := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
    match family.straightLineConstraintOutcome? static basis O with
    | none => none
    | some (PSum.inr relation) =>
        some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
          (pp.mergeDerived actionCircuit).k basis ▸
            AugmentedRelationWitness.toAlgebraicRelationWitness relation))
    | some (PSum.inl success) =>
        let decode : DeployedAlgebraicDecode urs rfl
            (actionCircuit.toVerifierKey pp urs)
            (actionCircuit.instanceCommitment pp urs inputs) pnu.1.proof.1 ch
            (pnu.1.aMulti (wrappedPreIpaReads pnu))
            (pnu.1.multiU (wrappedPreIpaReads pnu))
            (pnu.1.multiBlind (wrappedPreIpaReads pnu)) := hI basis ▸ hvk basis ▸
          success.witness.decode.reRound (runRounds family.toFamily basis O)
        let haccepts : DeployedAccepts urs rfl
            (actionCircuit.toVerifierKey pp urs)
            (actionCircuit.instanceCommitment pp urs inputs) pnu.1.proof.1 ch :=
          hI basis ▸ hvk basis ▸ success.accepts
        let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs) haccepts
        let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts
        match hxgood : szBadSetAvoidance?
            (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
                model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
                ch.y model.chunkLen model.l0 model.lLast model.lBlind
              - polynomial CommitmentId.vanishingH
                  * (X ^ (actionCircuit.toVerifierKey pp urs).n - 1)) ch.x with
        | some hxgoodProof =>
          let hn : (actionCircuit.toVerifierKey pp urs).n ≠ 0 := by
            change 2 ^ actionCircuit.domainExponent ≠ 0
            positivity
          match hgoodY : foldSplitAvoidance? model.constraints
              (actionCircuit.toVerifierKey pp urs).n hn ch.y with
          | some hgoodYProof =>
            match hpermutation : resolverPermutationChallengeExclusions?
                (actionCircuit.toVerifierKey pp urs) ch polynomial actionActiveRows with
            | some hpermutationProof =>
              match hlookup : TopLevelLookupCoherence.topLevelLookupChallengeExclusions?
                  actionCircuit pp urs ch polynomial with
              | some hlookupProof =>
                let hblinding := ActionPermutationDomain.blindingFactors_lt pp urs
                let gateCoherence := ActionGateCoherence.topLevelGateCoherence pp urs
                let hnFp : ((actionCircuit.toVerifierKey pp urs).n : Fp) ≠ 0 := by
                  change (((2 ^ actionCircuit.domainExponent : ℕ) : Fp)) ≠ 0
                  exact TopLevelAssignment.domainSizeCastNeZero
                    ActionPermutationDomain.domainExponent_lt
                match acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
                    urs rfl (actionCircuit.toVerifierKey pp urs)
                    (actionCircuit.instanceCommitment pp urs inputs) pnu.1.proof.1 ch
                    (fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts hblinding
                    (polynomial .vanishingH) rfl gateCoherence.fixedQueryCount
                    gateCoherence.adviceQueryCount gateCoherence.instanceQueryCount
                    (fun slot point hpoint =>
                      PSum.inl (decode.memberBinding (hchar basis O) slot point hpoint))
                    (ActionPermutationDomain.routingCoherent_of_derived pp urs)
                    (ActionPermutationDomain.rowsInjective pp urs)
                    (ActionPermutationDomain.root pp urs) hnFp
                    (by exact hxgoodProof.down) with
                | PSum.inr relation =>
                    some (Sum.inr (augmentedBasis_ursOfAugmentedBasis
                      (pp.mergeDerived actionCircuit).k basis ▸
                        AugmentedRelationWitness.toAlgebraicRelationWitness relation))
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
                          (pp.mergeDerived actionCircuit).k basis ▸
                            AugmentedRelationWitness.toAlgebraicRelationWitness relation))
              | none => none
            | none => none
          | none => none
        | none => none

/-- Relation-only projection retained for the ordinary-soundness reduction. -/
def actionTerminalRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match actionTerminalWitnessOrRelationFinder pp family static inputs hvk hI hchar basis O with
  | some (Sum.inr relation) => some relation
  | _ => none

/-- One executable straight-line outcome shared by the witness extractor and DLOG projection. -/
def actionKnowledgeOutcome
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match family.straightLineConstraintRelationFinder basis O with
  | some relation => some (Sum.inr relation)
  | none => actionTerminalWitnessOrRelationFinder pp family static inputs hvk hI hchar basis O

/-- Executable private-witness extractor for the straight-line/sequential presentation. -/
def actionKnowledgeExtractor
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (ActionBundleWitness inputs) := fun basis O =>
  match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
  | some (Sum.inl witness) => some witness
  | _ => none

/-- The single relation finder priced by the final Action capstone: the existing IPA/unbatching/
quotient finder first, followed by the executable Action-terminal finder. -/
def actionRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
    | some (Sum.inr relation) => some relation
    | _ => none

/-- The witness projection preserves the left branch of the shared outcome exactly. -/
theorem actionKnowledgeExtractor_eq_some_of_outcome_eq_inl
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
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
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
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
