import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionConstraintBounds
import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Mathlib.Util.AssertNoSorry

/-!
# Action correctness specialization

This module constructs the Action circuit's component-level correctness package
for the canonical polynomial assignment selected by an accepting verifier run.
Final statement and instance-commitment composition remain circuit-generic.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionCorrectness

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Construct the Action circuit's component-level correctness package for the
canonical polynomial assignment selected by an accepting run.

This is the circuit-owned adapter consumed by the generic top-level Vesta
capstone. It exposes gate, fixed/selector, copy, and lookup facts, but no Action
statement.
-/
def ofAcceptedCircuitSat
    (pp : ProofParams) (urs : URS G)
    (hk :
      actionCircuit.domainExponent = urs.k)
    (inputs :
      Fin pp.numProofs →
        PublicInputs Fp)
    (ps : ProofString
      (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges
      actionCircuit.domainExponent Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := actionCircuit.instanceCommitment urs inputs)
          urs hk (actionCircuit.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := actionCircuit.instanceCommitment urs inputs)
          (actionCircuit.toVerifierKey urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := actionCircuit.instanceCommitment urs inputs)
          (actionCircuit.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := actionCircuit.shape.withProofParams pp)
        (instanceCommitment := actionCircuit.instanceCommitment urs inputs)
        urs hk (actionCircuit.toVerifierKey urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
        (actionCircuit.toVerifierKey urs)
        (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat
          ch.y hpoly
          actionCircuit.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          actionCircuit.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        pp.numProofs (actionCircuit.toVerifierKey urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    TopLevelCircuitCorrectness
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts)
      (FlatCell actionNumPermCols actionDomainSize)
      (AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hcorrect :=
    Zcash.Snark.actionTopLevelCircuitCorrectness
      pp urs hk (actionCircuit.instanceCommitment urs inputs) ps ch pU pW a
      batchOpenings memberDecode hpoly relation
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
      (by simpa only [hpolynomial] using permutationExclusions)
      (by simpa only [hpolynomial] using lookupExclusions)
  simpa only [hpolynomial] using hcorrect

assert_no_sorry ofAcceptedCircuitSat

end ActionCorrectness

end Zcash.Snark
