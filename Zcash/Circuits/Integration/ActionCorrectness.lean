import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionGateCoherence
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

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionCorrectness

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

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
      (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived actionCircuit).numProofs →
        PublicInputs Fp)
    (ps : ProofString
      (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          urs hk (actionCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        urs hk (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          ActionPermutationDomain.blindingFactors_lt pp urs)
        haccepts).CircuitSat
          ch.y hpoly
          (actionCircuit.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).constraints
          (actionCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (actionCircuit.toVerifierKey pp urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    TopLevelCircuitCorrectness
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts)
      (FlatCell actionNumPermCols actionDomainSize)
      (NontrivialRelation (F := Fp) urs.g urs.u urs.w) := by
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
      pp urs hk (actionCircuit.instanceCommitment pp urs inputs) ps ch pU pW a
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
