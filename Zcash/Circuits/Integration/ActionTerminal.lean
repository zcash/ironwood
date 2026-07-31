import Zcash.Circuits.Integration.ActionCorrectness
import Zcash.Circuits.Integration.TopLevelAcceptedModel
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Snark.Soundness.Canonical.Terminal
import Mathlib.Util.AssertNoSorry

/-!
# Accepted Action circuit terminal

This module is the deliberate Clean/Ironwood boundary for the deterministic
soundness terminal. It specializes the verifier-native canonical decoded-model
theorem to the circuit-derived Action verification key and feeds the resulting
constraint satisfaction into the concrete Action bundle endpoint.

`Zcash.Snark.Soundness.Canonical.Terminal` remains entirely in verifier polynomial
language. Clean operation records occur only here, where they are consumed.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionTerminal

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

/--
Accepted decoded-member node binding implies the concrete Action bundle statement,
or produces the existing augmented-basis relation.

The verification key is not a parameter: every verifier object in the statement
uses `actionCircuit.toVerifierKey`. Fixed, advice, instance,
permutation, lookup, and selector claimed evaluations are reconstructed internally
from the accepted assembled queries. No free semantic proposition, `hencodes`,
constraint family, or decoded-column feed remains.
-/
def action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq
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
          urs hk
          (actionCircuit.toVerifierKey pp urs)
          ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs)
          ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs)
          ps ch),
      OpenedMemberDecode
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        urs hk
        (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch)
    (hpoly : CPoly)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        (actionCircuit.toVerifierKey pp urs) ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs)
          ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        urs hk
        (actionCircuit.toVerifierKey pp urs)
        ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
            (actionCircuit.toVerifierKey pp urs)
            ps ch slot point ⊕'
        NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).lBlind -
          hpoly *
            (X ^
              (actionCircuit.toVerifierKey pp urs).n - 1)))
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
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let vk := actionCircuit.toVerifierKey pp urs
  let hblinding : vk.blindingFactors < vk.n :=
    ActionPermutationDomain.blindingFactors_lt pp urs
  let gateCoherence :=
    ActionGateCoherence.topLevelGateCoherence pp urs
  have hnFp : (vk.n : Fp) ≠ 0 := by
    change
      (((2 ^ actionCircuit.domainExponent : ℕ) : Fp)) ≠ 0
    exact TopLevelAssignment.domainSizeCastNeZero
      ActionPermutationDomain.domainExponent_lt
  rcases
      acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
        urs hk vk (actionCircuit.instanceCommitment pp urs inputs) ps ch memberDecode
        haccepts hblinding hpoly hquot
        gateCoherence.fixedQueryCount
        gateCoherence.adviceQueryCount
        gateCoherence.instanceQueryCount
        hbind
        (ActionPermutationDomain.routingCoherent_of_derived pp urs)
        (ActionPermutationDomain.rowsInjective pp urs)
        (ActionPermutationDomain.root pp urs)
        hnFp hxgood with
    hsatisfied | hrelation
  · simpa only [BundleStatement] using
      (TopLevelAcceptedModel.statements_or_relation_of_circuitSat
        actionCircuit pp urs hk inputs ps ch pU pW a
        batchOpenings memberDecode haccepts hblinding hpoly
        hsatisfied hgoodY
        (cell := FlatCell actionNumPermCols actionDomainSize)
        (ActionCorrectness.ofAcceptedCircuitSat
          pp urs hk inputs ps ch pU pW a
          batchOpenings memberDecode haccepts hpoly
          hsatisfied hgoodY permutationExclusions lookupExclusions))
  · exact PSum.inr hrelation

assert_no_sorry action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq

end ActionTerminal

end Zcash.Snark
