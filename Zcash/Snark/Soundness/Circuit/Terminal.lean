import Zcash.Circuits.Integration.TopLevelInterpretation
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Canonical.Terminal
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Mathlib.Util.AssertNoSorry

set_option maxHeartbeats 20000

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`. It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle, and binds that statement
to the public inputs supplied to an accepting verifier.

The circuit's compiler laws and field support discharge the representation
boundaries generically. Callers supply the permutation and lookup challenge
exclusions; conflicting openings return an executable augmented-basis relation.
-/


namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open Zcash.Arithmetic (deltaFp)

variable
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    [CircuitFieldSupport top]
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.domainExponent Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          urs hk (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := top.instanceCommitment urs inputs)
        urs hk (top.toVerifierKey urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts (top.shape.withProofParams pp) urs hk
        (top.toVerifierKey urs)
        (top.instanceCommitment urs inputs) ps ch)

/--
Satisfaction of the accepted canonical model and the challenge exclusions retain
private witnesses at the public inputs supplied to the verifier.
-/
def topLevelWitnesses_or_relation_of_circuitSat
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (shape := top.shape.withProofParams pp)
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n urs) haccepts).CircuitSat
          ch.y hpoly top.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (shape := top.shape.withProofParams pp)
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          top.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts) (top.usableRowsAt top.domainExponent))
    (lookupExclusions : TopLevelLookup.ChallengeExclusions top pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hwitness := relation.topLevelWitnesses_or_relation top pp urs hk
    (by
      simpa only [CanonicalMemberConstraintRelation.model, hpolynomial] using hgoodY)
    (by simpa only [hpolynomial] using permutationExclusions)
    (by simpa only [hpolynomial] using lookupExclusions)
  rcases hwitness with hwitness | hrelation
  · exact
      TopLevelInstanceCommitment.witnesses_or_relation_of_accepted_topLevelBundleWitness
        top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
        haccepts (by simpa only [hpolynomial] using hwitness)
  · exact PSum.inr hrelation

assert_no_sorry topLevelWitnesses_or_relation_of_circuitSat

/-- Forget the retained private witnesses to obtain the statement-only terminal. -/
def topLevelStatements_or_relation_of_circuitSat
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (shape := top.shape.withProofParams pp)
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n urs) haccepts).CircuitSat
          ch.y hpoly top.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (shape := top.shape.withProofParams pp)
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          top.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts) (top.usableRowsAt top.domainExponent))
    (lookupExclusions : TopLevelLookup.ChallengeExclusions top pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  match topLevelWitnesses_or_relation_of_circuitSat
      top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
      haccepts hpoly hsatisfied hgoodY permutationExclusions lookupExclusions with
  | .inl witnesses => .inl fun proofIndex =>
      (witnesses proofIndex).statement
  | .inr relation => .inr relation

assert_no_sorry topLevelStatements_or_relation_of_circuitSat

/--
Accepted decoded-member binding reaches the statement of any top-level circuit.

The verifier-native quotient terminal is circuit-independent. The circuit enters
only through its derived key, public-input commitment, and certified compiler laws.
-/
def topLevelStatements_or_relation_of_decodedMemberPolynomial_eq
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    [CircuitFieldSupport top]
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.domainExponent Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          urs hk (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := top.instanceCommitment urs inputs)
        urs hk (top.toVerifierKey urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts (top.shape.withProofParams pp) urs hk
        (top.toVerifierKey urs)
        (top.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := top.instanceCommitment urs inputs)
        (top.toVerifierKey urs) ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch slot.setIndex →
      (decodedMemberPolynomial
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := top.instanceCommitment urs inputs)
        urs hk (top.toVerifierKey urs)
        ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (shape := top.shape.withProofParams pp)
            (instanceCommitment := top.instanceCommitment urs inputs)
            (top.toVerifierKey urs) ps ch slot point ⊕'
        AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (hxgood :
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode)
          (hblinding :=
            top.toVerifierKey_blindingFactors_lt_n urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        hpoly * (X ^ top.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (shape := top.shape.withProofParams pp)
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          top.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts) (top.usableRowsAt top.domainExponent))
    (lookupExclusions : TopLevelLookup.ChallengeExclusions top pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have terminal :=
    acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
      (G := G) (shape := top.shape.withProofParams pp)
      (R := AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
      (pU := pU) (pW := pW) (a := a)
      (batchOpenings := batchOpenings)
      urs hk (top.toVerifierKey urs)
      (top.instanceCommitment urs inputs) ps ch
  have outcome :=
      terminal memberDecode
  have terminal :=
    outcome haccepts (top.toVerifierKey_blindingFactors_lt_n urs)
  have outcome := terminal hpoly hquot hbind
  have hxgoodVk :
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode)
          (hblinding := top.toVerifierKey_blindingFactors_lt_n urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        hpoly * (X ^ (top.toVerifierKey urs).n - 1)) := by
    simpa only [top.toVerifierKey_n] using hxgood
  have outcome := outcome hxgoodVk
  exact match outcome with
  | .inl hsatisfied => by
      have hsatisfiedTop :
          (CanonicalMemberConstraintRelation.acceptedModel
            (shape := top.shape.withProofParams pp)
            (memberDecode := memberDecode)
            (hblinding := top.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).CircuitSat ch.y hpoly top.n a := by
        simpa only [top.toVerifierKey_n] using hsatisfied
      exact topLevelStatements_or_relation_of_circuitSat
        top pp urs hk inputs ps ch pU pW a
        batchOpenings memberDecode haccepts hpoly
        hsatisfiedTop hgoodY permutationExclusions lookupExclusions
  | .inr relation => PSum.inr relation

assert_no_sorry
  topLevelStatements_or_relation_of_decodedMemberPolynomial_eq

end Zcash.Snark
