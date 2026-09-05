import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver

/-!
# Canonical decoded-member constraint relation

The older member capstone accepts fixed columns, permutation sets/chunks, lookups,
and selector polynomials as independent arguments. That is useful for decomposing
the verifier proof, but it is too weak as the semantic handoff to a formal circuit:
those arguments could describe a different constraint model.

This relation retains the decoded batch witness and derives one polynomial resolver
from the deployed query grouping. The complete `ConstraintPolyModel` is then built
canonically from that resolver and the accepted verification key. It is bundle-wide:
one constraint identity covers every proof member, with no selected proof index.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Deployed acceptance supplies the two routing facts used by the canonical decoded
member resolver.

This is verifier-native: the rejecting assembler itself rules out duplicate
commitment/point queries and fixes the number of grouped point sets.
-/
theorem canonicalRoutingConditions_of_accepts
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    deployedX4PairCount
        (instanceCommitment := instanceCommitment)
        vk ps ch =
        (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length ∧
      hasDuplicateCommitmentPoint
        (assembleQueries vk instanceCommitment ps ch) = false := by
  unfold DeployedAccepts at haccepts
  cases hassemble :
      assemble? vk instanceCommitment ps ch with
  | none =>
      rw [hassemble] at haccepts
      exact False.elim haccepts
  | some msm =>
      exact assembledQueryRoutingConditions_of_assemble?_eq_some
        (instanceCommitment := instanceCommitment)
        vk ps ch hassemble

/--
The deterministic semantic payload expected from the extraction/probability stack.

All constraint-bearing polynomials come from `memberDecode` through the canonical
assembled-query route. In particular, fixed columns and the permutation/lookup
families are not caller-supplied.
-/
structure CanonicalMemberConstraintRelation
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (hblinding : vk.blindingFactors < vk.n)
    (y : Fp) (hpoly : CPoly) (deg : ℕ) : Prop where
  groupingCount :
    deployedX4PairCount
      (instanceCommitment := instanceCommitment)
      vk ps ch =
      (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).sets.length
  noDuplicateQueries :
    hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false
  satisfiesCircuit :
    let route :=
      assembledQueryMemberRoute
        (instanceCommitment := instanceCommitment)
        vk ps ch groupingCount noDuplicateQueries
    let poly :=
      decodedPolynomialResolver
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode route
    let model := vk.constraintModel
      (numProofs := shape.numProofs) ch poly hblinding
    model.CircuitSat y hpoly deg a

namespace CanonicalMemberConstraintRelation

variable
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : CPoly} {deg : ℕ}

/-- The canonical commitment-ID route selected by an accepting verifier run. -/
def acceptedRoute
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    CommitmentId →
      Option (DeployedMemberSlot
        (instanceCommitment := instanceCommitment)
        vk ps ch) :=
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  assembledQueryMemberRoute
    (instanceCommitment := instanceCommitment)
    vk ps ch routing.1 routing.2

/-- Decoded member polynomials routed by the accepting assembler. -/
def acceptedPolynomial
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    CommitmentId → CPoly :=
  decodedPolynomialResolver
    (instanceCommitment := instanceCommitment)
    urs hk vk ps ch memberDecode (acceptedRoute haccepts)

/--
Member-node binding opens every assembled query through the accepting run's
canonical resolver, or computes the existing augmented-basis relation.

This is the verifier-native source of the uniform opening family used by the
canonical constraint terminal; no caller-selected route or resolver remains.
-/
def acceptedPolynomial_opens_or_relation
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := instanceCommitment)
          vk ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := instanceCommitment)
            vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) :
    (∀ query ∈ assembleQueries vk instanceCommitment ps ch,
      (acceptedPolynomial
        (memberDecode := memberDecode) haccepts query.commId).eval
          query.point = query.eval)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  simpa only [acceptedPolynomial, acceptedRoute, routing] using
    decodedPolynomialResolver_opens_or_relation
      (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode
      (assembledQueryMemberRoute
        (instanceCommitment := instanceCommitment)
        vk ps ch routing.1 routing.2)
      (assembleQueries vk instanceCommitment ps ch)
      (fun query hquery =>
        assembledQueryMemberRoute_faithful
          (instanceCommitment := instanceCommitment)
          vk ps ch routing.1 routing.2 query hquery)
      hbind

/-- The complete constraint model canonically determined by an accepting run. -/
def acceptedModel
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    ConstraintPolyModel shape.numProofs :=
  vk.constraintModel (numProofs := shape.numProofs) ch
    (acceptedPolynomial
      (memberDecode := memberDecode) haccepts)
    hblinding

/--
Satisfaction of the accepted canonical model constructs the exact relation consumed
by the circuit integration boundary. No fixed, permutation, lookup, or selector
polynomial family is supplied independently.
-/
def ofAcceptedCircuitSat
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hsatisfied :
      (acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          y hpoly deg a) :
    CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg := by
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  refine
    { groupingCount := routing.1
      noDuplicateQueries := routing.2
      satisfiesCircuit := ?_ }
  change
    (vk.constraintModel (numProofs := shape.numProofs) ch
      (decodedPolynomialResolver
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode
        (assembledQueryMemberRoute
          (instanceCommitment := instanceCommitment)
          vk ps ch routing.1 routing.2))
      hblinding).CircuitSat y hpoly deg a
  simpa only [acceptedModel, acceptedPolynomial, acceptedRoute, routing] using
    hsatisfied

/-- The unique commitment-ID route selected by the deployed grouping. -/
def route
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    CommitmentId →
      Option (DeployedMemberSlot
        (instanceCommitment := instanceCommitment)
        vk ps ch) :=
  assembledQueryMemberRoute
    (instanceCommitment := instanceCommitment)
    vk ps ch relation.groupingCount relation.noDuplicateQueries

/-- The decoded polynomial resolver determined by the relation's member openings. -/
def polynomial
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    CommitmentId → CPoly :=
  decodedPolynomialResolver
    (instanceCommitment := instanceCommitment)
    urs hk vk ps ch memberDecode relation.route

/-- The complete verifier-native constraint model determined by the relation. -/
def model
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    ConstraintPolyModel shape.numProofs :=
  vk.constraintModel (numProofs := shape.numProofs)
    ch relation.polynomial hblinding

/--
A good folding challenge splits the canonical bundle-wide identity into the exact
family-separated satisfaction record consumed by gate, permutation, and lookup
semantics.
-/
theorem constraintSatisfaction
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (hn : deg ≠ 0)
    (hgoodY : ∀ j,
      y ∉ szBadSet
        (foldSplitWitness relation.model.constraints deg j)) :
    ConstraintSatisfaction relation.model deg := by
  apply ConstraintSatisfaction.of_circuitSatViaConstraints
    relation.model y hpoly a hn
  · exact relation.satisfiesCircuit
  · exact hgoodY

end CanonicalMemberConstraintRelation

end Zcash.Snark
