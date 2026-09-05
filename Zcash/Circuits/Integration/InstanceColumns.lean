import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Public-instance commitment provenance

This module connects the canonical decoded-member route to the public-instance
commitment supplied to the verifier. It is the statement-side analogue of
`FixedColumns`: the decoded polynomial is the zero-padded public row polynomial, or
the two augmented openings compute a nontrivial relation.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

omit [AddCommGroup G] [Module Fp G] in
omit [DecidableEq G] in
/--
An instance-column entry in the accepted key's query layout is enough to produce
the assembled query consumed by canonical member routing.

The evaluation-length premise is not separate: a well-shaped verifying key has one
instance evaluation for each layout entry.
-/
theorem instanceQuery_of_layout
    {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (proofIndex : Fin shape.numProofs)
    (column : ℕ) (rotation : ℤ)
    (hcount :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (hlayout : (column, rotation) ∈ vk.instanceQueryLayout) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .instanceCol proofIndex column := by
  obtain ⟨queryIndex, hqueryIndex, hentry⟩ :=
    List.mem_iff_getElem.mp hlayout
  have hevalIndex : queryIndex < shape.numInstanceQueries := by
    simpa only [← hcount] using hqueryIndex
  obtain ⟨q, hq, hqid, -⟩ :=
    instance_query_mem_assembleQueries_eval
      vk instanceCommitment ps ch proofIndex hqueryIndex hevalIndex
  refine ⟨q, hq, ?_⟩
  rw [List.getD_eq_getElem _ _ hqueryIndex, hentry] at hqid
  exact hqid

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

/--
A canonically routed instance-column opening is the polynomial interpolating the
verifier-supplied public rows, or it computes an augmented commitment relation.
-/
def instanceColumn_eq_rowPolynomial_or_relation
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (proofIndex : Fin shape.numProofs)
    (column : ℕ)
    (key : LagrangeCommitmentKey urs vk.omega)
    (rows : List Fp) (blind : Fp)
    (hcommit :
      instanceCommitment proofIndex column =
        key.commitInstance rows blind)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .instanceCol proofIndex column) :
    relation.polynomial (.instanceCol proofIndex column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega rows ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hsome : (relation.route (.instanceCol proofIndex column)).isSome := by
    obtain ⟨q, hq, hqid⟩ := hquery
    have routed := assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment) vk ps ch relation.groupingCount
      relation.noDuplicateQueries q hq
    unfold CanonicalMemberConstraintRelation.route
    rw [← hqid, routed.route_eq]
    rfl
  let slot := (relation.route (.instanceCol proofIndex column)).get hsome
  have routedInstance :
      relation.route (.instanceCol proofIndex column) =
        some slot := (Option.some_get hsome).symm
  have hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD
          (slot.memberIndex : ℕ) .vanishingH =
        .instanceCol proofIndex column := by
    apply assembledQueryMemberRoute_id
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries
      (.instanceCol proofIndex column) slot
    simpa [CanonicalMemberConstraintRelation.route] using routedInstance
  have href :=
    deployedMemberRef_eq_instanceCommitment
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount slot proofIndex column hid
  let decoded :=
    memberDecode slot.setIndex slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols slot.memberIndex) +
          decoded.uComp slot.memberIndex • urs.u +
          decoded.wComp slot.memberIndex • urs.w =
        key.commitInstance rows blind := by
    calc
      commit urs (decoded.cols slot.memberIndex) +
            decoded.uComp slot.memberIndex • urs.u +
            decoded.wComp slot.memberIndex • urs.w =
          ((deployedSetQueries
              (instanceCommitment := instanceCommitment)
              vk ps ch slot.setIndex).getD
            (slot.memberIndex : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ :=
        decoded.commitment slot.memberIndex
      _ = instanceCommitment proofIndex column := by
        rw [href]
        rfl
      _ = key.commitInstance rows blind := hcommit
  have hbound :=
    coeffsToPoly_eq_instanceRowPolynomial_or_relation
      key rows blind
      (decoded.cols slot.memberIndex)
      (decoded.uComp slot.memberIndex)
      (decoded.wComp slot.memberIndex)
      hrows hopen
  refine bindOrRelationWitness hbound fun heq => ?_
  rw [CanonicalMemberConstraintRelation.polynomial,
    decodedPolynomialResolver, routedInstance]
  exact heq

/--
The accepting run's canonical resolver identifies a queried instance column with
the polynomial committed by the verifier's public-instance commitment, without
requiring circuit satisfaction.
-/
def acceptedInstanceColumn_eq_rowPolynomial_or_relation
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
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (proofIndex : Fin shape.numProofs)
    (column : ℕ)
    (key : LagrangeCommitmentKey urs vk.omega)
    (rows : List Fp) (blind : Fp)
    (hcommit :
      instanceCommitment proofIndex column =
        key.commitInstance rows blind)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .instanceCol proofIndex column) :
    acceptedPolynomial
          (memberDecode := memberDecode) haccepts
          (.instanceCol proofIndex column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega rows ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  let route :=
    assembledQueryMemberRoute
      (instanceCommitment := instanceCommitment)
      vk ps ch routing.1 routing.2
  have hsome : (route (.instanceCol proofIndex column)).isSome := by
    obtain ⟨q, hq, hqid⟩ := hquery
    have routed := assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment) vk ps ch routing.1 routing.2 q hq
    dsimp only [route]
    rw [← hqid, routed.route_eq]
    rfl
  let slot := (route (.instanceCol proofIndex column)).get hsome
  have routedInstance :
      route (.instanceCol proofIndex column) = some slot := (Option.some_get hsome).symm
  have hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD
          (slot.memberIndex : ℕ) .vanishingH =
        .instanceCol proofIndex column := by
    apply assembledQueryMemberRoute_id
      (instanceCommitment := instanceCommitment)
      vk ps ch routing.1 routing.2
      (.instanceCol proofIndex column) slot
    simpa only [route] using routedInstance
  have href :=
    deployedMemberRef_eq_instanceCommitment
      (instanceCommitment := instanceCommitment)
      vk ps ch routing.1 slot proofIndex column hid
  let decoded :=
    memberDecode slot.setIndex slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols slot.memberIndex) +
          decoded.uComp slot.memberIndex • urs.u +
          decoded.wComp slot.memberIndex • urs.w =
        key.commitInstance rows blind := by
    calc
      commit urs (decoded.cols slot.memberIndex) +
            decoded.uComp slot.memberIndex • urs.u +
            decoded.wComp slot.memberIndex • urs.w =
          ((deployedSetQueries
              (instanceCommitment := instanceCommitment)
              vk ps ch slot.setIndex).getD
            (slot.memberIndex : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ :=
        decoded.commitment slot.memberIndex
      _ = instanceCommitment proofIndex column := by
        rw [href]
        rfl
      _ = key.commitInstance rows blind := hcommit
  have hbound :=
    coeffsToPoly_eq_instanceRowPolynomial_or_relation
      key rows blind
      (decoded.cols slot.memberIndex)
      (decoded.uComp slot.memberIndex)
      (decoded.wComp slot.memberIndex)
      hrows hopen
  refine bindOrRelationWitness hbound fun heq => ?_
  simpa only [
    acceptedPolynomial, acceptedRoute, routing, route,
    decodedPolynomialResolver, routedInstance] using heq

end CanonicalMemberConstraintRelation

end Zcash.Snark
