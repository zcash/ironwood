import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Multiopen.RowBinding
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Public-instance commitment provenance

This module connects the canonical decoded-member route to the public-instance
commitment supplied to the verifier. Query coverage and the shared row-binding
argument identify the decoded polynomial with the zero-padded public rows, or
compute a relation from conflicting augmented openings.
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
  let routing := canonicalRoutingConditions_of_accepts
    urs hk vk instanceCommitment ps ch haccepts
  simpa only [acceptedPolynomial, acceptedRoute, routing] using
    decodedPolynomialResolver_eq_rowPolynomial_or_relation
      (memberDecode := memberDecode) routing.1 routing.2
      (.instanceCol proofIndex column) key rows blind
      (fun q hq hid => (assembleQueries_instance_commitment
        vk instanceCommitment ps ch q hq proofIndex column hid).trans (congrArg _ hcommit))
      hrows hquery

end CanonicalMemberConstraintRelation

end Zcash.Snark
