import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver

/-! # Binding routed polynomials to committed rows

A queried commitment to a row vector determines its decoded polynomial, or the
two openings compute an augmented-basis relation. Routing and the Lagrange/monomial
comparison are shared by fixed, permutation, and public-instance columns.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

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

/-- Canonical routing binds a queried row commitment to its interpolating polynomial,
or computes a relation from the conflicting augmented openings. -/
def decodedPolynomialResolver_eq_rowPolynomial_or_relation
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (hduplicates : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false)
    (id : CommitmentId)
    (key : LagrangeCommitmentKey urs vk.omega) (rows : List Fp) (blind : Fp)
    (hcommit : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = id → q.commitment = .point (key.commitInstance rows blind))
    (hrows : Function.Injective fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = id) :
    decodedPolynomialResolver (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode
      (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
        vk ps ch hcount hduplicates) id =
      instanceRowPolynomial (2 ^ urs.k) vk.omega rows ⊕'
        AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let route := assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
    vk ps ch hcount hduplicates
  have hsome : (route id).isSome := by
    obtain ⟨q, hq, hqid⟩ := hquery
    have routed := assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment) vk ps ch hcount hduplicates q hq
    dsimp only [route]
    rw [← hqid, routed.route_eq]
    rfl
  let slot := (route id).get hsome
  have hroute : route id = some slot := (Option.some_get hsome).symm
  have hid := assembledQueryMemberRoute_id
    (instanceCommitment := instanceCommitment) vk ps ch hcount hduplicates id slot hroute
  have hi : slot.setIndex <
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
    rw [← hcount]
    exact slot.setIndex_lt
  have hm : (slot.memberIndex : ℕ) <
      ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.getD
        slot.setIndex []).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
      slot.memberIndex.isLt
  have hcommitment :
      ((deployedSetQueries (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).1 =
      .point (key.commitInstance rows blind) := by
    obtain ⟨q, hq, href, hqid⟩ := constructIntermediateSets_member_provenance
      (assembleQueries vk instanceCommitment ps ch) slot.setIndex (slot.memberIndex : ℕ)
      hi hm (.point 0, []) .vanishingH
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
      href.trans (hcommit q hq (hqid.symm.trans hid))
  let decoded := memberDecode slot.setIndex slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols slot.memberIndex) +
        decoded.uComp slot.memberIndex • urs.u +
        decoded.wComp slot.memberIndex • urs.w = key.commitInstance rows blind := by
    have h := decoded.commitment slot.memberIndex
    rw [hcommitment] at h
    exact h
  have hbound := coeffsToPoly_eq_instanceRowPolynomial_or_relation
    key rows blind (decoded.cols slot.memberIndex)
    (decoded.uComp slot.memberIndex) (decoded.wComp slot.memberIndex) hrows hopen
  refine bindOrRelationWitness hbound fun heq => ?_
  simpa only [decodedPolynomialResolver, hroute, decodedMemberPolynomial, route] using heq

end Zcash.Snark
