import Zcash.Snark.Soundness.AGM.DeployedRootSets

/-!
# Deterministic deployed decode outside the explicit AGM root sets

The probabilistic layer only needs to price the root sets.  This module proves the complementary
deterministic statement: once the recursive IPA supplies the raw aggregate value, avoiding the
`x4`, `x3`, `x2`, and per-set `x1` roots forces every represented member polynomial to take the
value claimed by the deployed proof string at every routed node.
-/

namespace Zcash.Snark

open Classical Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments

/-- The concrete output of rewind-free deployed value decoding. -/
structure DeployedAlgebraicDecode [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW : Fp) where
  batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW
  x4Values : forall j,
    commitGen (evalVector urs.k ch.x3) (batches.x4.coeffs j) = x4BatchEvals vk instanceCommitment ps ch j
  memberValues : forall i (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
    (coeffsToPoly ((batches.x1 i hi).coeffs m)).eval
        ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (idx : Nat) 0

/-- Avoiding all explicit deployed root sets gives the complete member-value decode. -/
def deployedAlgebraicDecode_of_good_roots [Inhabited G]
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (hvalue : commitGen (evalVector urs.k ch.x3) aggregate = multiopenValue vk instanceCommitment ps ch)
    (hgood4 : ch.x4 ∉ deployedX4RootSet urs hk vk instanceCommitment ps ch batches)
    (hgood3 : ch.x3 ∉ deployedX3RootSet urs hk vk instanceCommitment ps ch batches)
    (hgood2 : ch.x2 ∉ deployedX2RootSet urs hk vk instanceCommitment ps ch batches)
    (hgood1 : forall i, i < deployedX4PairCount vk instanceCommitment ps ch ->
      ch.x1 ∉ deployedX1RootSet urs hk vk instanceCommitment ps ch batches i) :
    DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW := by
  have hx4 : ch.x4 ∉ szBadSet
      (algebraicBatchErrorPolynomial (evalVector urs.k ch.x3)
        batches.x4.coeffs (x4BatchEvals vk instanceCommitment ps ch)) := by
    simpa only [deployedX4RootSet] using hgood4
  have hvalues := deployedX4AlgebraicValues_of_good urs hk vk instanceCommitment ps ch batches.x4
    (evalVector urs.k ch.x3) hvalue hx4
  have hx3poly : ch.x3 ∉ szBadSet (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batches.x4) := by
    intro hx
    apply hgood3
    simp only [deployedX3RootSet, Finset.mem_coe, Finset.mem_union]
    exact Or.inl hx
  have hx3points : ch.x3 ∉ deployedAllPts vk instanceCommitment ps ch := by
    intro hx
    apply hgood3
    simp only [deployedX3RootSet, Finset.mem_coe, Finset.mem_union]
    exact Or.inr hx
  have hnode3 : forall j : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      (vanishingProd (deployedAlgebraicSetPoints vk instanceCommitment ps ch j)).eval ch.x3 ≠ 0 := by
    intro j
    apply vanishingProd_eval_ne
    intro hx
    apply hx3points
    exact deployedSetPts_subset vk instanceCommitment ps ch _ hx
  refine
    { batches := batches
      x4Values := hvalues
      memberValues := ?_ }
  intro i hi idx m
  let node := ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]
  have hnodeAll : node ∈ deployedAllPts vk instanceCommitment ps ch := by
    have hnodeSet : node ∈ deployedSetPts vk instanceCommitment ps ch i := by
      rw [<- deployedSetsForEval_getD_toFinset vk instanceCommitment ps ch hi]
      exact List.mem_toFinset.mpr (List.get_mem _ idx)
    exact deployedSetPts_subset vk instanceCommitment ps ch i hnodeSet
  have hx2 : ch.x2 ∉ szBadSet
      (nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
        (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
        (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batches.x4)
        (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node) := by
    intro hx
    apply hgood2
    exact ⟨node, hnodeAll, hx⟩
  have hx1 : ch.x1 ∉ szBadSet (deployedX1RootPolynomial urs hk vk instanceCommitment ps ch batches i hi idx) := by
    intro hx
    apply hgood1 i hi
    rw [deployedX1RootSet, dif_pos hi]
    exact ⟨idx, Finset.mem_univ _, hx⟩
  exact deployedMemberNodeBinding_of_good_challenges urs hk vk instanceCommitment ps ch batches.x4 hvalues
    i hi (batches.x1 i hi) (by
      intro qc hqc
      rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hi]
      exact deployedSetQueries_eval_length vk instanceCommitment ps ch i qc hqc) idx hnode3 hx3poly hx2 (by
      simpa only [deployedX1RootPolynomial] using hx1) m

end Zcash.Snark
