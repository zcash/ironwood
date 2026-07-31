import Zcash.Snark.Soundness.AGM.DeployedX1
import Zcash.Snark.Soundness.AGM.ValueUnbatch
import Zcash.Snark.Soundness.Multiopen.NodeBinding

/-!
# Deployed rewind-free multiopen value unbatching

This file specializes the single-challenge root arguments to Halo2's deployed set ordering.  The
`x4` AGM batch supplies fixed aggregate and `qPrime` polynomials.  Its value equations at `x3`
make the deployed multiopen equation a root of the cleared quotient mismatch; a good `x3` proves
the polynomial identity, and a good `x2` then separates the point sets at each node.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals

/-- The represented deployed point-set aggregate polynomials, in `x2`/`x4` reverse order. -/
def deployedAlgebraicSetColumns [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) -> CPoly :=
  fun j => coeffsToPoly (batch.coeffs ⟨(j : Nat), Nat.lt_succ_of_lt j.isLt⟩)

/-- The represented top `x4` slot is the fixed `qPrime` polynomial. -/
def deployedAlgebraicQPrime [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) : CPoly :=
  coeffsToPoly (batch.coeffs
    ⟨deployedX4PairCount vk instanceCommitment ps ch, Nat.lt_succ_self _⟩)

/-- Claimed set interpolants, in the reverse order paired with ascending `x2` powers. -/
def deployedAlgebraicSetInterpolants [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) -> CPoly :=
  fun j => lagrangePoly
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : Nat) ([], [], 0)).1
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : Nat) ([], [], 0)).2.1

/-- Deployed point sets in the reverse order paired with ascending `x2` powers. -/
def deployedAlgebraicSetPoints [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) -> Finset Fp :=
  fun j => deployedSetPts vk instanceCommitment ps ch
    (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : Nat))

/-- The exact deployed `x3` error polynomial.  All of its ingredients are fixed before `x3`
provided the AGM representations are online and squeeze-pinned. -/
def deployedX3ErrorPolynomial [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) : CPoly :=
  clearedQuotientErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
    (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch)
    (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch)
    (fun j => ch.x2 ^ (j : Nat))
    (deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch)

/-- The direct `x3` error polynomial has the deployed degree bound needed to price its sampled
root. -/
theorem deployedX3ErrorPolynomial_natDegree_le
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batch).natDegree <=
      max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card +
        (deployedAllPts vk instanceCommitment ps ch).card := by
  apply clearedQuotientErrorPolynomial_natDegree_le
  ·
    exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
      (le_max_left _ _)
  · intro j
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
        (le_max_left _ _)
    · have hnd := deployedSetsForEval_reverse_getD_nodup vk instanceCommitment ps ch j.isLt
      have hle := lagrangePoly_natDegree_le
        (points := ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : Nat) ([], [], 0)).1)
        (evals := ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : Nat) ([], [], 0)).2.1)
        (List.nodup_iff_injective_getElem.mp hnd)
      have hcard :
          ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : Nat) ([], [], 0)).1.length <=
            (deployedAllPts vk instanceCommitment ps ch).card := by
        rw [<- List.toFinset_card_of_nodup hnd,
          deployedSetsForEval_reverse_getD_toFinset vk instanceCommitment ps ch j.isLt]
        exact Finset.card_le_card (deployedSetPts_subset vk instanceCommitment ps ch _)
      exact le_trans (le_trans hle hcard) (le_max_right _ _)

/-- The `x4` value equations turn the current deployed multiopen equation into the full cleared
quotient identity, except exactly on the explicit `x3` root set. -/
theorem deployedClearedQuotientIdentity_of_good_x3
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (hnode : forall j : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      (vanishingProd (deployedAlgebraicSetPoints vk instanceCommitment ps ch j)).eval ch.x3 ≠ 0)
    (hgood : ch.x3 ∉ szBadSet (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batch)) :
    deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch * vanishingProd (deployedAllPts vk instanceCommitment ps ch) =
      ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch),
        C (ch.x2 ^ (j : Nat)) *
          ((deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch j -
              deployedAlgebraicSetInterpolants vk instanceCommitment ps ch j) *
            coProd (deployedAllPts vk instanceCommitment ps ch) (deployedAlgebraicSetPoints vk instanceCommitment ps ch j)) := by
  apply clearedQuotientIdentity_of_good_x3
    (deployedAllPts vk instanceCommitment ps ch)
    (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
    (fun j => deployedSetPts_subset vk instanceCommitment ps ch _)
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch)
    (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch)
    (fun j => ch.x2 ^ (j : Nat))
    (deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch)
    ch.x3 hnode ?_ hgood
  apply hsamp_of_multiopenEval_reversed
    (deployedSetsForEval vk instanceCommitment ps ch)
    (deployedSetsForEval_length vk instanceCommitment ps ch)
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch)
    (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch)
    (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
    ch.x2 ch.x3
    ((deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch).eval ch.x3)
  · rw [deployedAlgebraicQPrime, coeffsToPoly_eval, hvalues, x4BatchEvals_top,
      deployedBaseEval_eq_multiopenEval]
  · intro j
    exact deployedSetsForEval_reverse_getD_nodup vk instanceCommitment ps ch j.isLt
  · intro j
    exact deployedSetsForEval_reverse_getD_toFinset vk instanceCommitment ps ch j.isLt
  · intro j
    rw [deployedAlgebraicSetColumns, coeffsToPoly_eval, hvalues]
    exact (deployedSetsForEval_reverse_getD_u vk instanceCommitment ps ch j.isLt).symm
  · intro j
    exact lagrangePoly_eval
      (List.nodup_iff_injective_getElem.mp
        (deployedSetsForEval_reverse_getD_nodup vk instanceCommitment ps ch j.isLt)) ch.x3

/-- Once the cleared identity is known, a good single `x2` binds an aggregate polynomial to its
claimed interpolant at any deployed node. -/
theorem deployedAggregateNodeBinding_of_good_x2
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hid : deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch *
        vanishingProd (deployedAllPts vk instanceCommitment ps ch) =
      ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch),
        C (ch.x2 ^ (j : Nat)) *
          ((deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch j -
              deployedAlgebraicSetInterpolants vk instanceCommitment ps ch j) *
            coProd (deployedAllPts vk instanceCommitment ps ch) (deployedAlgebraicSetPoints vk instanceCommitment ps ch j)))
    (j : Fin (deployedX4PairCount vk instanceCommitment ps ch)) {node : Fp}
    (hnode : node ∈ deployedAlgebraicSetPoints vk instanceCommitment ps ch j)
    (hgood : ch.x2 ∉ szBadSet
      (nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
        (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
        (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch)
        (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node)) :
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch j).eval node =
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch j).eval node := by
  exact nodeBinding_of_good_x2
    (deployedAllPts vk instanceCommitment ps ch)
    (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch)
    (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch)
    (deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch)
    ch.x2 hid j hnode (deployedSetPts_subset vk instanceCommitment ps ch _ hnode) hgood

/-! ## Within-set `x1` value separation -/

omit [AddCommGroup G] [Module Fp G] in
/-- Reflecting the reverse-order `x2` slot for set `i` reads the original deployed set entry `i`. -/
theorem deployedSetsForEval_reverse_getD_reflect
    [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch) :
    (deployedSetsForEval vk instanceCommitment ps ch).reverse.getD
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - i) ([], [], 0) =
      (deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0) := by
  have hlen := deployedSetsForEval_length vk instanceCommitment ps ch
  rw [List.getD_eq_getElem?_getD (l := (deployedSetsForEval vk instanceCommitment ps ch).reverse),
    List.getElem?_reverse (by rw [hlen]; omega), hlen,
    show deployedX4PairCount vk instanceCommitment ps ch - 1 -
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - i) = i by omega,
    <- List.getD_eq_getElem?_getD]

/-- The reconstructed within-set `x1` batch gives the aggregate polynomial's evaluation as the
`x1` power sum of its represented member polynomials. -/
theorem deployedX1Aggregate_eval
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (x4Batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (x1Batch : AlgebraicPowerBatch urs (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)
      (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) ch.x1)
    (node : Fp) :
    (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch x4Batch
        ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩).eval node =
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        ch.x1 ^ (m : Nat) * (coeffsToPoly (x1Batch.coeffs m)).eval node := by
  rw [deployedAlgebraicSetColumns, coeffsToPoly_eval]
  calc
    commitGen (evalVector urs.k node)
        (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) =
      commitGen (evalVector urs.k node)
        (∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          ch.x1 ^ (m : Nat) • x1Batch.coeffs m) :=
        congrArg (commitGen (evalVector urs.k node)) x1Batch.reconstruct
    _ = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        ch.x1 ^ (m : Nat) * (coeffsToPoly (x1Batch.coeffs m)).eval node := by
      rw [commitGen_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [commitGen_smul_left, <- coeffsToPoly_eval, smul_eq_mul]

omit [Module Fp G] in
/-- At a routed node, the deployed set interpolant is exactly the `x1` power sum of the member
claimed values stored in the proof string. -/
theorem deployedSetInterpolant_eval_eq_memberPowerSum
    [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (hql : ∀ qc ∈ deployedSetQueries vk instanceCommitment ps ch i,
      qc.2.length = ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length) :
    (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch
        ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩).eval
          ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] =
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        ch.x1 ^ (m : Nat) *
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
            (idx : Nat) 0 := by
  rw [deployedAlgebraicSetInterpolants,
    deployedSetsForEval_reverse_getD_reflect vk instanceCommitment ps ch hi]
  have hnd := deployedSetsForEval_getD_nodup vk instanceCommitment ps ch hi
  rw [lagrangePoly_eval_node (List.nodup_iff_injective_getElem.mp hnd) idx,
    deployedSetsForEval_getD_evals vk instanceCommitment ps ch hi,
    <- deployedSetsForEval_getD_points vk instanceCommitment ps ch hi,
    compressSet_snd_getD ch.x1 (deployedSetQueries vk instanceCommitment ps ch i) (.point 0, [])
      idx.isLt hql,
    <- Fin.sum_univ_eq_sum_range]

/-- A good single `x1` challenge separates the represented members of a deployed set.  This is
the value-side companion of `deployedX1AlgebraicBatchWithSourceOrRelation`; no accepting `x1` rewinds are
used. -/
theorem deployedMemberNodeBinding_of_good_x1
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (x4Batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (x1Batch : AlgebraicPowerBatch urs (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)
      (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) ch.x1)
    (hql : ∀ qc ∈ deployedSetQueries vk instanceCommitment ps ch i,
      qc.2.length = ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
    (haggregate :
      (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch x4Batch
          ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩).eval
            ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] =
        (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch
          ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩).eval
            ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx])
    (hgood : ch.x1 ∉ szBadSet
      (memberBindingErrorPolynomial
        (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
          coeffsToPoly (x1Batch.coeffs m))
        (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
            (idx : Nat) 0)
        ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx])) :
    forall m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
      (coeffsToPoly (x1Batch.coeffs m)).eval
          ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
          (idx : Nat) 0 := by
  let node := ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]
  have hmembers := deployedX1Aggregate_eval urs hk vk instanceCommitment ps ch x4Batch i hi x1Batch node
  have hclaimed := deployedSetInterpolant_eval_eq_memberPowerSum vk instanceCommitment ps ch i hi hql idx
  have hagg :
      (∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        ch.x1 ^ (m : Nat) * (coeffsToPoly (x1Batch.coeffs m)).eval node) =
        ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          ch.x1 ^ (m : Nat) *
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (idx : Nat) 0 := by
    rw [<- hmembers, haggregate, hclaimed]
  exact memberBinding_of_good_x1
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length => coeffsToPoly (x1Batch.coeffs m))
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD (idx : Nat) 0)
    node ch.x1 hagg hgood

/-! ## End-to-end deterministic value chain -/

/-- The deployed rewind-free value chain for one member at one routed node.  Starting from the
`x4` column values supplied by the recursive IPA/AGM batch, good `x3`, `x2`, and `x1` challenges
yield the member's claimed value.  The theorem contains no accepting rewind family. -/
theorem deployedMemberNodeBinding_of_good_challenges
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (x4Batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : ∀ j,
      commitGen (evalVector urs.k ch.x3) (x4Batch.coeffs j) = x4BatchEvals vk instanceCommitment ps ch j)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (x1Batch : AlgebraicPowerBatch urs (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)
      (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) ch.x1)
    (hql : ∀ qc ∈ deployedSetQueries vk instanceCommitment ps ch i,
      qc.2.length = ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)
    (hnode3 : ∀ j : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      (vanishingProd (deployedAlgebraicSetPoints vk instanceCommitment ps ch j)).eval ch.x3 ≠ 0)
    (hgood3 : ch.x3 ∉ szBadSet (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch x4Batch))
    (hgood2 : ch.x2 ∉ szBadSet
      (nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
        (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
        (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch x4Batch)
        (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch)
        ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]))
    (hgood1 : ch.x1 ∉ szBadSet
      (memberBindingErrorPolynomial
        (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
          coeffsToPoly (x1Batch.coeffs m))
        (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
            (idx : Nat) 0)
        ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx])) :
    ∀ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
      (coeffsToPoly (x1Batch.coeffs m)).eval
          ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
          (idx : Nat) 0 := by
  let pos : Fin (deployedX4PairCount vk instanceCommitment ps ch) :=
    ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
  let node := ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]
  have hnodeSet : node ∈ deployedAlgebraicSetPoints vk instanceCommitment ps ch pos := by
    have hmem : node ∈ deployedSetPts vk instanceCommitment ps ch i := by
      rw [<- deployedSetsForEval_getD_toFinset vk instanceCommitment ps ch hi]
      exact List.mem_toFinset.mpr (List.get_mem _ idx)
    have hreflect : deployedX4PairCount vk instanceCommitment ps ch - 1 -
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - i) = i := by omega
    simpa only [deployedAlgebraicSetPoints, pos, hreflect] using hmem
  have hid := deployedClearedQuotientIdentity_of_good_x3
    urs hk vk instanceCommitment ps ch x4Batch hvalues hnode3 hgood3
  have haggregate := deployedAggregateNodeBinding_of_good_x2
    urs hk vk instanceCommitment ps ch x4Batch hid pos hnodeSet hgood2
  exact deployedMemberNodeBinding_of_good_x1
    urs hk vk instanceCommitment ps ch x4Batch i hi x1Batch hql idx haggregate hgood1

end Zcash.Snark
