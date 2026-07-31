import Zcash.Snark.Soundness.AGM.DeployedMultiopen

/-!
# AGM unbatching for deployed within-set `x₁` compression

After the `x₄` algebraic batch exposes a represented point-set aggregate, this file identifies
that aggregate with the exact `x₁` power batch of the query commitments routed to the set.  As at
`x₄`, equality reconstructs the member coordinates and any representation mismatch is an
explicit augmented-basis relation; no accepting `x₁` rewinds are used.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- These deployed grouping definitions occur inside index types.  Sealing them prevents elaboration
-- from normalizing the complete fingerprint assembly while checking a `Fin` coercion.
attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments

/-- The actual query commitments routed by the deployed fingerprint to point set `i`. -/
def deployedSetMemberCommitments [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : Nat) :
    Fin (deployedSetQueries vk instanceCommitment ps ch i).length → G :=
  fun j => ((deployedSetQueries vk instanceCommitment ps ch i).getD (j : Nat) (.point 0, [])).1.eval
    ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩

theorem deployedSetMemberCommitments_apply [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : Nat)
    (j : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) :
    deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i j =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (j : Nat) (.point 0, [])).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := rfl

attribute [local irreducible] deployedSetMemberCommitments

/-- Provenance-preserving form of the deployed `x1` unbatch.  Its successful branch retains the
equality between the batch columns and the online member coordinates. -/
def deployedX1AlgebraicBatchWithSourceOrRelation
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (x4Batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (members : AlgebraicColumnRepresentations urs
      (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)) :
    AlgebraicPowerBatchWithSource urs members
        (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
        (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
        (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
        ch.x1 ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let pos : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) :=
    ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
  have haggregate : commit urs (x4Batch.coeffs pos) + x4Batch.uComp pos • urs.u +
      x4Batch.wComp pos • urs.w =
        ∑ j : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          ch.x1 ^ (j : Nat) •
            deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i j := by
    have hpos : (pos : Nat) < deployedX4PairCount vk instanceCommitment ps ch := by
      dsimp [pos]
      omega
    have hqs : i < (deployedX4Qs vk instanceCommitment ps ch).length := by
      have hle : deployedX4PairCount vk instanceCommitment ps ch ≤
          (deployedX4Qs vk instanceCommitment ps ch).length := by
        rw [deployedX4PairCount_eq]
        simp only [deployedX4Pairs, List.length_zip]
        exact min_le_left _ _
      omega
    calc
      commit urs (x4Batch.coeffs pos) + x4Batch.uComp pos • urs.u +
            x4Batch.wComp pos • urs.w = x4BatchCommitments urs hk vk instanceCommitment ps ch pos :=
        x4Batch.commitment pos
      _ = ((deployedX4Qs vk instanceCommitment ps ch).getD i (Msm.zero shape.k Fp G)).eval
            ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
        rw [x4BatchCommitments_getD urs hk vk instanceCommitment ps ch (j := pos) hpos]
        congr 2
        dsimp [pos]
        omega
      _ = ∑ j : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
            ch.x1 ^ (j : Nat) •
              deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i j := by
        rw [deployedX4Qs_getD_eval (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch hqs]
        rw [← Fin.sum_univ_eq_sum_range (fun j =>
          ch.x1 ^ j •
            ((deployedSetQueries vk instanceCommitment ps ch i).getD j (.point 0, [])).1.eval
            ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)]
        exact Finset.sum_congr rfl fun j _ => by
          rw [deployedSetMemberCommitments_apply]
  exact algebraicPowerBatchWithSourceOrRelation members (x4Batch.coeffs pos)
    (x4Batch.uComp pos) (x4Batch.wComp pos) ch.x1 haggregate

end Zcash.Snark
