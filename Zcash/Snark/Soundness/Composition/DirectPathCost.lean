import Zcash.Snark.Soundness.AGM.DirectX4Columns
import Zcash.Snark.Soundness.Composition.ActionBudget

/-!
# Total-cost model for the direct-coordinate postprocessing

`DirectX4Columns` makes the direct decode an executable program over the covered representations
rather than a classical choice.  This module supplies the runtime half of that claim: a
field-independent polynomial bound on the arithmetic the decode performs, in the modeled-count
style of `deployedConstraintRelationFinderCalls`.

Per `x₄` batch column, including the final `q′` column, the model charges one traversal of the
column's member list — each member paying a covered-source lookup of at most `sourceLen` steps, a
challenge-power update, a scalar multiply-add on each of the `2^k` generator coordinates, and the
`u`/`w` multiply-adds — plus one fold-and-compare over the column's `2^k + 2` coordinates.  Group
operations never touch this path, so field operations and data traversal are the whole cost.

The bounds are stated at the actual per-run quantities (`deployedX4PairCount`,
`deployedSetQueries`) and discharged shape-polynomially by `deployedX4PairCount_le_numPointSets`
and `deployedSetQueries_length_le`.  No term depends on `|F|`, and the captured-shape corollaries
in `Fixtures.MaxShapeBounds` evaluate the bound to a count linear in the action count.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G]
variable {shape : Shape}

/-- Modeled cost of assembling and checking one `x₄` batch column: `memberCount` member visits at
`sourceLen + 2·2^k + 5` field operations and data steps each, plus the column's aggregate fold
over its `2^k + 2` coordinates. -/
def directColumnDecodeOps (memberCount sourceLen k : ℕ) : ℕ :=
  memberCount * (sourceLen + 2 * 2 ^ k + 5) + (2 ^ k + 2)

/-- Modeled total cost of one direct-coordinate decode: the per-column model summed over every
`x₄` batch column, each traversing exactly the member list the decode itself reads.  `sourceLen`
is the length of the covered assembly source the member lookups scan. -/
def deployedDirectDecodeOps
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (sourceLen : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (deployedX4PairCount vk instanceCommitment ps ch + 1),
    directColumnDecodeOps
      (deployedSetQueries vk instanceCommitment ps ch
        (x4ColumnSetIndex vk instanceCommitment ps ch j)).length
      sourceLen shape.k

/-- **The direct-coordinate decode has a field-independent polynomial total cost.**  Every column
traverses at most `queryBudget shape` members, and there are at most `numPointSets + 1` columns —
both bounds are consequences of the deployed query assembly alone, with no spread premise,
adversary-dependent quantity, or `|F|` term. -/
theorem deployedDirectDecodeOps_le
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (sourceLen : ℕ) :
    deployedDirectDecodeOps vk instanceCommitment ps ch sourceLen ≤
      (shape.numPointSets + 1) *
        (queryBudget shape * (sourceLen + 2 * 2 ^ shape.k + 5) + (2 ^ shape.k + 2)) := by
  refine le_trans (Finset.sum_le_card_nsmul _ _
    (queryBudget shape * (sourceLen + 2 * 2 ^ shape.k + 5) + (2 ^ shape.k + 2)) ?_) ?_
  · intro j _
    have h := deployedSetQueries_length_le vk instanceCommitment ps ch
      (x4ColumnSetIndex vk instanceCommitment ps ch j)
    unfold directColumnDecodeOps
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
  · rw [Finset.card_range, smul_eq_mul]
    exact Nat.mul_le_mul_right _
      (Nat.add_le_add_right
        (deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch) 1)

end Zcash.Snark
