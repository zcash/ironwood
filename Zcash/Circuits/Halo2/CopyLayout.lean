import Clean.Halo2.Keygen.Layout
import Zcash.Arithmetic

/-! # Column layout and constant allocation for the copy compiler -/

namespace Halo2.Layout

open Zcash

/-- V1 constant allocations in the legacy copy-list tuple order. Values remain
field-valued in Clean; only this permutation-copy adapter reads their canonical `Fp.val`. -/
def constantCopyEntries (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (ℕ × ℕ × ℕ) :=
  (FloorPlanner.V1.constantAssignments ops (cs.constants.map (·.index))).map
    fun (value, column, row) => (value.val, column, row)

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem Fp) : List Halo2.Layout.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

/-- Translating the keygen permutation columns back to Clean columns is lossless. -/
theorem permColsOf_map_toAny (cs : ConstraintSystem Fp) :
    (permColsOf cs).map Halo2.Layout.ColRef.toAny =
      cs.permutationColumns := by
  rw [permColsOf, List.map_map]
  induction cs.permutationColumns with
  | nil => rfl
  | cons column rest ih =>
      simp only [List.map_cons]
      rw [ih]
      rcases column with ⟨kind, index⟩
      cases kind <;> rfl

end Halo2.Layout
