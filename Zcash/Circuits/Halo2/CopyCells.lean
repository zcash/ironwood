import Clean.Halo2.Keygen.Layout

/-! # Bounded copy-table coordinates -/

namespace Zcash.Snark

/-- A flat permutation-table cell: a permutation column and a row. -/
abbrev FlatCell (numCols n : ℕ) := Fin numCols × Fin n

/-- The `(column, row)` pair the assembly arrays index by. -/
def FlatCell.pair {numCols n : ℕ} (c : FlatCell numCols n) : ℕ × ℕ :=
  ((c.1 : ℕ), (c.2 : ℕ))

theorem FlatCell.pair_injective {numCols n : ℕ} :
    Function.Injective (FlatCell.pair (numCols := numCols) (n := n)) := by
  intro c d h
  simp only [FlatCell.pair, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨Fin.ext h.1, Fin.ext h.2⟩

end Zcash.Snark
