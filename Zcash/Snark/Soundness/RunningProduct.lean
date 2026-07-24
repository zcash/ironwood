import Mathlib
import Zcash.Snark.Soundness.GrandProduct

/-!
# Telescoping the running product

Both the permutation and the lookup argument work the same way. The prover commits to a running
product `z`, and the verifier checks a one-row recurrence: `z` at the next row times one product of
factors equals `z` at this row times another. The verifier also pins `z` at the first row to `1` and
at the last row to `0` or `1`.

Multiplying the recurrence across the rows cancels every interior `z`, leaving the two whole-column
products related by the boundary values. That turns the verifier's per-row checks into the product
identity `GrandProduct` reads as a multiset identity.

If `z` ends at `0`, one factor `v + β·name + γ` must vanish — a collision on the challenges. So each
result here is *either* the product identity *or* an explicit vanishing factor, and the caller
prices the second branch.
-/

namespace Zcash.Snark

open Finset

variable {F : Type*}

/-- **Telescoping.** A one-row recurrence multiplied across `m` rows: every interior `z` cancels,
leaving the boundary values times the two products. -/
theorem telescope_running_product [CommRing F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i) :
    z m * ∏ i ∈ range m, B i = z 0 * ∏ i ∈ range m, A i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := hrec m (Nat.lt_succ_self m)
      calc z (m + 1) * ∏ i ∈ range (m + 1), B i
          = (z (m + 1) * B m) * ∏ i ∈ range m, B i := by
            rw [prod_range_succ]; ring
        _ = (z m * A m) * ∏ i ∈ range m, B i := by rw [hstep]
        _ = (z m * ∏ i ∈ range m, B i) * A m := by ring
        _ = (z 0 * ∏ i ∈ range m, A i) * A m := by
            rw [ih fun i hi => hrec i (Nat.lt_succ_of_lt hi)]
        _ = z 0 * ∏ i ∈ range (m + 1), A i := by rw [prod_range_succ]; ring

/-- **The product identity the kernel consumes.** With `z` pinned to `1` at the first row and to `0`
or `1` at the last, telescoping gives *either* the two products are equal *or* one factor on the
right vanished — the case `z` ended at `0`. -/
theorem prod_eq_or_factor_eq_zero [Field F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i)
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1) :
    (∏ i ∈ range m, B i = ∏ i ∈ range m, A i) ∨ ∃ i ∈ range m, A i = 0 := by
  have htel := telescope_running_product z A B hrec
  rw [hz0, one_mul] at htel
  rcases hzm with hzm | hzm
  · rw [hzm, zero_mul] at htel
    exact Or.inr (prod_eq_zero_iff.mp htel.symm)
  · exact Or.inl (by rw [hzm, one_mul] at htel; exact htel)

/-- Telescoping with the last-row value known to be `1`: the two products agree outright. This is
the branch the honest prover is in. -/
theorem prod_eq_of_running_product [CommRing F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i) (hz0 : z 0 = 1) (hzm : z m = 1) :
    ∏ i ∈ range m, B i = ∏ i ∈ range m, A i := by
  have htel := telescope_running_product z A B hrec
  rwa [hz0, hzm, one_mul, one_mul] at htel

/-! ## Rows of several columns

Each row's factor is itself a product over that row's columns, so the telescoped identity is a
product over `row × column` pairs. Rewriting it as a product over one index set is what lets
`prod_pair_inj` read it as a multiset of `(value, name)` pairs. -/

/-- A row-wise product of column factors, flattened to a single product over `row × column`. -/
theorem prod_range_prod_range [CommRing F] (f : ℕ → ℕ → F) (m k : ℕ) :
    (∏ i ∈ range m, ∏ j ∈ range k, f i j) = ∏ p ∈ range m ×ˢ range k, f p.1 p.2 := by
  rw [prod_product]

/-- **The grand product of a running-product argument.** Each row's recurrence multiplies the row's
column factors; across all rows the result is a single product over every cell, related by the
boundary values. Either the two whole-table products agree, or some right-hand cell factor
vanished. -/
theorem grandProduct_eq_or_cell_eq_zero [Field F] (z : ℕ → F) (a b : ℕ → ℕ → F) {m k : ℕ}
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, b i j = z i * ∏ j ∈ range k, a i j)
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1) :
    (∏ p ∈ range m ×ˢ range k, b p.1 p.2 = ∏ p ∈ range m ×ˢ range k, a p.1 p.2)
      ∨ ∃ p ∈ range m ×ˢ range k, a p.1 p.2 = 0 := by
  rcases prod_eq_or_factor_eq_zero z (fun i => ∏ j ∈ range k, a i j)
      (fun i => ∏ j ∈ range k, b i j) hrec hz0 hzm with h | ⟨i, hi, hzero⟩
  · exact Or.inl (by rw [← prod_range_prod_range, ← prod_range_prod_range]; exact h)
  · obtain ⟨j, hj, hj0⟩ := prod_eq_zero_iff.mp hzero
    exact Or.inr ⟨(i, j), mem_product.mpr ⟨hi, hj⟩, hj0⟩


end Zcash.Snark
