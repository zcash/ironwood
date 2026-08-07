import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Splitting a power-of-two vector into halves

One IPA round halves a length-`2^{k+1}` vector. These are the two projections and their
reassembly, generic over the codomain so the same three definitions serve witness vectors
(`α = F`) and generator vectors (`α = G`).

* `loHalf` / `hiHalf` — the two halves of a length-`2^{k+1}` vector.
* `append` — reassembly, inverse to the pair of projections (`append_loHalf_hiHalf`).

The round folds built on top of these live with their consumers: `foldVec` in
`Soundness.InnerProduct` folds the witness by `u`, and `foldGens` in `Soundness.Consistency`
folds the generators by `u⁻¹`.
-/

namespace Zcash.Snark

private theorem two_pow_succ (k : ℕ) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [pow_succ, Nat.mul_two]

/-- The lower half of a length-`2^{k+1}` vector. Generic over the codomain `α`, so it halves both
witness vectors (`α = F`) and generator vectors (`α = G`). -/
def loHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => a ⟨i.val, by have h := i.isLt; have e := two_pow_succ k; omega⟩

/-- The upper half of a length-`2^{k+1}` vector. -/
def hiHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => a ⟨2 ^ k + i.val, by have h := i.isLt; have e := two_pow_succ k; omega⟩

/-- Reassemble a length-`2^{k+1}` vector from its two halves. -/
def append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : Fin (2 ^ (k + 1)) → α :=
  fun i => if h : i.val < 2 ^ k then lo ⟨i.val, h⟩
           else hi ⟨i.val - 2 ^ k, by have h2 := i.isLt; have e := two_pow_succ k; omega⟩

/-- Reassembling the two halves recovers the original vector. -/
theorem append_loHalf_hiHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) :
    append (loHalf a) (hiHalf a) = a := by
  funext i
  rcases lt_or_ge i.val (2 ^ k) with h | h
  · simp only [append, dif_pos h, loHalf]
  · simp only [append, dif_neg (not_lt.mpr h), hiHalf]
    refine congrArg a (Fin.ext ?_)
    show 2 ^ k + (i.val - 2 ^ k) = i.val
    omega

end Zcash.Snark
