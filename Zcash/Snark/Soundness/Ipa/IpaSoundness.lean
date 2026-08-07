import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Ipa.CommitFold
import Zcash.Snark.Soundness.Ipa.Halves

/-!
# Commitment-vector and batch algebra

Shared linearity lemmas for splitting commitment vectors and recovering coordinates from an
explicit power batch. The deployed soundness route performs straight-line AGM extraction and does
not construct a recursive ternary transcript tree.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Split a commitment over the lower and upper halves of its vectors. -/
theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- The lower half of an `append` is the lower part. -/
theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : loHalf (append lo hi) = lo := by
  funext i; simp only [loHalf, append, dif_pos i.isLt]

/-- The upper half of an `append` is the upper part. -/
theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1; apply Fin.ext; simp

/-- A commitment to `append a_lo a_hi` splits into commitments to both halves. -/
theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
    commitGen g (append a_lo a_hi) = commitGen (loHalf g) a_lo + commitGen (hiHalf g) a_hi := by
  rw [commitGen_split, loHalf_append, hiHalf_append]

/-- A length-`m` commitment is additive over a finite sum of witnesses. -/
theorem commitGen_sum {m : ℕ} (g : Fin m → G) {ι : Type*} (s : Finset ι) (f : ι → Fin m → F) :
    commitGen g (∑ k ∈ s, f k) = ∑ k ∈ s, commitGen g (f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [commitGen]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, commitGen_add_left, ih]

end Zcash.Snark
