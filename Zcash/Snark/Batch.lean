import Mathlib
import Zcash.Snark.Field

/-!
# The batch random-linear-combination soundness bound

Batch verification combines the per-proof MSM evaluations `gᵢ` with fresh random scalars and accepts
only if the combination is the group identity. Soundness: if any `gᵢ ≠ 0` (some proof's fingerprint
is nonzero), the random combination is the identity only with negligible probability.

The atomic fact is `smul_eq_zero_iff_of_ne_zero`: a random scalar annihilates a nonzero group element
only when it is `0`. `batch_rlc_card_le` amplifies it to the `N`-fold linear combination `∑ rᵢ • gᵢ`:
if some `gⱼ ≠ 0`, the combination vanishes for at most `p ^ (N-1)` of the `p ^ N` choices of
randomness — a `1 / p` fraction, negligible for `p ≈ 2²⁵⁴`. (halo2's deployed combiner folds with
iterated scaling, a degree-`(N-1)` variant bounded by `(N-1) / p` through the same atomic fact; we
model the linear-combination form, whose `1 / p` is the cleaner statement of the same soundness.)

Requires `[NoZeroSMulDivisors Fp G]` — the prime-order property of the verifier group `E_q`.
-/

namespace Zcash.Snark

open Finset

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A uniformly random scalar annihilates a nonzero group element only at `0` — the atomic fact behind
batch verification: a random multiplier cannot hide a nonzero MSM. -/
theorem smul_eq_zero_iff_of_ne_zero [NoZeroSMulDivisors Fp G] {g : G} (hg : g ≠ 0) {r : Fp} :
    r • g = 0 ↔ r = 0 := by
  simp [smul_eq_zero, hg]

/-- **Batch random-linear-combination bound.** If a batched MSM evaluation `g j` is nonzero, the
random linear combination `∑ rᵢ • gᵢ` vanishes for at most `p ^ (N-1)` of the `p ^ N` choices of
randomness — a `1 / p` fraction. So batch verification hides a nonzero MSM with probability `≤ 1 / p`,
negligible for `p ≈ 2²⁵⁴`. -/
theorem batch_rlc_card_le [DecidableEq G] [NoZeroSMulDivisors Fp G] {N : ℕ} (g : Fin N → G)
    (j : Fin N) (hj : g j ≠ 0) :
    (univ.filter fun r : Fin N → Fp => ∑ i, r i • g i = 0).card ≤ scalarFieldOrder ^ (N - 1) := by
  have hinj : Function.Injective
      (fun (r : {r : Fin N → Fp // ∑ i, r i • g i = 0}) (i : {i : Fin N // i ≠ j}) => r.1 i.1) := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ heq
    have hother : ∀ i : Fin N, i ≠ j → r i = r' i := fun i hi => congrFun heq ⟨i, hi⟩
    have hsum : ∑ i, (r i - r' i) • g i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hr, hr', sub_self]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [hother i hi, sub_self, zero_smul])
        (fun h => absurd (mem_univ j) h)] at hsum
    have hjeq : r j = r' j := by
      rcases smul_eq_zero.mp hsum with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hj
    apply Subtype.ext
    funext i
    by_cases hi : i = j
    · subst hi; exact hjeq
    · exact hother i hi
  have hcard : Fintype.card ({i : Fin N // i ≠ j} → Fp) = scalarFieldOrder ^ (N - 1) := by
    rw [Fintype.card_fun, card_Fp]
    congr 1
    simp [Fintype.card_subtype_compl]
  calc (univ.filter fun r : Fin N → Fp => ∑ i, r i • g i = 0).card
      = Fintype.card {r : Fin N → Fp // ∑ i, r i • g i = 0} := (Fintype.card_subtype _).symm
    _ ≤ Fintype.card ({i : Fin N // i ≠ j} → Fp) := Fintype.card_le_of_injective _ hinj
    _ = scalarFieldOrder ^ (N - 1) := hcard

end Zcash.Snark
