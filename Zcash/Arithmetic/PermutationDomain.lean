import Zcash.Arithmetic.Domain
import Mathlib.Tactic.NormNum.Parity

/-! # Pasta permutation-column cosets -/

namespace Zcash.Arithmetic

/-- `deltaFp = 5^(2^32)` lies in the odd-order factor of `Fpˣ`. -/
theorem deltaFp_pow_pastaOddFactor :
    deltaFp ^ deltaFpOrder = 1 := by
  exact deltaFp_isPrimitiveRoot.pow_eq_one

theorem pastaOddFactor_coprime_domain (k : ℕ) :
    Nat.Coprime (2 ^ k) deltaFpOrder := by
  apply Nat.Coprime.pow_left
  exact Odd.coprime_two_left (by
    norm_num [deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

/-- Every supported prefix of the permutation-column names `deltaFp^j`
occupies distinct cosets of a supported Pasta evaluation subgroup. -/
theorem deltaFp_domainCosets
    {k n : ℕ} (hk : k ≤ 32) (hn : n ≤ deltaFpOrder)
    (j j' : Fin n) (t : ℕ)
    (h :
      deltaFp ^ (j : ℕ) =
        omegaOf k ^ t * deltaFp ^ (j' : ℕ)) :
    j = j' := by
  have hj :
      (deltaFp ^ (j : ℕ)) ^ deltaFpOrder = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hj' :
      (deltaFp ^ (j' : ℕ)) ^ deltaFpOrder = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hpow := congrArg (fun x : Fp => x ^ deltaFpOrder) h
  dsimp only at hpow
  rw [hj, mul_pow, hj', _root_.mul_one] at hpow
  have htMul : omegaOf k ^ (t * deltaFpOrder) = 1 := by
    rw [pow_mul]
    exact hpow.symm
  have hprimitive : IsPrimitiveRoot (omegaOf k) (2 ^ k) :=
    omegaOf_isPrimitiveRoot k hk
  have hdvdMul : 2 ^ k ∣ t * deltaFpOrder :=
    (hprimitive.pow_eq_one_iff_dvd _).mp htMul
  have hdvd : 2 ^ k ∣ t :=
    (pastaOddFactor_coprime_domain k).dvd_of_dvd_mul_right hdvdMul
  have ht : omegaOf k ^ t = 1 :=
    (hprimitive.pow_eq_one_iff_dvd _).mpr hdvd
  rw [ht, _root_.one_mul] at h
  exact deltaFp_powers_injective n hn h

end Zcash.Arithmetic
