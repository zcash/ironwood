import CompElliptic.Curves.Pasta
import Zcash.Arithmetic.Field

/-!
# Evaluation-domain scalars (pasta `Fp` constants and facts)

halo2's domain data as pure functions: binary exponentiation (`powFast`), the size-`2^k`
domain root of unity `omegaOf` (CompElliptic's certified Pasta `ROOT_OF_UNITY` squared
down, `EvaluationDomain::new`), `Fp::DELTA`, and the domain facts (primitive-root, power
injectivity, size nonvanishing) derived from the certificate's order fact.
Moved out of `Zcash/Bridge` per the Clean-boundary architecture
(`Zcash/Circuits/Integration/clean-boundary.md`): these are verifier-native arithmetic
facts, not bridge plumbing.
-/

namespace Zcash.Arithmetic

/-- Binary exponentiation (`Monoid.npow`'s default recursion is linear — unusable for
exponents of order `p/2^k`). -/
def powFast (b : Fp) (n : ℕ) : Fp :=
  if n = 0 then 1
  else
    let r := powFast (b * b) (n / 2)
    if n % 2 = 1 then b * r else r
  decreasing_by omega

/-- Binary exponentiation agrees with the field's ordinary natural power. -/
theorem powFast_eq_pow (b : Fp) (n : ℕ) :
    powFast b n = b ^ n := by
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
      rw [powFast]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn]
        have hhalf : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by norm_num)
        rw [ih (n / 2) hhalf]
        by_cases hodd : n % 2 = 1
        · rw [if_pos hodd]
          have hn_split : n = 2 * (n / 2) + 1 := by omega
          calc
            b * (b * b) ^ (n / 2) =
                b * (b ^ 2) ^ (n / 2) := by rw [pow_two]
            _ = b ^ (2 * (n / 2) + 1) := by
              rw [pow_add, pow_mul, pow_one]
              ring
            _ = b ^ n := congrArg (b ^ ·) hn_split.symm
        · have heven : n % 2 = 0 := by omega
          rw [if_neg hodd]
          have hn_split : n = 2 * (n / 2) := by omega
          calc
            (b * b) ^ (n / 2) = (b ^ 2) ^ (n / 2) := by rw [pow_two]
            _ = b ^ (2 * (n / 2)) := by rw [pow_mul]
            _ = b ^ n := congrArg (b ^ ·) hn_split.symm

/-- pasta `Fp::ROOT_OF_UNITY = 5^((p−1)/2^32)` as a bare literal — pure data, so that
definitions built on the domain scalars do not pull CompElliptic's certificate (and its
native axiom) into their trusted base. `rootOfUnityFp_eq_certified` identifies it with the
certified constant definitionally. -/
def rootOfUnityFp : Fp :=
  0x2bce74deac30ebda362120830561f81aea322bf2b7bb7584bdad6fabd87ea32f

/-- The literal is CompElliptic's certified Pasta root, definitionally. -/
theorem rootOfUnityFp_eq_certified :
    rootOfUnityFp = CompElliptic.Fields.Pasta.pallasBase.rootOfUnity := rfl

/-- The size-`2^k` domain's root of unity: the Pasta root (`ROOT_OF_UNITY = 5^((p−1)/2^32)`,
pasta `Fp::GENERATOR = 5`) squared down `32 − k` times, exactly as `EvaluationDomain::new`
does — so `omega = 5^((p−1)/2^k)`. Its order is a theorem of CompElliptic's certificate via
`rootOfUnityFp_eq_certified`; agreement with the deployed key's omega is pinned by `VkMatch`
against the captured VK. -/
def omegaOf (k : ℕ) : Fp :=
  powFast rootOfUnityFp (2 ^ (32 - k))

/-- `omegaOf k` is a primitive size-`2^k` domain root for every supported exponent. -/
theorem omegaOf_isPrimitiveRoot (k : ℕ) (hk : k ≤ 32) :
    IsPrimitiveRoot (omegaOf k) (2 ^ k) := by
  have hroot :
      IsPrimitiveRoot
        CompElliptic.Fields.Pasta.pallasBase.rootOfUnity (2 ^ 32) :=
    IsPrimitiveRoot.iff_orderOf.mpr
      CompElliptic.Fields.Pasta.pallasBase.valid.rootOfUnity_order
  unfold omegaOf
  rw [rootOfUnityFp_eq_certified, powFast_eq_pow]
  apply IsPrimitiveRoot.pow (by positivity) hroot
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- Every point `omegaOf k ^ row` lies in the size-`2^k` evaluation domain. -/
theorem omegaOf_domain (k row : ℕ) (hk : k ≤ 32) :
    (omegaOf k ^ row) ^ (2 ^ k) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  rw [(omegaOf_isPrimitiveRoot k hk).pow_eq_one, one_pow]

/-- Distinct row indices below `2^k` name distinct evaluation-domain points. -/
theorem omegaOf_powers_injective (k : ℕ) (hk : k ≤ 32) :
    Function.Injective fun row : Fin (2 ^ k) => omegaOf k ^ (row : ℕ) := by
  intro left right heq
  apply Fin.ext
  exact (omegaOf_isPrimitiveRoot k hk).pow_inj left.isLt right.isLt heq

/-- The supported evaluation-domain size is nonzero when cast into `Fp`. -/
theorem domainSize_cast_ne_zero (k : ℕ) (hk : k ≤ 32) :
    ((2 ^ k : ℕ) : Fp) ≠ 0 := by
  intro hzero
  have hdiv : scalarFieldOrder ∣ 2 ^ k :=
    (ZMod.natCast_eq_zero_iff (2 ^ k) scalarFieldOrder).mp hzero
  apply Nat.not_dvd_of_pos_of_lt (by positivity) _ hdiv
  calc
    2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hk
    _ < scalarFieldOrder := by
      norm_num [scalarFieldOrder,
        CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- pasta `Fp::DELTA = GENERATOR^(2^S) = 5^(2^32)`. -/
def deltaFp : Fp := powFast 5 (2 ^ 32)


end Zcash.Arithmetic
