import Zcash.Common.Hash.Blake2bSimd.Guts
import Zcash.Common.Hash.Blake2b

/-!
# `blake2b_simd`'s shared helpers agree with Ironwood's BLAKE2b

The constants and helpers in `Guts.lean` are the same as their counterparts in
`Common/Hash/Blake2b.lean`: the counter halves of a byte count are `counterLow` and `counterHigh`.
The module also proves that `wordFromLeBytes` undoes splitting a word into its little-endian
bytes, which the AVX2 proof uses for its byte shuffles.
-/

namespace Zcash.Common.Blake2bSimd

/-- The low counter word of a byte count `t` is `counterLow t`. -/
theorem countLow_ofNat (t : ℕ) : countLow (BitVec.ofNat 128 t) = Blake2b.counterLow t := by
  apply UInt64.toBitVec_inj.mp
  simp [countLow, Blake2b.counterLow]
  rfl

/-- The high counter word of a byte count `t` is `counterHigh t`, for every `t`: both are bits 64
to 127 of `t`. -/
theorem countHigh_ofNat (t : ℕ) : countHigh (BitVec.ofNat 128 t) = Blake2b.counterHigh t := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp [countHigh, Blake2b.counterHigh]
  rw [Nat.shiftRight_eq_div_pow]; omega

/-- `wordFromLeBytes` unfolded: the bytes shifted in from the most significant. -/
theorem wordFromLeBytes_def (v : Vector UInt8 8) :
    wordFromLeBytes v =
      ((((((((0 : UInt64) <<< 8 ||| v[7].toUInt64) <<< 8 ||| v[6].toUInt64) <<< 8 |||
        v[5].toUInt64) <<< 8 ||| v[4].toUInt64) <<< 8 ||| v[3].toUInt64) <<< 8 |||
        v[2].toUInt64) <<< 8 ||| v[1].toUInt64) <<< 8 ||| v[0].toUInt64 := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => rfl

/-- `a <<< n ||| b` is a sum when `b` fits below bit `n`. -/
theorem or_shift_eq (a b : UInt64) (n : ℕ) (hn : n < 64) (hb : b.toNat < 2 ^ n) :
    (a <<< n.toUInt64 ||| b).toNat = a.toNat * 2 ^ n % 2 ^ 64 + b.toNat := by
  have hn' : (n.toUInt64).toNat % 64 = n := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hn', Nat.shiftLeft_eq]
  have hsplit : 2 ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, Nat.mul_mod_mul_right, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb]

/-- Putting back the low byte of `y` under `y >>> 8` gives `y`. -/
theorem byte_step (y : UInt64) : (y >>> 8) <<< 8 ||| y.toUInt8.toUInt64 = y := by
  apply UInt64.toNat_inj.mp
  rw [show (8 : UInt64) = (8 : ℕ).toUInt64 from rfl]
  rw [or_shift_eq _ _ 8 (by omega) (by simp; omega)]
  have := UInt64.toNat_lt y
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt8, UInt8.toNat_toUInt64,
    Nat.shiftRight_eq_div_pow, show (Nat.toUInt64 8).toNat % 64 = 8 from rfl]
  omega

/-- Shifting right by `8k` bits and then by 8 more is shifting by `8(k + 1)`. -/
theorem shiftRight_8 (x : UInt64) (k : ℕ) (hk : k < 7) :
    (x >>> (8 * k).toUInt64) >>> 8 = x >>> (8 * (k + 1)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', show (8 : UInt64).toNat % 64 = 8 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * (k + 1) < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * k < 64),
    Nat.mod_eq_of_lt (by omega : 8 * (k + 1) < 64),
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * (k + 1) = 8 * k + 8 by omega]

/-- `wordFromLeBytes` of a word's eight little-endian bytes is the word: the most significant byte
first, then `byte_step` puts back one byte at a time. -/
theorem wordFromLeBytes_leBytes (x : UInt64) :
    wordFromLeBytes (Vector.ofFn fun k : Fin 8 => (x >>> (8 * k.val).toUInt64).toUInt8) = x := by
  have base : (0 : UInt64) <<< 8 ||| (x >>> (8 * 7 : ℕ).toUInt64).toUInt8.toUInt64 =
      x >>> (8 * 7 : ℕ).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [show (8 : UInt64) = (8 : ℕ).toUInt64 from rfl]
    rw [or_shift_eq _ _ 8 (by omega) (by simp; omega)]
    have := UInt64.toNat_lt x
    simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt8, UInt8.toNat_toUInt64,
      Nat.shiftRight_eq_div_pow, show (Nat.toUInt64 (8 * 7)).toNat % 64 = 56 from rfl,
      UInt64.toNat_zero, Nat.zero_mul, Nat.zero_mod, Nat.zero_add]
    omega
  rw [wordFromLeBytes_def]
  simp only [Vector.getElem_ofFn]
  rw [base, ← shiftRight_8 x 6 (by omega), byte_step, ← shiftRight_8 x 5 (by omega), byte_step,
    ← shiftRight_8 x 4 (by omega), byte_step, ← shiftRight_8 x 3 (by omega), byte_step,
    ← shiftRight_8 x 2 (by omega), byte_step, ← shiftRight_8 x 1 (by omega), byte_step,
    ← shiftRight_8 x 0 (by omega), byte_step]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, show (Nat.toUInt64 (8 * 0)).toNat % 64 = 0 from rfl,
    Nat.shiftRight_zero]

/-- Eight zero bytes read as the zero word. -/
theorem wordFromLeBytes_zero : wordFromLeBytes (Vector.ofFn fun _ : Fin 8 => 0) = 0 := rfl

end Zcash.Common.Blake2bSimd
