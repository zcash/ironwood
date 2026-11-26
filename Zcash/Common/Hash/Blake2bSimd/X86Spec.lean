import Zcash.Common.Hash.Blake2bSimd.X86
import Zcash.Common.Hash.Blake2bSimd.GutsSpec
import Mathlib.Tactic.IntervalCases

/-!
# The x86 shuffles `blake2b_simd` uses move whole 64-bit lanes

The intrinsic models in `X86.lean` work on the lane widths the instructions do: 32-bit lanes for
`_mm256_blend_epi32`, bytes for `_mm256_alignr_epi8`. For the immediates `blake2b_simd`'s AVX2
code passes, each one only moves whole 64-bit lanes, and this module states which: `blend33`,
`blendF0`, `alignr8`, `unpacklo`, `unpackhi`. The general facts behind them are that a 64-bit
lane split into 32-bit lanes or bytes and put back in order is unchanged (`ofLanes32_shuffle`,
`ofLanes8_shuffle`).
-/

namespace Zcash.Common.Blake2bSimd

open X86

/-- A word is its low 32 bits or'd with its high 32 bits shifted back up. -/
theorem halves32 (x : UInt64) :
    x.toUInt32.toUInt64 ||| (x >>> 32).toUInt32.toUInt64 <<< 32 = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.or_comm]
  rw [show (32 : UInt64) = (32 : ℕ).toUInt64 from rfl,
    or_shift_eq _ _ 32 (by omega) (by simp; omega)]
  have := UInt64.toNat_lt x
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt32.toNat_toUInt64,
    Nat.shiftRight_eq_div_pow, show (Nat.toUInt64 32).toNat % 64 = 32 from rfl]
  omega

/-- A 64-bit lane rebuilt from the two 32-bit lanes `lanes32` splits it into is unchanged. -/
theorem halves32_lanes (x : UInt64) :
    (x >>> (32 * (0 % 2) : ℕ).toUInt64).toUInt32.toUInt64 |||
      (x >>> (32 * (1 % 2) : ℕ).toUInt64).toUInt32.toUInt64 <<< 32 = x := by
  have h0 : x >>> (32 * (0 % 2) : ℕ).toUInt64 = x := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, show (Nat.toUInt64 (32 * (0 % 2))).toNat % 64 = 0 from rfl,
      Nat.shiftRight_zero]
  rw [h0, show (32 * (1 % 2) : ℕ).toUInt64 = 32 from rfl]
  exact halves32 x

/-- Lane `i` of `shuffle a b idx` is lane `idx[i]` of `a ++ b`. -/
theorem shuffle_getElem {α : Type} {n m : ℕ} (a b : Vector α n) (idx : Vector (Fin (n + n)) m)
    (i : ℕ) (hi : i < m) : (shuffle a b idx)[i] = (a ++ b)[(idx[i]).val] := by
  simp [shuffle]

/-- `lanes32` lane `i`: 32-bit half `i % 2` of 64-bit lane `i / 2`. -/
theorem lanes32_getElem (a : M256i) (i : ℕ) (hi : i < 8) :
    (lanes32 a)[i] = (a[i / 2] >>> (32 * (i % 2) : ℕ).toUInt64).toUInt32 := by
  simp [lanes32]

/-- `ofLanes32` lane `w`: 32-bit lanes `2w` and `2w + 1`, low first. -/
theorem ofLanes32_getElem (v : Vector UInt32 8) (w : ℕ) (hw : w < 4) :
    (ofLanes32 v)[w] = v[2 * w].toUInt64 ||| v[2 * w + 1].toUInt64 <<< 32 := by
  simp [ofLanes32]

/-- A lane of `a ++ b` below `n` is a lane of `a`. -/
theorem append_getElem_lt {α : Type} {n : ℕ} (a b : Vector α n) (i : ℕ) (hi : i < n) :
    (a ++ b)[i] = a[i] := Vector.getElem_append_left hi

/-- A lane of `a ++ b` from `n` on is a lane of `b`. -/
theorem append_getElem_ge {α : Type} {n : ℕ} (a b : Vector α n) (i : ℕ) (h : i < n + n)
    (hi : n ≤ i) : (a ++ b)[i] = b[i - n] := Vector.getElem_append_right h hi

/-- A lane of `ofLanes32 (shuffle (lanes32 a) (lanes32 b) idx)` whose two 32-bit halves `idx`
takes, in order, from one 64-bit lane `s` of `a ++ b` is that lane. -/
theorem ofLanes32_shuffle (a b : M256i) (idx : Vector (Fin (8 + 8)) 8) (w : ℕ) (hw : w < 4)
    (s : ℕ) (hs : s < 8) (h0 : (idx[2 * w]).val = 2 * s) (h1 : (idx[2 * w + 1]).val = 2 * s + 1) :
    (ofLanes32 (shuffle (lanes32 a) (lanes32 b) idx))[w] = (a ++ b)[s] := by
  rw [ofLanes32_getElem _ _ hw, shuffle_getElem, shuffle_getElem]
  simp only [h0, h1]
  by_cases hs4 : s < 4
  · rw [append_getElem_lt _ _ _ (by omega), append_getElem_lt _ _ _ (by omega),
      append_getElem_lt _ _ _ hs4, lanes32_getElem _ _ (by omega), lanes32_getElem _ _ (by omega)]
    simp only [show 2 * s / 2 = s by omega, show (2 * s + 1) / 2 = s by omega,
      show 2 * s % 2 = 0 % 2 by omega, show (2 * s + 1) % 2 = 1 % 2 by omega]
    exact halves32_lanes a[s]
  · rw [append_getElem_ge _ _ _ (by omega) (by omega),
      append_getElem_ge _ _ _ (by omega) (by omega),
      append_getElem_ge _ _ _ (by omega) (by omega), lanes32_getElem _ _ (by omega),
      lanes32_getElem _ _ (by omega)]
    simp only [show (2 * s - 8) / 2 = s - 4 by omega, show (2 * s + 1 - 8) / 2 = s - 4 by omega,
      show (2 * s - 8) % 2 = 0 % 2 by omega, show (2 * s + 1 - 8) % 2 = 1 % 2 by omega]
    exact halves32_lanes b[s - 4]

/-- `_mm256_blend_epi32(a, b, 0x33)` takes 64-bit lanes 0 and 2 from `b`, 1 and 3 from `a`. -/
theorem blend33 (a b : M256i) : mm256BlendEpi32 0x33 a b = #v[b[0], a[1], b[2], a[3]] := by
  have : mm256BlendEpi32 0x33 a b =
      ofLanes32 (shuffle (lanes32 a) (lanes32 b) #v[8, 9, 2, 3, 12, 13, 6, 7]) := rfl
  rw [this]
  apply Vector.ext
  intro w hw
  interval_cases w
  · rw [ofLanes32_shuffle a b _ 0 (by omega) 4 (by omega) rfl rfl]
    exact append_getElem_ge a b 4 (by omega) (by omega)
  · rw [ofLanes32_shuffle a b _ 1 (by omega) 1 (by omega) rfl rfl]
    exact append_getElem_lt a b 1 (by omega)
  · rw [ofLanes32_shuffle a b _ 2 (by omega) 6 (by omega) rfl rfl]
    exact append_getElem_ge a b 6 (by omega) (by omega)
  · rw [ofLanes32_shuffle a b _ 3 (by omega) 3 (by omega) rfl rfl]
    exact append_getElem_lt a b 3 (by omega)

/-- `_mm256_blend_epi32(a, b, 0xF0)` takes the low two 64-bit lanes from `a`, the high two from
`b`. -/
theorem blendF0 (a b : M256i) : mm256BlendEpi32 0xF0 a b = #v[a[0], a[1], b[2], b[3]] := by
  have : mm256BlendEpi32 0xF0 a b =
      ofLanes32 (shuffle (lanes32 a) (lanes32 b) #v[0, 1, 2, 3, 12, 13, 14, 15]) := rfl
  rw [this]
  apply Vector.ext
  intro w hw
  interval_cases w
  · rw [ofLanes32_shuffle a b _ 0 (by omega) 0 (by omega) rfl rfl]
    exact append_getElem_lt a b 0 (by omega)
  · rw [ofLanes32_shuffle a b _ 1 (by omega) 1 (by omega) rfl rfl]
    exact append_getElem_lt a b 1 (by omega)
  · rw [ofLanes32_shuffle a b _ 2 (by omega) 6 (by omega) rfl rfl]
    exact append_getElem_ge a b 6 (by omega) (by omega)
  · rw [ofLanes32_shuffle a b _ 3 (by omega) 7 (by omega) rfl rfl]
    exact append_getElem_ge a b 7 (by omega) (by omega)

/-- `lanes8` lane `i`: byte `i % 8` of 64-bit lane `i / 8`. -/
theorem lanes8_getElem (a : M256i) (i : ℕ) (hi : i < 32) :
    (lanes8 a)[i] = (a[i / 8] >>> (8 * (i % 8) : ℕ).toUInt64).toUInt8 := by
  simp [lanes8]

/-- `ofLanes8` lane `w`: bytes `8w` to `8w + 7`, read little-endian. -/
theorem ofLanes8_getElem (v : Vector UInt8 32) (w : ℕ) (hw : w < 4) :
    (ofLanes8 v)[w] =
      wordFromLeBytes (Vector.ofFn fun k : Fin 8 => v[8 * w + k.val]'(by omega)) := by
  simp [ofLanes8]

/-- A lane of `ofLanes8 (shuffle (lanes8 a) (lanes8 b) idx)` whose eight bytes `idx` takes, in
order, from one 64-bit lane `s` of `a ++ b` is that lane. -/
theorem ofLanes8_shuffle (a b : M256i) (idx : Vector (Fin (32 + 32)) 32) (w : ℕ) (hw : w < 4)
    (s : ℕ) (hs : s < 8) (h : ∀ k (hk : k < 8), (idx[8 * w + k]'(by omega)).val = 8 * s + k) :
    (ofLanes8 (shuffle (lanes8 a) (lanes8 b) idx))[w] = (a ++ b)[s] := by
  rw [ofLanes8_getElem _ _ hw]
  have hv : (Vector.ofFn fun k : Fin 8 =>
        (shuffle (lanes8 a) (lanes8 b) idx)[8 * w + k.val]'(by omega)) =
      Vector.ofFn fun k : Fin 8 => ((a ++ b)[s] >>> (8 * k.val : ℕ).toUInt64).toUInt8 := by
    apply Vector.ext
    intro k hk
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn, shuffle_getElem]
    simp only [h k hk]
    by_cases hs4 : s < 4
    · rw [append_getElem_lt _ _ _ (by omega), append_getElem_lt _ _ _ hs4,
        lanes8_getElem _ _ (by omega)]
      simp only [show (8 * s + k) / 8 = s by omega, show (8 * s + k) % 8 = k by omega]
    · rw [append_getElem_ge _ _ _ (by omega) (by omega),
      append_getElem_ge _ _ _ (by omega) (by omega),
        lanes8_getElem _ _ (by omega)]
      simp only [show (8 * s + k - 32) / 8 = s - 4 by omega, show (8 * s + k - 32) % 8 = k by omega]
  rw [hv, wordFromLeBytes_leBytes]

/-- `_mm256_alignr_epi8(a, b, 8)` gives, in each 128-bit half, `b`'s high lane then `a`'s low
lane. -/
theorem alignr8 (a b : M256i) : mm256AlignrEpi8 8 a b = #v[b[1], a[0], b[3], a[2]] := by
  have : mm256AlignrEpi8 8 a b =
      ofLanes8 (shuffle (lanes8 b) (lanes8 a) (Vector.ofFn (alignrMask 8))) := rfl
  rw [this]
  apply Vector.ext
  intro w hw
  interval_cases w
  · rw [ofLanes8_shuffle b a _ 0 (by omega) 1 (by omega)
      (by intro k hk; interval_cases k <;> rfl)]
    exact append_getElem_lt b a 1 (by omega)
  · rw [ofLanes8_shuffle b a _ 1 (by omega) 4 (by omega)
      (by intro k hk; interval_cases k <;> rfl)]
    exact append_getElem_ge b a 4 (by omega) (by omega)
  · rw [ofLanes8_shuffle b a _ 2 (by omega) 3 (by omega)
      (by intro k hk; interval_cases k <;> rfl)]
    exact append_getElem_lt b a 3 (by omega)
  · rw [ofLanes8_shuffle b a _ 3 (by omega) 6 (by omega)
      (by intro k hk; interval_cases k <;> rfl)]
    exact append_getElem_ge b a 6 (by omega) (by omega)

/-- `_mm256_unpacklo_epi64(a, b)` interleaves the low lanes of each 128-bit half. -/
theorem unpacklo (a b : M256i) : mm256UnpackloEpi64 a b = #v[a[0], b[0], a[2], b[2]] := by
  apply Vector.ext
  intro w hw
  rw [mm256UnpackloEpi64, shuffle_getElem]
  interval_cases w
  · exact append_getElem_lt a b 0 (by omega)
  · exact append_getElem_ge a b 4 (by omega) (by omega)
  · exact append_getElem_lt a b 2 (by omega)
  · exact append_getElem_ge a b 6 (by omega) (by omega)

/-- `_mm256_unpackhi_epi64(a, b)` interleaves the high lanes of each 128-bit half. -/
theorem unpackhi (a b : M256i) : mm256UnpackhiEpi64 a b = #v[a[1], b[1], a[3], b[3]] := by
  apply Vector.ext
  intro w hw
  rw [mm256UnpackhiEpi64, shuffle_getElem]
  interval_cases w
  · exact append_getElem_lt a b 1 (by omega)
  · exact append_getElem_ge a b 5 (by omega) (by omega)
  · exact append_getElem_lt a b 3 (by omega)
  · exact append_getElem_ge a b 7 (by omega) (by omega)

end Zcash.Common.Blake2bSimd
