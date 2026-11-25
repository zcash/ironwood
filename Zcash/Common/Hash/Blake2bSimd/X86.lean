import Zcash.Common.Hash.Blake2bSimd.Guts

/-!
# The x86 intrinsics `blake2b_simd`'s AVX2 compression calls

`blake2b_simd` 1.0.5's one-stream AVX2 code (`compress_block` and `compress1_loop`,
`src/avx2.rs:153-510`) is written with `core::arch` intrinsics on 256-bit vectors, mostly through
helpers earlier in the file (`src/avx2.rs:17-150`). This module writes down each intrinsic that
code reaches, directly or through those helpers, as Rust's `core::arch` defines it, so the
transcription of `avx2.rs` can call them as ordinary functions. The helpers only the many-stream
code uses (`eq`, `and`, `negate_and`, `set1`) and their intrinsics are left out.

A 256-bit vector is its four 64-bit lanes, lane 0 the lowest (`M256i`). Rust reads the same bits as
eight 32-bit or thirty-two 8-bit lanes when an intrinsic works at that width; `lanes32`, `lanes8`
and their inverses are those views, little-endian as on x86. Seven of the intrinsics are
`simd_shuffle!` selections, so `shuffle` writes that once: element `i` of the result is element
`idx[i]` of the two inputs placed end to end.

These definitions are trusted: nothing here is proved about the hardware. Each computes what its
Rust definition computes; where the Lean takes another route, its docstring says why. The
instruction named in each docstring is the one the Rust's `assert_instr` test expects.

## Rust reference

`core::arch` as shipped with Rust 1.98.0, in `library/stdarch/crates/core_arch/src/x86/`:

* `avx2.rs:83-85` `_mm256_add_epi64`, `avx2.rs:3870-3872` `_mm256_xor_si256`,
  `avx2.rs:2314-2316` `_mm256_or_si256`;
* `avx2.rs:3284-3293` `_mm256_srli_epi64`, `avx2.rs:2865-2874` `_mm256_slli_epi64`;
* `avx2.rs:3854-3859` `_mm256_unpacklo_epi64`, `avx2.rs:3814-3819` `_mm256_unpackhi_epi64`;
* `avx2.rs:357-378` `_mm256_blend_epi32`, `avx2.rs:2635-2654` `_mm256_shuffle_epi32`,
  `avx2.rs:2477-2493` `_mm256_permute4x64_epi64`, `avx2.rs:181-252` `_mm256_alignr_epi8`;
* `avx2.rs:589-594` `_mm256_broadcastsi128_si256`;
* `avx.rs:2740-2742` `_mm256_setr_epi64x`, `avx.rs:1723-1731` `_mm256_loadu_si256`,
  `avx.rs:1742-1744` `_mm256_storeu_si256`, `sse2.rs:1339-1347` `_mm_loadu_si128`.
-/

namespace Zcash.Common.Blake2bSimd.X86

/-- `__m256i`: 256 bits as four 64-bit lanes, lane 0 the lowest. -/
abbrev M256i := Vector UInt64 4

/-- `__m128i`: 128 bits as two 64-bit lanes, lane 0 the lowest. -/
abbrev M128i := Vector UInt64 2

/-- `simd_shuffle!(a, b, idx)`: element `i` is element `idx[i]` of `a` followed by `b`. -/
def shuffle {α : Type} {n m : ℕ} (a b : Vector α n) (idx : Vector (Fin (n + n)) m) :
    Vector α m :=
  Vector.ofFn fun i => (a ++ b)[idx[i]]

/-- `as_i32x8`: the eight 32-bit lanes of the same bits, lane `2w` the low half of 64-bit lane
`w`. -/
def lanes32 (a : M256i) : Vector UInt32 8 :=
  Vector.ofFn fun i : Fin 8 => (a[i.val / 2] >>> (32 * (i.val % 2)).toUInt64).toUInt32

/-- The 256 bits whose 32-bit lanes are `v`: the inverse of `lanes32`. -/
def ofLanes32 (v : Vector UInt32 8) : M256i :=
  Vector.ofFn fun w : Fin 4 => v[2 * w.val].toUInt64 ||| v[2 * w.val + 1].toUInt64 <<< 32

/-- `as_i8x32`: the thirty-two bytes of the same bits, byte `8w + k` holding bits `8k` to
`8k + 7` of 64-bit lane `w`. -/
def lanes8 (a : M256i) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 => (a[i.val / 8] >>> (8 * (i.val % 8)).toUInt64).toUInt8

/-- The 256 bits whose bytes are `v`, each lane the little-endian word of its eight bytes: the
inverse of `lanes8`. -/
def ofLanes8 (v : Vector UInt8 32) : M256i :=
  Vector.ofFn fun w : Fin 4 =>
    wordFromLeBytes (Vector.ofFn fun k : Fin 8 => v[8 * w.val + k.val]'(by omega))

/-- `_mm256_add_epi64` (`vpaddq`): lane by lane, addition wrapping modulo `2^64`. -/
def mm256AddEpi64 (a b : M256i) : M256i := Vector.zipWith (· + ·) a b

/-- `_mm256_xor_si256` (`vxorps`): bitwise exclusive or. -/
def mm256XorSi256 (a b : M256i) : M256i := Vector.zipWith (· ^^^ ·) a b

/-- `_mm256_or_si256` (`vorps`): bitwise or. Rust computes it on the 32-bit view; on the same
bits, that is the bitwise or of the 64-bit lanes. -/
def mm256OrSi256 (a b : M256i) : M256i := Vector.zipWith (· ||| ·) a b

/-- `_mm256_srli_epi64::<IMM8>` (`vpsrlq`): each lane shifted right by `IMM8` bits, shifting in
zeros, so all zero once `IMM8` reaches 64. `IMM8` is below 256
(`static_assert_uimm_bits!(IMM8, 8)`). -/
def mm256SrliEpi64 (imm8 : Fin 256) (a : M256i) : M256i :=
  if imm8.val ≥ 64 then Vector.replicate 4 0 else a.map (· >>> imm8.val.toUInt64)

/-- `_mm256_slli_epi64::<IMM8>` (`vpsllq`): each lane shifted left by `IMM8` bits, shifting in
zeros, so all zero once `IMM8` reaches 64. -/
def mm256SlliEpi64 (imm8 : Fin 256) (a : M256i) : M256i :=
  if imm8.val ≥ 64 then Vector.replicate 4 0 else a.map (· <<< imm8.val.toUInt64)

/-- `_mm256_unpacklo_epi64` (`vunpcklpd`): in each 128-bit half, the low lane of `a` then the low
lane of `b`. -/
def mm256UnpackloEpi64 (a b : M256i) : M256i := shuffle a b #v[0, 4, 2, 6]

/-- `_mm256_unpackhi_epi64` (`vunpckhpd`): in each 128-bit half, the high lane of `a` then the
high lane of `b`. -/
def mm256UnpackhiEpi64 (a b : M256i) : M256i := shuffle a b #v[1, 5, 3, 7]

/-- `_mm256_blend_epi32::<IMM8>` (`vblendps`): 32-bit lane `j` from `b` where bit `j` of `IMM8` is
set, otherwise from `a`. Rust indexes a four-entry table by each pair of bits; so does this. -/
def mm256BlendEpi32 (imm8 : Fin 256) (a b : M256i) : M256i :=
  let pair (k : ℕ) : Fin 4 := ⟨(imm8.val >>> k) % 4, Nat.mod_lt _ (by decide)⟩
  let pick (t : Vector (Fin 16) 4) (k : ℕ) : Fin 16 := t[pair k]
  ofLanes32 (shuffle (lanes32 a) (lanes32 b)
    #v[pick #v[0, 8, 0, 8] 0, pick #v[1, 1, 9, 9] 0, pick #v[2, 10, 2, 10] 2,
       pick #v[3, 3, 11, 11] 2, pick #v[4, 12, 4, 12] 4, pick #v[5, 5, 13, 13] 4,
       pick #v[6, 14, 6, 14] 6, pick #v[7, 7, 15, 15] 6])

/-- `_mm256_shuffle_epi32::<MASK>` (`vshufps`): in each 128-bit half, its 32-bit lane `j`
(`j < 4`) is the lane of that half that bits `2j` and `2j + 1` of `MASK` select. -/
def mm256ShuffleEpi32 (mask : Fin 256) (a : M256i) : M256i :=
  let lo (k : ℕ) : Fin 16 := ⟨(mask.val >>> k) % 4, by omega⟩
  let hi (k : ℕ) : Fin 16 := ⟨(mask.val >>> k) % 4 + 4, by omega⟩
  ofLanes32 (shuffle (lanes32 a) (lanes32 a) #v[lo 0, lo 2, lo 4, lo 6, hi 0, hi 2, hi 4, hi 6])

/-- `_mm256_permute4x64_epi64::<IMM8>` (`vpermpd`): lane `j` is the lane that bits `2j` and
`2j + 1` of `IMM8` select. -/
def mm256Permute4x64Epi64 (imm8 : Fin 256) (a : M256i) : M256i :=
  let sel (k : ℕ) : Fin 8 := ⟨(imm8.val >>> k) % 4, by omega⟩
  shuffle a (Vector.replicate 4 0) #v[sel 0, sel 2, sel 4, sel 6]

/-- The byte `_mm256_alignr_epi8` takes for result byte `i` from `b` followed by `a`, for a shift
of `shift` bytes within each 16-byte half (Rust's `mask`). -/
def alignrMask (shift : ℕ) (i : Fin 32) : Fin 64 :=
  if i.val % 16 < 16 - shift % 16 then ⟨i.val + shift % 16, by omega⟩
  else ⟨i.val + 16 + shift % 16, by omega⟩

/-- `_mm256_alignr_epi8::<IMM8>` (`vpalignr`): in each 128-bit half, the 32 bytes of `a`'s half
above `b`'s half, shifted right by `IMM8` bytes, low 16 bytes kept. A shift of 32 or more gives
zero, a shift of exactly 16 gives `a`, and a shift above 16 shifts zeros in from above `a`. -/
def mm256AlignrEpi8 (imm8 : Fin 256) (a b : M256i) : M256i :=
  if imm8.val ≥ 32 then Vector.replicate 4 0 else
  let (a, b) := if imm8.val > 16 then (Vector.replicate 4 0, a) else (a, b)
  if imm8.val = 16 then a else
  ofLanes8 (shuffle (lanes8 b) (lanes8 a) (Vector.ofFn (alignrMask imm8.val)))

/-- `_mm256_broadcastsi128_si256`: `a` in both 128-bit halves. -/
def mm256Broadcastsi128Si256 (a : M128i) : M256i := shuffle a (Vector.replicate 2 0) #v[0, 1, 0, 1]

/-- `_mm256_setr_epi64x(e0, e1, e2, e3)`: lane `j` is `e_j`. Rust takes `i64`; `blake2b_simd`'s
`set4` (`src/avx2.rs:65-67`) passes `u64` values cast with `as i64`, which keeps the bits, so the
lanes here are `UInt64`. -/
def mm256SetrEpi64x (e0 e1 e2 e3 : UInt64) : M256i := #v[e0, e1, e2, e3]

/-- `_mm256_loadu_si256(p)` (`vmovups`): the 32 bytes at `p`. `blake2b_simd`'s `loadu`
(`src/avx2.rs:17-20`) loads only `[u64; 4]` arrays, whose bytes, read back as four little-endian
64-bit lanes, are the array. -/
def mm256LoaduSi256 (p : Vector UInt64 4) : M256i := p

/-- `_mm256_storeu_si256(p, a)` (`vmovups`): `a`'s 32 bytes written to `p`. `blake2b_simd`'s
`storeu` (`src/avx2.rs:23-26`) stores only into `[u64; 4]` arrays, which then hold `a`'s lanes. -/
def mm256StoreuSi256 (a : M256i) : Vector UInt64 4 := a

/-- `_mm_loadu_si128(p)` (`movups`): the 16 bytes at `p` as two little-endian 64-bit lanes.
`blake2b_simd`'s `loadu_128` (`src/avx2.rs:29-31`) loads only `[u8; 16]` arrays. -/
def mmLoaduSi128 (p : Vector UInt8 16) : M128i :=
  Vector.ofFn fun w : Fin 2 =>
    wordFromLeBytes (Vector.ofFn fun k : Fin 8 => p[8 * w.val + k.val]'(by omega))

end Zcash.Common.Blake2bSimd.X86
