import Zcash.Common.Hash.Blake2bSimd.Loop
import Zcash.Common.Hash.Blake2bSimd.X86

/-!
# `blake2b_simd`'s AVX2 compression function

`blake2b_simd` 1.0.5 compresses one block with the AVX2 `compress_block` (`src/avx2.rs`) when AVX2
is available. Where the portable code mixes the sixteen working words one column or diagonal at a
time, it keeps them in four 256-bit rows `a`, `b`, `c`, `d` and mixes all four columns at once:
`g1` and `g2` are the two halves of the mixing function, and `diagonalize` rotates the rows so the
same code then mixes the diagonals. Before each `g1` or `g2` call, two shuffles of the eight
message vectors and a blend make the message vector it takes.

The twelve rounds share one shape and differ only in those shuffles, so `rounds` lists them as a
table read from the Rust (`src/avx2.rs:206-444`).

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/avx2.rs:70-74` `_MM_SHUFFLE!`, `src/avx2.rs:86-103` `rot32`, `rot24`, `rot16`, `rot63`;
* `src/avx2.rs:106-128` `g1` and `g2`, `src/avx2.rs:135-150` `diagonalize` and `undiagonalize`;
* `src/avx2.rs:153-454` `compress_block`, `src/avx2.rs:457-510` `compress1_loop`.
-/

namespace Zcash.Common.Blake2bSimd.Avx2

open X86

/-- `_MM_SHUFFLE!(z, y, x, w)`: the immediate `(z << 6) | (y << 4) | (x << 2) | w`, four two-bit
fields. The fields do not overlap, so the `|`s are sums. -/
def mmShuffle (z y x w : Fin 4) : Fin 256 :=
  ⟨z.val * 64 + y.val * 16 + x.val * 4 + w.val, by omega⟩

/-- `rot32`, `rot24`, `rot16`, `rot63`: each 64-bit lane rotated right by `n`, as an `or` of a
right and a left shift. -/
def rot (n : Fin 64) (x : M256i) : M256i :=
  mm256OrSi256 (mm256SrliEpi64 ⟨n.val, by omega⟩ x)
    (mm256SlliEpi64 ⟨64 - n.val, by omega⟩ x)

/-- The four rows `a`, `b`, `c`, `d` of the working vector. -/
abbrev Rows := M256i × M256i × M256i × M256i

/-- `g1`: the first half of the mixing function on all four columns, with message vector `m`. -/
def g1 (s : Rows) (m : M256i) : Rows :=
  let (a, b, c, d) := s
  let a := mm256AddEpi64 a m
  let a := mm256AddEpi64 a b
  let d := mm256XorSi256 d a
  let d := rot 32 d
  let c := mm256AddEpi64 c d
  let b := mm256XorSi256 b c
  let b := rot 24 b
  (a, b, c, d)

/-- `g2`: the second half of the mixing function on all four columns, with message vector `m`. -/
def g2 (s : Rows) (m : M256i) : Rows :=
  let (a, b, c, d) := s
  let a := mm256AddEpi64 a m
  let a := mm256AddEpi64 a b
  let d := mm256XorSi256 d a
  let d := rot 16 d
  let c := mm256AddEpi64 c d
  let b := mm256XorSi256 b c
  let b := rot 63 b
  (a, b, c, d)

/-- `diagonalize`: rotate rows `a`, `d`, `c` by one, two and three lanes, so the diagonals of the
working vector line up as columns. `b` stays where it is, and the message shuffles allow for that
(`src/avx2.rs:131-133`). -/
def diagonalize (s : Rows) : Rows :=
  let (a, b, c, d) := s
  let a := mm256Permute4x64Epi64 (mmShuffle 2 1 0 3) a
  let d := mm256Permute4x64Epi64 (mmShuffle 1 0 3 2) d
  let c := mm256Permute4x64Epi64 (mmShuffle 0 3 2 1) c
  (a, b, c, d)

/-- `undiagonalize`: the rotations that undo `diagonalize`. -/
def undiagonalize (s : Rows) : Rows :=
  let (a, b, c, d) := s
  let a := mm256Permute4x64Epi64 (mmShuffle 0 3 2 1) a
  let d := mm256Permute4x64Epi64 (mmShuffle 1 0 3 2) d
  let c := mm256Permute4x64Epi64 (mmShuffle 2 1 0 3) c
  (a, b, c, d)

/-- One shuffle that builds `t0` or `t1` from the message vectors `m0` to `m7`. -/
inductive Shuffle where
  /-- `_mm256_unpacklo_epi64(mX, mY)`. -/
  | lo (x y : Fin 8)
  /-- `_mm256_unpackhi_epi64(mX, mY)`. -/
  | hi (x y : Fin 8)
  /-- `_mm256_alignr_epi8(mX, mY, 8)`. -/
  | alignr (x y : Fin 8)
  /-- `_mm256_blend_epi32(mX, mY, 0x33)`. -/
  | blend (x y : Fin 8)
  /-- `_mm256_shuffle_epi32(mX, _MM_SHUFFLE!(1, 0, 3, 2))`. -/
  | swap (x : Fin 8)

/-- The vector a `Shuffle` makes from the message vectors `m`. -/
def Shuffle.apply (m : Vector M256i 8) : Shuffle → M256i
  | .lo x y => mm256UnpackloEpi64 m[x] m[y]
  | .hi x y => mm256UnpackhiEpi64 m[x] m[y]
  | .alignr x y => mm256AlignrEpi8 8 m[x] m[y]
  | .blend x y => mm256BlendEpi32 0x33 m[x] m[y]
  | .swap x => mm256ShuffleEpi32 (mmShuffle 1 0 3 2) m[x]

open Shuffle in
/-- The shuffles of the twelve rounds, read from `src/avx2.rs:206-444`. Round `k`, counting from 0,
is lines `206 + 20k` to `224 + 20k`: four groups of `t0 = …; t1 = …;`, each followed by
`b0 = _mm256_blend_epi32(t0, t1, 0xF0);` and a call of `g1` or `g2`. -/
def rounds : Vector (Vector (Shuffle × Shuffle) 4) 12 :=
  #v[#v[(lo 0 1, lo 2 3), (hi 0 1, hi 2 3), (lo 7 4, lo 5 6), (hi 7 4, hi 5 6)],
     #v[(lo 7 2, hi 4 6), (lo 5 4, alignr 3 7), (hi 2 0, blend 5 0), (alignr 6 1, blend 3 1)],
     #v[(alignr 6 5, hi 2 7), (lo 4 0, blend 6 1), (alignr 5 4, hi 1 3), (lo 2 7, blend 0 3)],
     #v[(hi 3 1, hi 6 5), (hi 4 0, lo 6 7), (alignr 1 7, swap 2), (lo 4 3, lo 5 0)],
     #v[(hi 4 2, lo 1 5), (blend 3 0, blend 7 2), (alignr 7 1, alignr 3 5), (hi 6 0, lo 6 4)],
     #v[(lo 1 3, lo 0 4), (lo 6 5, hi 5 1), (alignr 2 0, hi 3 7), (hi 4 6, alignr 7 2)],
     #v[(blend 0 6, lo 7 2), (hi 2 7, alignr 5 6), (lo 4 0, blend 4 3), (hi 5 3, swap 1)],
     #v[(hi 6 3, blend 1 6), (alignr 7 5, hi 0 4), (blend 2 1, alignr 4 7), (lo 5 0, lo 2 3)],
     #v[(lo 3 7, alignr 0 5), (hi 7 4, alignr 4 1), (lo 5 6, hi 6 0), (alignr 1 2, alignr 2 3)],
     #v[(lo 5 4, hi 3 0), (lo 1 2, blend 2 3), (hi 6 7, hi 4 1), (blend 5 0, lo 7 6)],
     #v[(lo 0 1, lo 2 3), (hi 0 1, hi 2 3), (lo 7 4, lo 5 6), (hi 7 4, hi 5 6)],
     #v[(lo 7 2, hi 4 6), (lo 5 4, alignr 3 7), (hi 2 0, blend 5 0), (alignr 6 1, blend 3 1)]]

/-- `b0 = _mm256_blend_epi32(t0, t1, 0xF0)`: the low half of `t0` and the high half of `t1`, the
message vector one `g1` or `g2` call takes. -/
def b0 (m : Vector M256i 8) (t : Shuffle × Shuffle) : M256i :=
  mm256BlendEpi32 0xF0 (t.1.apply m) (t.2.apply m)

/-- One round: `g1`, `g2`, `diagonalize`, `g1`, `g2`, `undiagonalize`, the four `g` calls taking
the message vectors the round's four shuffle pairs make. -/
def round (m : Vector M256i 8) (r : Vector (Shuffle × Shuffle) 4) (s : Rows) : Rows :=
  let s := g1 s (b0 m r[0])
  let s := g2 s (b0 m r[1])
  let s := diagonalize s
  let s := g1 s (b0 m r[2])
  let s := g2 s (b0 m r[3])
  undiagonalize s

/-- `compress_block`: one block into the state `words`. Rows `a` and `b` are the state's two
halves, `c` is the low half of `IV`, and `d` is the high half of `IV` xored with the counter's two
halves and the two flags (`set4`). Each of the eight message vectors is a 16-byte piece of the block
in both 128-bit halves. After the twelve rounds the new state is `a ^ c` and `b ^ d`, each xored
with the row it started as. The Rust's `iv0` and `iv1` (`src/avx2.rs:200-201`) hold those starting
rows, the state, not `IV`. -/
def compressBlock (block : Vector UInt8 128) (words : Vector Word 8) (count : Count)
    (lastBlock lastNode : Word) : Vector Word 8 :=
  let a := mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => words[i.val])
  let b := mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => words[i.val + 4])
  let c := mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => IV[i.val])
  let flags := mm256SetrEpi64x (countLow count) (countHigh count) lastBlock lastNode
  let d := mm256XorSi256 (mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => IV[i.val + 4])) flags
  let m : Vector M256i 8 := Vector.ofFn fun k : Fin 8 =>
    mm256Broadcastsi128Si256 (mmLoaduSi128 (Vector.ofFn fun i : Fin 16 =>
      block[16 * k.val + i.val]'(by omega)))
  let (a', b', c', d') := rounds.toList.foldl (fun s r => round m r s) (a, b, c, d)
  let a' := mm256XorSi256 (mm256XorSi256 a' c') a
  let b' := mm256XorSi256 (mm256XorSi256 b' d') b
  mm256StoreuSi256 a' ++ mm256StoreuSi256 b'

/-- `compress1_loop`: the compression loop (`compress1Loop`) with the AVX2 `compress_block`. The
Rust is `unsafe` and compiled for AVX2 (`#[target_feature(enable = "avx2")]`), so it may run only
on a CPU with AVX2; its full-block read is an unchecked pointer cast (`src/avx2.rs:491`), which
the loop's offsets keep inside the input. -/
def compress1Loop (input : List UInt8) (words : Vector Word 8) (count : Count)
    (lastNode : LastNode) (finalize : Finalize) (stride : Stride) : Vector Word 8 :=
  Blake2bSimd.compress1Loop compressBlock input words count lastNode finalize stride

end Zcash.Common.Blake2bSimd.Avx2
