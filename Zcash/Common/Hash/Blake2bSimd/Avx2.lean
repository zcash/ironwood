import Zcash.Common.Hash.Blake2bSimd.X86

/-!
# `blake2b_simd`'s AVX2 compression function

`blake2b_simd` 1.0.5 compresses one block with the AVX2 `compress_block` (`src/avx2.rs`) when AVX2
is available. Where the portable code mixes the sixteen working words one column or diagonal at a
time, it keeps them in four 256-bit rows `a`, `b`, `c`, `d` and mixes all four columns at once:
`g1` and `g2` are the two halves of the mixing function, and `diagonalize` rotates the rows so the
same code then mixes the diagonals. This module transcribes those helpers.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/avx2.rs:70-74` `_MM_SHUFFLE!`, `src/avx2.rs:86-103` `rot32`, `rot24`, `rot16`, `rot63`;
* `src/avx2.rs:106-128` `g1` and `g2`, `src/avx2.rs:135-150` `diagonalize` and `undiagonalize`.
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

end Zcash.Common.Blake2bSimd.Avx2
