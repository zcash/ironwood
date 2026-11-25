import Zcash.Common.Hash.Blake2bSimd.Guts

/-!
# `blake2b_simd`'s portable compression function

`blake2b_simd` 1.0.5 compresses one 128-byte block into the eight state words with the portable
`compress_block` (`src/portable.rs`) unless it has selected AVX2. It sets up
the sixteen-word working vector from the state, `IV`, the byte counter and the two flags, reads the
block as sixteen little-endian words, runs twelve rounds of the mixing function `g`, and folds the
working vector back into the state.

Rust's indices into fixed-size arrays become `Fin` values here, so every index is in range by its
type: the state positions `g` mixes and the entries of `SIGMA` are `Fin 16`, and the round number is
`Fin 12`.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/portable.rs:13-22` `g`, `src/portable.rs:27-42` `round`;
* `src/portable.rs:45-149` `compress_block`.
-/

namespace Zcash.Common.Blake2bSimd

/-- `u64::rotate_right(n)` for `0 < n < 64`, which is Ironwood's `Blake2b.rotr`. `g` rotates by
32, 24, 16 and 63. -/
def rotateRight (x : Word) (n : UInt64) : Word := Blake2b.rotr x n

namespace Portable

/-- `g`: the mixing function. It mixes four words of the working vector `v`, at positions `a`,
`b`, `c`, `d`, with two message words `x` and `y`, by additions modulo `2^64`, xors and rotations
by 32, 24, 16 and 63. Each step reads the words as the previous step left them. -/
def g (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d (rotateRight (v[d] ^^^ v[a]) 32)
  let v := v.set c (v[c] + v[d])
  let v := v.set b (rotateRight (v[b] ^^^ v[c]) 24)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d (rotateRight (v[d] ^^^ v[a]) 16)
  let v := v.set c (v[c] + v[d])
  v.set b (rotateRight (v[b] ^^^ v[c]) 63)

/-- `round`: round `r`, eight applications of `g`, first on the four columns of `v` seen as a
4 × 4 matrix and then on its four diagonals, with the message words `SIGMA[r]` selects. -/
def round (r : Fin 12) (m : Vector Word 16) (v : Vector Word 16) : Vector Word 16 :=
  let s := SIGMA[r]
  let v := g v 0 4 8 12 m[s[0]] m[s[1]]
  let v := g v 1 5 9 13 m[s[2]] m[s[3]]
  let v := g v 2 6 10 14 m[s[4]] m[s[5]]
  let v := g v 3 7 11 15 m[s[6]] m[s[7]]
  let v := g v 0 5 10 15 m[s[8]] m[s[9]]
  let v := g v 1 6 11 12 m[s[10]] m[s[11]]
  let v := g v 2 7 8 13 m[s[12]] m[s[13]]
  g v 3 4 9 14 m[s[14]] m[s[15]]

/-- `compress_block`: one block into the state `words`. The working vector is the state, then `IV`
with the counter's two halves and the two flags xored into its last four words; the message words
are the block's sixteen little-endian words; after the twelve rounds, state word `i` is xored with
working words `i` and `i + 8`. -/
def compressBlock (block : Vector UInt8 128) (words : Vector Word 8) (count : Count)
    (lastBlock lastNode : Word) : Vector Word 8 :=
  let v : Vector Word 16 :=
    #v[words[0], words[1], words[2], words[3], words[4], words[5], words[6], words[7],
       IV[0], IV[1], IV[2], IV[3], IV[4] ^^^ countLow count, IV[5] ^^^ countHigh count,
       IV[6] ^^^ lastBlock, IV[7] ^^^ lastNode]
  let m : Vector Word 16 := Vector.ofFn fun i : Fin 16 =>
    wordFromLeBytes (Vector.ofFn fun k : Fin 8 => block[8 * i.val + k.val]'(by omega))
  let v := round 0 m v
  let v := round 1 m v
  let v := round 2 m v
  let v := round 3 m v
  let v := round 4 m v
  let v := round 5 m v
  let v := round 6 m v
  let v := round 7 m v
  let v := round 8 m v
  let v := round 9 m v
  let v := round 10 m v
  let v := round 11 m v
  Vector.ofFn fun i : Fin 8 => words[i] ^^^ (v[i.val] ^^^ v[i.val + 8])

end Portable

end Zcash.Common.Blake2bSimd
