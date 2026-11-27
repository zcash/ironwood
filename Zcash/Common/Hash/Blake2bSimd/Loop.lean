import Zcash.Common.Hash.Blake2bSimd.Guts

/-!
# `blake2b_simd`'s compression loop

`blake2b_simd` 1.0.5 compresses a whole input with `compress1_loop`, once in `src/portable.rs`
and once in `src/avx2.rs`. The two are the same loop apart from three things: the AVX2 one is
`unsafe`, they call different `compress_block`s, and they read a full block differently. The
portable loop slices with bounds checks (`src/portable.rs:182`); the AVX2 loop casts a pointer
without them (`src/avx2.rs:491`). Both read only bytes inside the input, so here they are one
definition, `compress1Loop`, taking the `compress_block` as an argument.

The loop compresses the input block by block. Each block before the last is a full 128 bytes of
input; the last, at `fin_offset`, comes from `final_block` and is the only one that can carry the
final flags.

Lean accepts the loop only with a proof that it stops. That proof keeps `offset` at a multiple of
the stride no greater than `fin_offset`, and the same facts show that every full block lies inside
the input, so the full-block read indexes the input with that proof. An out-of-bounds read, which
the AVX2 loop would not catch, cannot be written here.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/portable.rs:151-200` and `src/avx2.rs:457-510` `compress1_loop`.
-/

namespace Zcash.Common.Blake2bSimd

/-- The signature of a `compress_block`: one block, the state words, the count including this
block, and the last-block and last-node flag words, giving the new state words. -/
abbrev CompressBlockFn :=
  Vector UInt8 128 → Vector Word 8 → Count → Word → Word → Vector Word 8

/-- Every stride is at least one block. -/
theorem Stride.blockBytes_le_paddedBlockBytes (s : Stride) : BLOCKBYTES ≤ s.paddedBlockBytes := by
  cases s <;> simp [paddedBlockBytes, BLOCKBYTES]

/-- Two multiples of `s`, the first below the second, are at least `s` apart: the loop's next
offset does not pass `fin_offset`. -/
theorem add_le_of_dvd_of_lt {s a b : ℕ} (hab : a < b) (ha : s ∣ a) (hb : s ∣ b) :
    a + s ≤ b :=
  Nat.le_of_lt_add_of_dvd (Nat.add_lt_add_right hab s) (Nat.dvd_add ha (Nat.dvd_refl s)) hb

/-- The loop from `offset` on: the body of `compress1_loop`'s `loop`. At `fin_offset` it
compresses the final block with the final flags and stops; before it, it compresses the full
block at `offset` and moves on by one stride. The count grows by each block's input bytes,
wrapping modulo `2^128` (`wrapping_add`). -/
def compress1LoopFrom
    (compressBlock : CompressBlockFn)
    (input : List UInt8) (stride : Stride) (finOffset : ℕ) (finBlock : Vector UInt8 128)
    (finLen : ℕ) (finLastBlock finLastNode : Word)
    (hfinDvd : stride.paddedBlockBytes ∣ finOffset) (hfinLe : finOffset ≤ input.length - 1)
    (offset : ℕ) (hle : offset ≤ finOffset) (hdvd : stride.paddedBlockBytes ∣ offset)
    (words : Vector Word 8) (count : Count) : Vector Word 8 :=
  if hfin : offset = finOffset then
    compressBlock finBlock words (count + BitVec.ofNat 128 finLen) finLastBlock finLastNode
  else
    have hnext : offset + stride.paddedBlockBytes ≤ finOffset :=
      add_le_of_dvd_of_lt (Nat.lt_of_le_of_ne hle hfin) hdvd hfinDvd
    have hblock := stride.blockBytes_le_paddedBlockBytes
    let block : Vector UInt8 128 := Vector.ofFn fun i =>
      input[offset + i.val]'(by simp only [BLOCKBYTES] at hblock; omega)
    let count := count + BitVec.ofNat 128 BLOCKBYTES
    compress1LoopFrom compressBlock input stride finOffset finBlock finLen finLastBlock finLastNode
      hfinDvd hfinLe (offset + stride.paddedBlockBytes) hnext (Nat.dvd_add hdvd (Nat.dvd_refl _))
      (compressBlock block words count (flagWord false) (flagWord false)) count
termination_by finOffset - offset
decreasing_by
  have := stride.blockBytes_le_paddedBlockBytes
  simp only [BLOCKBYTES] at this
  omega

/-- `compress1_loop`: compress all of `input` into `words`, starting from `count` bytes already
counted. `fin_offset` is the last offset at which a block starts: one less than the input's
length (zero for an empty input), rounded down to a multiple of the stride. The final block comes
from `final_block`, with a zeroed buffer; it carries the final flag when `finalize` says so, and
the last-node flag when `last_node` says so too. -/
def compress1Loop
    (compressBlock : CompressBlockFn)
    (input : List UInt8) (words : Vector Word 8) (count : Count) (lastNode : LastNode)
    (finalize : Finalize) (stride : Stride) : Vector Word 8 :=
  let finOffset :=
    (input.length - 1) - (input.length - 1) % stride.paddedBlockBytes
  let fin := finalBlock input finOffset (Vector.replicate 128 0)
  compress1LoopFrom compressBlock input stride finOffset fin.1 fin.2
    (flagWord finalize.isYes) (flagWord (finalize.isYes && lastNode.isYes))
    (Nat.dvd_sub_mod _) (Nat.sub_le _ _) 0 (Nat.zero_le _) (Nat.dvd_zero _) words count

end Zcash.Common.Blake2bSimd
