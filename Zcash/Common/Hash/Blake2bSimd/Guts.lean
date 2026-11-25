import Zcash.Common.Hash.Blake2b

/-!
# `blake2b_simd`'s shared compression helpers

`blake2b_simd` 1.0.5 keeps what its compression loops share in `src/guts.rs`: which
implementation runs, the flags a block is compressed with, the two halves of the 128-bit byte
counter, and how the last, possibly partial, block of an input is found. This module transcribes
those parts, with the `src/lib.rs` types and constants the compression code uses and Rust's
`u64::from_le_bytes`. The loops, and the dispatch that runs the selected one, are in other
modules.

Rust's `debug_assert!`s in `input_debug_asserts` (`src/guts.rs:251-258`) are left out. Release
builds compile them out, and this transcription follows a release build.

Two differences from the Rust recur in the other modules and are stated once, here. Where the
Rust updates a value in place through `&mut`, the Lean returns the new value. And the Rust's
`try_into().unwrap()` calls take a fixed-size view of bytes whose count is already right, so they
cannot fail and have no counterpart.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/lib.rs:63-64` `Word` and `Count`, `src/lib.rs:76` `BLOCKBYTES`, `src/lib.rs:78-87` `IV`,
  `src/lib.rs:89-102` `SIGMA`;
* `src/guts.rs:14-24` `Platform` and `Implementation`;
* `src/guts.rs:158-201` `Finalize`, `LastNode` and `Stride`, with `src/blake2bp.rs:38` `DEGREE`;
* `src/guts.rs:203-209` `count_low` and `count_high`, `src/guts.rs:216-222` `flag_word`;
* `src/guts.rs:231-249` `final_block`.
-/

namespace Zcash.Common.Blake2bSimd

/-- `Word`: BLAKE2b's 64-bit word. -/
abbrev Word := UInt64

/-- `Count`: the 128-bit count of bytes compressed so far. Lean has no 128-bit unsigned integer
type, so it is a 128-bit vector. -/
abbrev Count := BitVec 128

/-- `BLOCKBYTES`: a block is sixteen words, 128 bytes. -/
def BLOCKBYTES : ℕ := 128

/-- `IV`: BLAKE2b's initialization vector, the same eight words as Ironwood's `Blake2b.IV`. -/
abbrev IV : Vector Word 8 := Blake2b.IV

/-- `SIGMA`: the message schedule, the order in which round `r` feeds the sixteen message words
to the mixing function, the same table as Ironwood's `Blake2b.sigma`. Rust's entries are `u8` used
as indices; here they are `Fin 16`. -/
abbrev SIGMA : Vector (Vector (Fin 16) 16) 12 := Blake2b.sigma

/-- `u64::from_le_bytes`: the word whose little-endian bytes are `bytes`, which is Ironwood's
`Blake2b.wordLE` on exactly eight bytes. -/
def wordFromLeBytes (bytes : Vector UInt8 8) : Word := Blake2b.wordLE bytes.toList

/-- `Platform`: the implementations `blake2b_simd` can select. `SSE41` and `AVX2` exist only on
x86 targets. -/
inductive Platform where
  | portable
  | sse41
  | avx2
  deriving DecidableEq, Repr

/-- `Implementation`: the platform a `Params` or `State` compresses with. -/
structure Implementation where
  platform : Platform
  deriving DecidableEq, Repr

/-- `Finalize`: whether the loop flags its last block as the input's final block. With
`LastNode::Yes` it also sets the last-node flag on that block (`src/portable.rs:168`,
`src/avx2.rs:475`). -/
inductive Finalize where
  | yes
  | no
  deriving DecidableEq, Repr

/-- `Finalize::yes`. -/
def Finalize.isYes : Finalize → Bool
  | .yes => true
  | .no => false

/-- `LastNode`: whether this is the last node of a tree hash. `Params::new` sets `No`
(`src/lib.rs:178`); only `Params::last_node` and `State::set_last_node` change it
(`src/lib.rs:334-341`, `src/lib.rs:508-515`). -/
inductive LastNode where
  | yes
  | no
  deriving DecidableEq, Repr

/-- `LastNode::yes`. -/
def LastNode.isYes : LastNode → Bool
  | .yes => true
  | .no => false

/-- `Stride`: one input at a time (`Serial`, BLAKE2b) or interleaved (`Parallel`, BLAKE2bp). -/
inductive Stride where
  | serial
  | parallel
  deriving DecidableEq, Repr

/-- `Stride::padded_blockbytes`: how far apart one input's consecutive blocks are. BLAKE2bp
interleaves four inputs (`blake2bp::DEGREE`). -/
def Stride.paddedBlockBytes : Stride → ℕ
  | .serial => BLOCKBYTES
  | .parallel => 4 * BLOCKBYTES

/-- `count_low`: the counter's low 64 bits, `count as Word`. -/
def countLow (count : Count) : Word := UInt64.ofBitVec (count.setWidth 64)

/-- `count_high`: the counter's high 64 bits, `(count >> 8 * size_of::<Word>()) as Word`. -/
def countHigh (count : Count) : Word := UInt64.ofBitVec ((count >>> 64).setWidth 64)

/-- `flag_word`: all ones for a set flag, zero otherwise. -/
def flagWord (flag : Bool) : Word := if flag then ~~~0 else 0

-- The Rust writes a partial block into the caller's buffer and returns a reference to it; here
-- the filled buffer is returned. It also returns whether the input may be finalized at this
-- block, which the one-stream loops ignore (`src/portable.rs:166`, `src/avx2.rs:473`) and which
-- is left out.
/-- `final_block`: the block that starts `offset` bytes into `input`, and how many of its bytes
are input. A full block is taken from the input; a partial one is copied to the front of
`buffer`. The offset is capped at the input's length, so nothing here can panic. -/
def finalBlock (input : List UInt8) (offset : ℕ) (buffer : Vector UInt8 128) :
    Vector UInt8 128 × ℕ :=
  let offsetSlice := input.drop (min offset input.length)
  if h : BLOCKBYTES ≤ offsetSlice.length then
    (Vector.ofFn fun i : Fin 128 => offsetSlice[i.val]'(by simp only [BLOCKBYTES] at h; omega),
      BLOCKBYTES)
  else
    (Vector.ofFn fun i : Fin 128 =>
      if hi : i.val < offsetSlice.length then offsetSlice[i.val] else buffer[i],
      offsetSlice.length)

end Zcash.Common.Blake2bSimd
