import Zcash.Common.Hash.Blake2bSimd.Dispatch
import Zcash.Common.Hash.Blake2bSimd.Params

/-!
# `blake2b_simd`'s incremental hashing state

`blake2b_simd` 1.0.5 hashes incrementally with `State` (`src/lib.rs`): `Params::to_state` makes
one, `update` feeds it input in any pieces, and `finalize` returns the digest as a `Hash`. The
state keeps the words, the count of bytes compressed, and a one-block buffer of input not yet
compressed. `update` never compresses the buffered block until more input follows, so the last
block is always still in the buffer when `finalize` compresses it as the final one.

`finalize` takes `&self` and compresses a copy of the words, so it leaves the state unchanged.
Halo 2 relies on that: at each challenge it finalizes a clone of its transcript state and keeps
updating the original (`halo2_proofs/src/transcript.rs:122-124`, at the halo2 commit `fbc2dc53`
the fixtures pin). Here the state is a value, so `finalize` cannot change it.

The buffer length is a `Fin 129`, at most `BLOCKBYTES` by its type. The Rust relies on that
bound: without it, the buffer slices in `fill_buf` and `finalize` would panic, and
`BLOCKBYTES - self.buflen` would wrap in a release build.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/lib.rs:391-400` `State`, `src/lib.rs:408-424` `with_params`, `src/lib.rs:232-234`
  `Params::to_state`;
* `src/lib.rs:426-431` `fill_buf`, `src/lib.rs:436-452` `compress_buffer_if_possible`;
* `src/lib.rs:455-480` `update`, `src/lib.rs:484-498` `finalize`;
* `src/lib.rs:531-545` `state_words_to_bytes`, `src/lib.rs:582-585` `Hash`,
  `src/lib.rs:590-592` `as_bytes`.
-/

namespace Zcash.Common.Blake2bSimd

/-- `State`: an incremental hash in progress. -/
structure State where
  /-- The state words. -/
  words : Vector Word 8
  /-- The count of bytes compressed so far, the buffer not included. -/
  count : Count
  /-- The buffer of input not yet compressed. -/
  buf : Vector UInt8 128
  /-- How many bytes of `buf` hold input. -/
  buflen : Fin 129
  /-- Whether this is the last node of a tree hash. -/
  lastNode : LastNode
  /-- The digest length. -/
  hashLength : Fin 65
  /-- The implementation that compresses. -/
  implementation : Implementation

/-- `with_params`: the state a `Params` starts: its starting words, an empty buffer, and its
last-node flag, digest length and implementation. A keyed hash starts with the key block
buffered. The Rust also keeps an `is_keyed` field, which only `State::count` reads; it is left
out. -/
def State.withParams (p : Params) : State :=
  let state : State :=
    { words := p.toWords, count := 0, buf := Vector.replicate 128 0, buflen := 0,
      lastNode := p.lastNode, hashLength := p.hashLength, implementation := p.implementation }
  if p.keyLength > 0 then { state with buf := p.keyBlock, buflen := 128 } else state

/-- `Params::to_state`. -/
def Params.toState (p : Params) : State := State.withParams p

/-- `fill_buf`: copy as much of `input` as fits after the buffered bytes; return the state and
the rest of `input`. -/
def State.fillBuf (st : State) (input : List UInt8) : State × List UInt8 :=
  let take := min (BLOCKBYTES - st.buflen.val) input.length
  let buf := Vector.ofFn fun i : Fin 128 =>
    if h : st.buflen.val ≤ i.val ∧ i.val < st.buflen.val + take then
      input[i.val - st.buflen.val]'(by omega)
    else st.buf[i]
  have htake : st.buflen.val + take < 129 := by
    show st.buflen.val + min (BLOCKBYTES - st.buflen.val) input.length < 129
    simp only [BLOCKBYTES]; omega
  ({ st with buf, buflen := ⟨st.buflen.val + take, htake⟩ },
    input.drop take)

/-- `compress_buffer_if_possible`: if bytes are buffered, top the buffer up from `input`; if
input remains after that, the buffer is a full block that is not the last, so compress it. -/
def State.compressBufferIfPossible (st : State) (input : List UInt8) : State × List UInt8 :=
  if st.buflen.val > 0 then
    let (st, input) := st.fillBuf input
    if !input.isEmpty then
      ({ st with
          words := st.implementation.compress1Loop st.buf.toList st.words st.count st.lastNode
            .no .serial,
          count := st.count + BitVec.ofNat 128 BLOCKBYTES,
          buflen := 0 }, input)
    else (st, input)
  else (st, input)

/-- `update`: feed `input` to the state. A partly full buffer is completed first; then every
whole block of `input` except the one holding its last byte is compressed directly; the rest is
buffered. -/
def State.update (st : State) (input : List UInt8) : State :=
  let (st, input) := st.compressBufferIfPossible input
  let «end» := (input.length - 1) - (input.length - 1) % BLOCKBYTES
  let (st, input) :=
    if «end» > 0 then
      ({ st with
          words := st.implementation.compress1Loop (input.take «end») st.words st.count
            st.lastNode .no .serial,
          count := st.count + BitVec.ofNat 128 «end» }, input.drop «end»)
    else (st, input)
  (st.fillBuf input).1

/-- `u64::to_le_bytes`: the eight bytes of `w`, least significant first. -/
def wordToLeBytes (w : Word) : Vector UInt8 8 :=
  Vector.ofFn fun i : Fin 8 => (w >>> (8 * i.val).toUInt64).toUInt8

/-- `state_words_to_bytes`: the eight words' little-endian bytes, word after word. -/
def stateWordsToBytes (words : Vector Word 8) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 => (wordToLeBytes words[i.val / 8])[i.val % 8]

/-- `Hash`: a digest, stored in full with the digest length. -/
structure Hash where
  /-- All 64 bytes of the final state. -/
  bytes : Vector UInt8 64
  /-- The digest length. -/
  len : Fin 65

/-- `as_bytes`: the digest, the first `len` bytes. -/
def Hash.asBytes (h : Hash) : List UInt8 := h.bytes.toList.take h.len.val

/-- `finalize`: compress the buffered bytes as the final block, into a copy of the words, and
return their bytes with the digest length. The state itself is unchanged. -/
def State.finalize (st : State) : Hash :=
  let wordsCopy := st.implementation.compress1Loop (st.buf.toList.take st.buflen.val) st.words
    st.count st.lastNode .yes .serial
  { bytes := stateWordsToBytes wordsCopy, len := st.hashLength }

end Zcash.Common.Blake2bSimd
