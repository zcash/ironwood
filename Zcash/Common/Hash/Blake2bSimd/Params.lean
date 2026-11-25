import Zcash.Common.Hash.Blake2bSimd.Guts

/-!
# `blake2b_simd`'s hash parameters

`blake2b_simd` 1.0.5 configures a hash with `Params` (`src/lib.rs`): the digest length, the
key, salt and personalization, the tree-hashing fields, and the implementation. `Params::new`
gives the defaults, its setters change them, and `to_words` turns them into the starting state:
`IV` with the parameter block xored in.

Halo 2 calls only `hash_length` and `personal`: `halo2_proofs/src/transcript.rs:76-79` and
`:162-165` and `halo2_proofs/src/plonk.rs:79-82`, at the halo2 commit `fbc2dc53` the fixtures pin.
This module transcribes those two setters, with the fields and `to_words` in full. The Rust setters
`assert!` their argument's bounds; here they return `none` where the Rust would panic. The digest
length is a `Fin 65`, at most `OUTBYTES` by its type, which `Hash::as_bytes` (`src/lib.rs:590-592`)
relies on to slice the digest.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/lib.rs:145-159` `Params`, `src/lib.rs:164-181` `Params::new`;
* `src/lib.rs:184-206` `to_words`;
* `src/lib.rs:240-248` `hash_length`, `src/lib.rs:274-283` `personal`.
-/

namespace Zcash.Common.Blake2bSimd

/-- `Params`: the hash's configuration. -/
structure Params where
  /-- The digest length in bytes; the setter keeps it from 1 to `OUTBYTES`. -/
  hashLength : Fin 65
  /-- The key length; zero for an unkeyed hash. -/
  keyLength : UInt8
  /-- The key, zero-padded to a block. -/
  keyBlock : Vector UInt8 128
  /-- The salt, zero-padded. -/
  salt : Vector UInt8 16
  /-- The personalization, zero-padded. -/
  personal : Vector UInt8 16
  /-- Tree hashing: the fanout. -/
  fanout : UInt8
  /-- Tree hashing: the maximum depth. -/
  maxDepth : UInt8
  /-- Tree hashing: the maximum leaf length. -/
  maxLeafLength : UInt32
  /-- Tree hashing: this node's offset. -/
  nodeOffset : UInt64
  /-- Tree hashing: this node's depth. -/
  nodeDepth : UInt8
  /-- Tree hashing: the inner digest length. -/
  innerHashLength : UInt8
  /-- Tree hashing: whether this is the last node. -/
  lastNode : LastNode
  /-- The implementation that compresses. -/
  implementation : Implementation

/-- `Params::new`: a 64-byte digest, no key, salt or personalization, sequential mode (fanout and
depth 1, the other tree fields 0, not the last node), and the implementation
`Implementation::detect` picks, which here is the argument. -/
def Params.new (implementation : Implementation) : Params where
  hashLength := ⟨OUTBYTES, by decide⟩
  keyLength := 0
  keyBlock := Vector.replicate 128 0
  salt := Vector.replicate 16 0
  personal := Vector.replicate 16 0
  fanout := 1
  maxDepth := 1
  maxLeafLength := 0
  nodeOffset := 0
  nodeDepth := 0
  innerHashLength := 0
  lastNode := .no
  implementation := implementation

/-- `to_words`: the starting state, `IV` xored with the parameter block. Word 0 packs the digest
length, key length, fanout, depth and leaf length; words 1 and 2 the node offset, node depth and
inner length; words 4 to 7 the salt and personalization, each half read little-endian. -/
def Params.toWords (p : Params) : Vector Word 8 :=
  let half (v : Vector UInt8 16) (k : Fin 2) : Word :=
    wordFromLeBytes (Vector.ofFn fun i : Fin 8 => v[8 * k.val + i.val]'(by omega))
  #v[IV[0] ^^^ p.hashLength.val.toUInt64 ^^^ (p.keyLength.toUInt64 <<< 8)
       ^^^ (p.fanout.toUInt64 <<< 16) ^^^ (p.maxDepth.toUInt64 <<< 24)
       ^^^ (p.maxLeafLength.toUInt64 <<< 32),
     IV[1] ^^^ p.nodeOffset,
     IV[2] ^^^ p.nodeDepth.toUInt64 ^^^ (p.innerHashLength.toUInt64 <<< 8),
     IV[3],
     IV[4] ^^^ half p.salt 0,
     IV[5] ^^^ half p.salt 1,
     IV[6] ^^^ half p.personal 0,
     IV[7] ^^^ half p.personal 1]

/-- `hash_length`: set the digest length, `none` where the Rust panics, outside 1 to `OUTBYTES`. -/
def Params.hashLength? (p : Params) (length : ℕ) : Option Params :=
  if h : 1 ≤ length ∧ length ≤ OUTBYTES then
    some { p with hashLength := ⟨length, by simp only [OUTBYTES] at h; omega⟩ }
  else none

/-- `personal`: set the personalization, zero-padded to `PERSONALBYTES`; `none` where the Rust
panics, when it is longer. -/
def Params.personal? (p : Params) (personalization : List UInt8) : Option Params :=
  if personalization.length ≤ PERSONALBYTES then
    some { p with personal := Vector.ofFn fun i =>
      if h : i.val < personalization.length then personalization[i.val] else 0 }
  else none

end Zcash.Common.Blake2bSimd
