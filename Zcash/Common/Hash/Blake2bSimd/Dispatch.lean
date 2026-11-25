import Zcash.Common.Hash.Blake2bSimd.Avx2
import Zcash.Common.Hash.Blake2bSimd.Portable

/-!
# `blake2b_simd`'s choice of compression loop

`Implementation::compress1_loop` (`src/guts.rs:95-115`) runs the AVX2 loop on an AVX2
implementation and the portable loop on every other one. An SSE4.1 implementation therefore
compresses with the portable code: the crate has no one-stream SSE4.1 loop, as its comment at
`src/guts.rs:109-110` says, and `src/sse41.rs` holds only a two-stream loop. The method lives in
`src/guts.rs`; it is transcribed here because it calls both loops.

## Rust reference

`blake2b_simd` 1.0.5 from crates.io:

* `src/guts.rs:95-115` `Implementation::compress1_loop`.
-/

namespace Zcash.Common.Blake2bSimd

/-- `Implementation::compress1_loop`: the AVX2 loop for `Platform::AVX2`, the portable loop for
`Portable` and `SSE41`. -/
def Implementation.compress1Loop (impl : Implementation) (input : List UInt8)
    (words : Vector Word 8) (count : Count) (lastNode : LastNode) (finalize : Finalize)
    (stride : Stride) : Vector Word 8 :=
  match impl.platform with
  | .avx2 => Avx2.compress1Loop input words count lastNode finalize stride
  | _ => Portable.compress1Loop input words count lastNode finalize stride

end Zcash.Common.Blake2bSimd
