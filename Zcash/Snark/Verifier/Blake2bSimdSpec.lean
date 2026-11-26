import Zcash.Common.Hash.Blake2bSimd.StateSpec
import Zcash.Snark.Verifier.KeyDigest

/-!
# Halo 2's digests are the `blake2b_simd` transcription's

`squeezeDigest` and `keyDigest` are defined with Ironwood's `digest64`. Halo 2 computes them with
`blake2b_simd`: `Params::new().hash_length(64).personal(…).to_state()`, updates, then `finalize`
(`halo2_proofs/src/transcript.rs:72-127`, `halo2_proofs/src/plonk.rs:79-90`, at the halo2 commit
`fbc2dc53` the fixtures pin). By `halo2_finalize_eq_digest64` the transcription of those calls
gives the same digests: here for the transcript's squeeze and for the key digest, with the pieces
of input any split of the bytes Ironwood encodes. Halo 2 reads the key digest with `as_array`,
which at digest length 64 is `as_bytes`.

Two things are not this module's claim: that the pieces Halo 2 passes concatenate to those bytes,
which is the encoding's, and that the transcription matches the Rust, which is trusted.
-/

namespace Zcash.Snark

open Zcash.Common.Blake2bSimd

/-- **The squeeze digest is the transcription's.** With any implementation, the transcribed hasher
set up as Halo 2's transcript hasher and fed pieces that concatenate to `encodeTranscript t`
finalizes to `squeezeDigest t`. -/
theorem squeezeDigest_eq_blake2bSimd (impl : Implementation) (t : List (TranscriptElt Fp VestaG))
    (xs : List (List UInt8)) (hxs : xs.flatten = encodeTranscript t) :
    ((Params.new impl).hashLength? 64 >>= fun params =>
        params.personal? Zcash.Common.Blake2b.halo2Personal.toList).map
        (fun params => (xs.foldl State.update params.toState).finalize.asBytes) =
      some (squeezeDigest t).toList := by
  rw [squeezeDigest, ← hxs]
  exact halo2_finalize_eq_digest64 impl _ xs

/-- **The key digest's hash is the transcription's.** With any implementation, the transcribed
hasher set up as Halo 2 sets it up under `Halo2-Verify-Key`, fed pieces that concatenate to
`keyDigestPreimage s`, finalizes to the digest `keyDigest s` reduces. -/
theorem keyDigest_eq_blake2bSimd (impl : Implementation) (s : String) (xs : List (List UInt8))
    (hxs : xs.flatten = keyDigestPreimage s) :
    ((Params.new impl).hashLength? 64 >>= fun params =>
        params.personal? verifyKeyPersonal.toList).map
        (fun params => (xs.foldl State.update params.toState).finalize.asBytes) =
      some (Zcash.Common.Blake2b.digest64 verifyKeyPersonal (keyDigestPreimage s)).toList := by
  rw [← hxs]
  exact halo2_finalize_eq_digest64 impl _ xs

end Zcash.Snark
