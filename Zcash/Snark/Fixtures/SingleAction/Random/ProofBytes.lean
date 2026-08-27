import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.SingleAction.Random.ProofHex
import Zcash.Snark.Fixtures.Shared.Hex
import Zcash.Snark.Verifier.ProofBytes

/-!
# Proof-string byte check for the random single-action capture

`Fixture.lean` carries the typed proof `ps` the deployed verifier parsed in this capture;
`ProofHex.lean` carries the raw bytes it parsed it from. This module runs Lean's proof-string
decoder over those bytes and checks that it reads back exactly `ps`, consuming the string
exactly (`capturedProofBytes_decodes`), and that serializing `ps` writes those bytes back
(`serializeProof_eq_capturedProofBytes`). Together they check `read_point`/`read_scalar` — the
canonical decode beneath `ProofString` — against the deployed verifier's own consumption of a
random proof string, whose elements are random canonical values rather than a prover's.

The negatives tamper with the bytes rather than the typed data: a truncated string, a
non-canonical scalar, the identity encoding, an out-of-range coordinate, and a non-residue `x`
are all rejected, and flipping a sign bit decodes to the negated point. They exercise Lean's
decoder; that the deployed one rejects the same strings rests on `decodePoint32_eq_some_iff` and
`decodeScalar32_eq_some_iff` together with a reading of `pasta_curves`' `from_bytes` and
`from_repr`, not on a capture of these exact edits at the current release pin. Orchard's Rust-only
`fingerprint_rejected_capture_two_actions` supplies a related truncation run, plus a skipped-scalar
desynchronization and a well-formed evaluation tamper; it does not exercise the non-canonical
scalar, identity, out-of-range coordinate, non-residue, or sign-bit cases. Exact deployed-reader
checks for those edits are the pending capture-side counterpart.
-/

namespace Zcash.Snark.FixtureRandom

open Zcash.Snark
open Zcash.Arithmetic (scalarFieldOrder)
open CompElliptic.Fields.Pasta

/-- The captured proof bytes, decoded from the rendered hex string. -/
def capturedProofBytes : List UInt8 := (hexDecode? capturedProofHex).getD []

/-- The rendering is well-formed hex, so `capturedProofBytes` is not the empty fallback. -/
theorem capturedProofHex_decodes : (hexDecode? capturedProofHex).isSome = true := by
  native_decide

/-- The captured proof string has the consensus length for one Action. -/
theorem capturedProofBytes_length : capturedProofBytes.length = 4992 := by
  native_decide

/-- **The deployed verifier's parse is Lean's parse.** `readProof?` on the captured bytes returns
exactly the captured typed proof and consumes the string exactly. -/
theorem capturedProofBytes_decodes :
    (readProof? shape).run capturedProofBytes = some (ps, []) := by
  native_decide

/-- Serializing the captured typed proof recovers the captured bytes. -/
theorem serializeProof_eq_capturedProofBytes : serializeProof ps = capturedProofBytes := by
  exact serializeProof_eq_of_readProof?_eq_some capturedProofBytes_decodes

/-! ## Byte-level negatives

Each tamper edits the bytes of one element and leaves every other byte in place; the decoder must
reject at that element, not somewhere downstream of it. -/

/-- Dropping the final byte leaves the last scalar short. -/
theorem truncated_proof_rejected :
    (readProof? shape).run capturedProofBytes.dropLast = none := by
  native_decide

/-- The final scalar `ipaF` re-encoded as its value plus `p`: the same field element, written
non-canonically. -/
def nonCanonicalFinalScalar : List UInt8 :=
  capturedProofBytes.take (capturedProofBytes.length - 32)
    ++ List.ofFn fun i : Fin 32 => UInt8.ofNat ((ps.ipaF.val + scalarFieldOrder) / 256 ^ i.val % 256)

/-- Encoding the final scalar as its value plus the modulus makes the proof reader fail. -/
theorem non_canonical_scalar_rejected :
    (readProof? shape).run nonCanonicalFinalScalar = none := by
  native_decide

/-- The first advice commitment replaced by the identity's encoding, 32 zero bytes. -/
def identityFirstPoint : List UInt8 := List.replicate 32 0 ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by the identity encoding makes the proof reader fail. -/
theorem identity_point_rejected : (readProof? shape).run identityFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (m := 0) (n := 9) rfl rfl
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_zero_eq_none

/-- The first advice commitment replaced by `x = q` with the sign bit clear: a non-canonical
coordinate. -/
def outOfRangeFirstPoint : List UInt8 :=
  (List.ofFn fun i : Fin 32 => UInt8.ofNat (PALLAS_SCALAR_CARD / 256 ^ i.val % 256))
    ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by a non-canonical coordinate makes the proof reader fail. -/
theorem out_of_range_coordinate_rejected :
    (readProof? shape).run outOfRangeFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (m := 0) (n := 9) rfl rfl
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_baseModulus_eq_none

/-- The first advice commitment replaced by `x = 2`, whose radicand `2³ + 5 = 13` is a non-residue
in the Vesta base field: no point has this `x`. -/
def nonResidueFirstPoint : List UInt8 := (2 :: List.replicate 31 0) ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by an `x` with no curve point makes the proof reader fail. -/
theorem non_residue_x_rejected : (readProof? shape).run nonResidueFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (m := 0) (n := 9) rfl rfl
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_two_eq_none

/-- The first advice commitment with its sign bit flipped. -/
def flippedSignFirstPoint : List UInt8 :=
  capturedProofBytes.take 31 ++ [capturedProofBytes.getD 31 0 ^^^ 0x80]
    ++ capturedProofBytes.drop 32

/-- A flipped sign bit decodes to the negated point: the bit is bound to `y`. -/
theorem flipped_sign_decodes_negated :
    ((readProof? shape).run flippedSignFirstPoint).map
        (fun r => r.1.adviceCommitments ⟨0, by decide⟩ ⟨0, by decide⟩)
      = some (-(ps.adviceCommitments ⟨0, by decide⟩ ⟨0, by decide⟩)) := by
  native_decide

end Zcash.Snark.FixtureRandom
