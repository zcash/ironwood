import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Zcash.Snark.Fixtures.Shared.Hex
import Zcash.Snark.Verifier.ProofBytes

/-!
# Proof-string byte check for the random two-action capture

`Fixture.lean` carries both the typed proof `ps` and `capturedProofHex`, the raw bytes the deployed
verifier parsed it from. This module runs Lean's proof-string
decoder over those bytes and checks that it reads back exactly `ps`, consuming the string
exactly (`capturedProofBytes_decodes`), and that serializing `ps` writes those bytes back
(`serializeProof_eq_capturedProofBytes`). Together they check `read_point`/`read_scalar` — the
canonical decode beneath `ProofString` — against the deployed verifier's own consumption of a
random proof string, whose elements are random canonical values rather than a prover's.

The negatives tamper with the bytes rather than the typed data: a truncated string, a
non-canonical scalar, the identity encoding, an out-of-range coordinate, and a non-residue `x`
are all rejected, and flipping a sign bit decodes to the negated point. They exercise Lean's
decoder independently. At the pinned Orchard #544 commit, the random capture driver applies these
same six edits to this deterministic proof before export and checks them through deployed
`Blake2bRead`: the first five reject and the sign-bit edit decodes to the negated point.
`decodePoint32_eq_some_iff` and `decodeScalar32_eq_some_iff` state why the two readers agree for
every individual canonical encoding; the capture supplies concrete end-to-end regression coverage
for these exact bytes.
-/

namespace Zcash.Snark.FixtureRandom2

open Zcash.Snark
open Zcash.Arithmetic (scalarFieldOrder)
open CompElliptic.Fields.Pasta

/-- The captured proof bytes, decoded from the rendered hex string. -/
def capturedProofBytes : List UInt8 := (hexDecode? capturedProofHex).getD []

/-- **The deployed verifier's parse is Lean's parse.** `readProof?` on the captured bytes returns
exactly the captured typed proof and consumes the string exactly. This is the family's one
native anchor at the byte layer; the hex well-formedness, length, truncation, and
non-canonical-scalar facts below are derived from it. -/
theorem capturedProofBytes_decodes :
    (readProof? shape).run capturedProofBytes = some (ps, []) := by
  native_decide

/-- The rendering is well-formed hex, so `capturedProofBytes` is not the empty fallback: had the
hex been rejected, the parse anchored above would have run on `[]` and failed at its first
point. -/
theorem capturedProofHex_decodes : (hexDecode? capturedProofHex).isSome = true := by
  rcases hh : hexDecode? capturedProofHex with _ | bs
  · have hd := capturedProofBytes_decodes
    have hnone : (readProof? shape).run capturedProofBytes = none := by
      show (readProof? shape).run ((hexDecode? capturedProofHex).getD []) = none
      rw [hh, Option.getD_none]
      exact readProof?_eq_none_of_first_point (by decide) (by decide) rfl
    rw [hnone] at hd
    simp at hd
  · rfl

/-- The captured proof string has ZIP 225's specified canonical length for two Actions:
`2720 + 2272 · 2`): the byte accounting of its successful parse at this family's shape. -/
theorem capturedProofBytes_length : capturedProofBytes.length = 7264 := by
  have h := readProof?_length capturedProofBytes_decodes
  have hp : proofLength shape = 7264 := by decide
  simpa [hp] using h

/-- Serializing the captured typed proof recovers the captured bytes. -/
theorem serializeProof_eq_capturedProofBytes : serializeProof ps = capturedProofBytes := by
  exact serializeProof_eq_of_readProof?_eq_some capturedProofBytes_decodes

/-! ## Byte-level negatives

Each tamper edits the bytes of one element and leaves every other byte in place; the decoder must
reject at that element, not somewhere downstream of it. -/

/-- Dropping the final byte leaves the last scalar short: truncation is rejected by the
parse's byte accounting (`readProof?_none_of_truncated`). -/
theorem truncated_proof_rejected :
    (readProof? shape).run capturedProofBytes.dropLast = none := by
  rw [List.dropLast_eq_take]
  exact readProof?_none_of_truncated capturedProofBytes_decodes
    (by rw [capturedProofBytes_length]; omega)

/-- The final scalar `ipaF` re-encoded as its value plus `p`: the same field element, written
non-canonically. -/
def nonCanonicalFinalScalar : List UInt8 :=
  capturedProofBytes.take (capturedProofBytes.length - 32)
    ++ List.ofFn fun i : Fin 32 => UInt8.ofNat ((ps.ipaF.val + scalarFieldOrder) / 256 ^ i.val % 256)

/-- Encoding the final scalar as its value plus the modulus makes the proof reader fail: the
tampered tail reads at or above `p`, which `readProof?_none_of_noncanonical_final_scalar`
rejects by whole-proof canonicality. -/
theorem non_canonical_scalar_rejected :
    (readProof? shape).run nonCanonicalFinalScalar = none := by
  have hvlt : ps.ipaF.val + scalarFieldOrder < 2 ^ 256 := by
    have h1 : ps.ipaF.val < scalarFieldOrder := ZMod.val_lt _
    have h2 : scalarFieldOrder + scalarFieldOrder ≤ 2 ^ 256 := by decide
    exact lt_of_lt_of_le (Nat.add_lt_add_right h1 _) h2
  show (readProof? shape).run (capturedProofBytes.take (capturedProofBytes.length - 32)
      ++ (List.ofFn fun i : Fin 32 =>
          UInt8.ofNat ((ps.ipaF.val + scalarFieldOrder) / 256 ^ i.val % 256))) = none
  exact readProof?_none_of_noncanonical_final_scalar (bs := capturedProofBytes)
    capturedProofBytes_decodes (by simp)
    (by rw [leInt_ofFn_32 ⟨ps.ipaF.val + scalarFieldOrder, hvlt⟩]
        exact Nat.le_add_left _ _)

/-- The first advice commitment replaced by the identity's encoding, 32 zero bytes. -/
def identityFirstPoint : List UInt8 := List.replicate 32 0 ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by the identity encoding makes the proof reader fail. -/
theorem identity_point_rejected : (readProof? shape).run identityFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (by decide) (by decide)
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_zero_eq_none

/-- The first advice commitment replaced by `x = q` with the sign bit clear: a non-canonical
coordinate. -/
def outOfRangeFirstPoint : List UInt8 :=
  (List.ofFn fun i : Fin 32 => UInt8.ofNat (PALLAS_SCALAR_CARD / 256 ^ i.val % 256))
    ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by a non-canonical coordinate makes the proof reader fail. -/
theorem out_of_range_coordinate_rejected :
    (readProof? shape).run outOfRangeFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (by decide) (by decide)
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_baseModulus_eq_none

/-- The first advice commitment replaced by `x = 2`, whose radicand `2³ + 5 = 13` is a non-residue
in the Vesta base field: no point has this `x`. -/
def nonResidueFirstPoint : List UInt8 := (2 :: List.replicate 31 0) ++ capturedProofBytes.drop 32

/-- Replacing the first commitment by an `x` with no curve point makes the proof reader fail. -/
theorem non_residue_x_rejected : (readProof? shape).run nonResidueFirstPoint = none := by
  apply readProof?_eq_none_of_first_point (by decide) (by decide)
  exact pointReader_eq_none_of_prefix (by simp) decodePoint32_two_eq_none

/-- The first advice commitment with its sign bit flipped. -/
def flippedSignFirstPoint : List UInt8 :=
  capturedProofBytes.take 31 ++ [capturedProofBytes.getD 31 0 ^^^ 0x80]
    ++ capturedProofBytes.drop 32

/-- A flipped sign bit decodes to the negated point: the bit is bound to `y`. The captured
parse places the first advice commitment's encoding in the first 32 bytes
(`readProof?_run_replace_first_advice`); flipping bit 255 of a non-identity encoding is exactly
the negated point's encoding (`toBytes_neg_flip`); and the rest of the read runs on the
untouched suffix. -/
theorem flipped_sign_decodes_negated :
    ((readProof? shape).run flippedSignFirstPoint).map
        (fun r => r.1.adviceCommitments ⟨0, by decide⟩ ⟨0, by decide⟩)
      = some (-(ps.adviceCommitments ⟨0, by decide⟩ ⟨0, by decide⟩)) := by
  have hm : shape.numProofs ≠ 0 := by decide
  have hn : shape.numAdviceColumns ≠ 0 := by decide
  have hx : ∀ mid, pointReader.run capturedProofBytes = some
      (ps.adviceCommitments ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩, mid) →
      pointReader.run flippedSignFirstPoint = some
        (-(ps.adviceCommitments ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩), mid) := by
    intro mid hmid
    obtain ⟨hP0ne, hbs⟩ := pointReader_eq_some_iff.mp hmid
    have hflip : flippedSignFirstPoint
        = (CompElliptic.toBytes (-(ps.adviceCommitments ⟨0, Nat.pos_of_ne_zero hm⟩
            ⟨0, Nat.pos_of_ne_zero hn⟩))).toList ++ mid := by
      show capturedProofBytes.take 31 ++ [capturedProofBytes.getD 31 0 ^^^ 0x80]
          ++ capturedProofBytes.drop 32 = _
      rw [hbs, List.take_append_of_le_length (by simp), List.getD_append _ _ _ _ (by simp),
        List.drop_left' (by simp), ← toBytes_neg_flip hP0ne]
    rw [hflip]
    exact pointReader_eq_some_iff.mpr ⟨neg_ne_zero.mpr hP0ne, rfl⟩
  obtain ⟨ps', hrun, hproj⟩ :=
    readProof?_run_replace_first_advice hm hn capturedProofBytes_decodes hx
  rw [hrun]
  simp only [Option.map_some]
  exact congrArg some hproj

end Zcash.Snark.FixtureRandom2
