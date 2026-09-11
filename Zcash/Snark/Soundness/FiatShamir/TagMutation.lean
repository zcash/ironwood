import Zcash.Snark.Verifier.Transcript

/-!
# The transcript tags are load-bearing

`encodeElt` prefixes every absorbed element with halo2's domain tag — `0x00` for a squeeze,
`0x01` for a point, `0x02` for a scalar — and `encodeTranscript_injective` shows the tagged
encoding sends distinct typed transcripts to distinct byte strings, which is what lets the
random-oracle idealization over typed transcripts stand in for an oracle over bytes. This module
deletes the tags and exhibits the collisions that appear:

* `untagged_point_scalar_collision` — a point's uncompressed coordinates are the same 64 bytes as
  two scalars with the same canonical values, so `[point P]` and `[scalar a, scalar b]` reach the
  hash as one query. The witness is a fixed Vesta point whose coordinates are both below `p`, so
  each coordinate's bytes are also a scalar's.
* `untagged_marker_collision` — with no squeeze marker, a transcript and its pre-squeeze extension
  are the same bytes, so the challenge squeezed from a prefix is the hash of the prefix itself.

Each gives `¬ Function.Injective` for the untagged encoding, and the `tagged_separates_*` theorems
show the deployed tags separate the same witnesses. Nothing in the development depends on this
module; it exists so that the role of the tags is checked rather than asserted.
-/

namespace Zcash.Snark.TagMutation

open Zcash.Snark
open CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta

/-- The deployed encoding with every domain tag deleted. -/
def encodeEltUntagged : TranscriptElt Fp VestaG → List UInt8
  | .point P => (coordRepr P.x).toList ++ (coordRepr P.y).toList
  | .scalar s => (scalarRepr s).toList
  | .challenge => []

/-- Byte strings of typed transcripts under the untagged encoding. -/
def encodeTranscriptUntagged (t : List (TranscriptElt Fp VestaG)) : List UInt8 :=
  t.flatMap encodeEltUntagged

/-- The witness point's `x`: `1`. -/
def witnessX : VestaBaseField := 1

/-- The witness point's `y`: a square root of `1³ + 5 = 6` in the Vesta base field. Its value is
below `p` (as both roots' are), so its coordinate bytes also read back exactly as a scalar's. -/
def witnessY : VestaBaseField :=
  0x1943666ea922ae6b13b64e3aae89754cacce3a7f298ba20c4e4389b9b0276a62

/-- `(1, √6)` lies on Vesta. -/
theorem witness_onCurve : OnCurve Vesta.a Vesta.b (witnessX, witnessY) := by decide

/-- The witness point `(1, √6)`. -/
def witness : VestaG := ⟨witnessX, witnessY, Or.inl witness_onCurve⟩

/-- The witness `x` read as a scalar. Its value is below `p`, so the reading is exact; were it not,
the collision below would fail. -/
def witnessA : Fp := (witnessX.val : Fp)

/-- The witness `y` read as a scalar, exact for the same reason. -/
def witnessB : Fp := (witnessY.val : Fp)

/-- **Without tags, a point is two scalars.** -/
theorem untagged_point_scalar_collision :
    encodeTranscriptUntagged [.point witness]
      = encodeTranscriptUntagged [.scalar witnessA, .scalar witnessB] := by
  decide

/-- The untagged encoding is not injective: the point and the scalar pair are different typed
transcripts with the same bytes. -/
theorem untagged_not_injective_point_scalar : ¬ Function.Injective encodeTranscriptUntagged := by
  intro h
  have := h untagged_point_scalar_collision
  simp at this

/-- **Without the squeeze marker, a squeeze input is its own absorbed prefix.** -/
theorem untagged_marker_collision (t : List (TranscriptElt Fp VestaG)) :
    encodeTranscriptUntagged (t ++ [.challenge]) = encodeTranscriptUntagged t := by
  simp [encodeTranscriptUntagged, encodeEltUntagged]

/-- The untagged encoding is not injective: the empty transcript and a lone squeeze marker are
different typed transcripts with the same bytes. -/
theorem untagged_not_injective_marker : ¬ Function.Injective encodeTranscriptUntagged := by
  intro h
  have := h (untagged_marker_collision [])
  simp at this

/-- The deployed tags separate the point/scalar witness. -/
theorem tagged_separates_witness :
    encodeTranscript [.point witness] ≠ encodeTranscript [.scalar witnessA, .scalar witnessB] := by
  decide

/-- The deployed marker separates every transcript from its pre-squeeze extension. -/
theorem tagged_separates_marker (t : List (TranscriptElt Fp VestaG)) :
    encodeTranscript (t ++ [.challenge]) ≠ encodeTranscript t := by
  intro h
  have := congrArg List.length h
  simp [encodeTranscript_append, encodeElt] at this

end Zcash.Snark.TagMutation
