import CompElliptic.Encodings.Pasta
import Mathlib.Data.Nat.Digits.Lemmas
import Zcash.Common.Hash.Blake2b
import Zcash.Snark.Core.Vesta
import Zcash.Snark.Verifier.FiatShamir

/-!
# Halo2's transcript byte layer

The deployed verifier's Fiat–Shamir transcript is one running BLAKE2b state, personalized
`Halo2-Transcript`, fed a tagged byte encoding of every absorbed element; each squeeze finalizes a
copy of that state and reduces the 64-byte digest modulo `p`. This module writes that byte layer
down and instantiates the abstract `FiatShamir` oracle with it — `halo2Transcript` — so the typed
schedule `deriveChallenges` evaluates to the challenges the deployed verifier actually draws.

The encoding, from halo2's `transcript.rs` and `pasta_curves`' `to_repr`/`coordinates`:

* a squeeze first absorbs the single tag byte `0x00`; the challenge it returns is never absorbed;
* a point is the tag `0x01`, then the 32-byte little-endian `x` and `y` of its affine coordinates
  (uncompressed — the compressed form appears only in the proof string);
* a scalar is the tag `0x02`, then its 32-byte little-endian canonical value;
* the challenge is `Challenge255::new`: the digest read as a little-endian 512-bit integer and
  reduced modulo `p` (`from_uniform_bytes`).

`TranscriptElt.challenge` is exactly the `0x00` tag, so the typed schedule's marker convention is
the deployed byte stream, element for element.

Two facts make the byte layer a faithful carrier of the typed schedule. The encoding is
injective, and it is prefix-free: `encodeTranscript_prefix_iff` says one element list's bytes are
a prefix of another's exactly when the list itself is a prefix. So distinct typed transcripts are
distinct oracle queries, and byte-level prefix structure is typed prefix structure.

Each capture family's `Transcript.lean` checks `deriveChallenges halo2Transcript` against every
captured challenge. The security development still idealizes the squeeze as a random oracle; what
leaves the trusted base here is the encoding beneath it, not BLAKE2b's randomness.
-/

namespace Zcash.Snark

open CompElliptic CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Zcash.Common

/-! ## Little-endian field encodings -/

/-- Reading back the `m` little-endian base-`b` digits of `n` recovers `n` modulo `b ^ m`. -/
theorem ofDigits_ofFn_div_pow_mod (b n : ℕ) :
    ∀ m : ℕ, Nat.ofDigits b (List.ofFn fun i : Fin m => n / b ^ i.val % b) = n % b ^ m
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
      rw [List.ofFn_succ', List.concat_eq_append, Nat.ofDigits_append]
      simp only [Fin.val_castSucc, Fin.val_last, List.length_ofFn, Nat.ofDigits_singleton]
      rw [ofDigits_ofFn_div_pow_mod b n m, Nat.mod_pow_succ]

/-- `LEOS2IP` inverts `I2LEOSP` at 256 bits. -/
theorem LEOS2IP_I2LEOSP_256 (n : Fin (2 ^ 256)) : LEOS2IP (I2LEOSP 256 n) = n.val := by
  unfold LEOS2IP I2LEOSP
  rw [Vector.toList_ofFn, List.map_ofFn]
  have hdigits : (UInt8.toNat ∘ fun i : Fin ((256 + 7) / 8) => UInt8.ofNat (n.val / 256 ^ i.val % 256))
      = fun i : Fin 32 => n.val / 256 ^ i.val % 256 := by
    funext i
    simp only [Function.comp, UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  rw [hdigits, ofDigits_ofFn_div_pow_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq n.isLt (by norm_num))

/-- A byte string read little-endian is below `2 ^ (8 m)`. -/
theorem LEOS2IP_lt {m : ℕ} (S : Vector UInt8 m) : LEOS2IP S < 2 ^ (8 * m) := by
  unfold LEOS2IP
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (l := S.toList.map UInt8.toNat)
    (by norm_num) (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact UInt8.toNat_lt y)
  simpa [List.length_map, Vector.length_toList, pow_mul] using h

/-- Halo2's `to_repr` of a Vesta scalar: the 32 little-endian bytes of its canonical value. -/
def scalarRepr (s : Fp) : Vector UInt8 32 :=
  I2LEOSP 256 ⟨s.val, lt_of_lt_of_le (ZMod.val_lt s) (by decide)⟩

/-- Halo2's `to_repr` of a Vesta base-field coordinate: the 32 little-endian bytes of its
canonical value. -/
def coordRepr (c : VestaBaseField) : Vector UInt8 32 :=
  I2LEOSP 256 ⟨c.val, lt_of_lt_of_le (ZMod.val_lt c) (by decide)⟩

/-- A scalar's `to_repr` reads back as its canonical value. -/
theorem LEOS2IP_scalarRepr (s : Fp) : LEOS2IP (scalarRepr s) = s.val :=
  LEOS2IP_I2LEOSP_256 _

/-- A coordinate's `to_repr` reads back as its canonical value. -/
theorem LEOS2IP_coordRepr (c : VestaBaseField) : LEOS2IP (coordRepr c) = c.val :=
  LEOS2IP_I2LEOSP_256 _

/-- Equal scalar byte strings come from the same scalar. -/
theorem scalarRepr_toList_injective {s t : Fp}
    (h : (scalarRepr s).toList = (scalarRepr t).toList) : s = t := by
  apply ZMod.val_injective
  rw [← LEOS2IP_scalarRepr s, ← LEOS2IP_scalarRepr t]
  unfold LEOS2IP
  rw [h]

/-- Equal coordinate byte strings come from the same coordinate. -/
theorem coordRepr_toList_injective {c d : VestaBaseField}
    (h : (coordRepr c).toList = (coordRepr d).toList) : c = d := by
  apply ZMod.val_injective
  rw [← LEOS2IP_coordRepr c, ← LEOS2IP_coordRepr d]
  unfold LEOS2IP
  rw [h]

/-! ## Transcript elements

The tag bytes are halo2's `BLAKE2B_PREFIX_CHALLENGE = 0`, `BLAKE2B_PREFIX_POINT = 1`, and
`BLAKE2B_PREFIX_SCALAR = 2`. -/

/-- The transcript bytes of an absorbed point: the point tag, then the uncompressed affine
coordinates. The deployed verifier refuses to absorb the identity (`cannot write points at infinity
to the transcript`); this total function encodes the `(0, 0)` sentinel as zero coordinates, which
no accepting transcript contains. -/
def pointBytes (P : VestaG) : List UInt8 :=
  1 :: ((coordRepr P.x).toList ++ (coordRepr P.y).toList)

/-- The transcript bytes of an absorbed scalar: the scalar tag, then its canonical value. -/
def scalarBytes (s : Fp) : List UInt8 :=
  2 :: (scalarRepr s).toList

/-- The bytes one transcript element contributes to the running BLAKE2b state. -/
def encodeElt : TranscriptElt Fp VestaG → List UInt8
  | .point P => pointBytes P
  | .scalar s => scalarBytes s
  | .challenge => [0]

/-- The byte string the deployed transcript has absorbed after the typed prefix `t`. -/
def encodeTranscript (t : List (TranscriptElt Fp VestaG)) : List UInt8 :=
  t.flatMap encodeElt

/-- The empty transcript has absorbed nothing. -/
@[simp] theorem encodeTranscript_nil : encodeTranscript [] = [] := rfl

/-- Absorbing one more element appends its bytes. -/
@[simp] theorem encodeTranscript_cons (e : TranscriptElt Fp VestaG) (t : List (TranscriptElt Fp VestaG)) :
    encodeTranscript (e :: t) = encodeElt e ++ encodeTranscript t := rfl

/-- Absorbing a suffix of elements appends its bytes. -/
@[simp] theorem encodeTranscript_append (s t : List (TranscriptElt Fp VestaG)) :
    encodeTranscript (s ++ t) = encodeTranscript s ++ encodeTranscript t :=
  List.flatMap_append

/-- Equal point encodings come from the same point: the two coordinate halves have fixed length,
and each coordinate encoding is injective. -/
theorem pointBytes_injective : Function.Injective pointBytes := by
  intro P Q h
  simp only [pointBytes, List.cons.injEq, true_and] at h
  obtain ⟨hx, hy⟩ := List.append_inj h (by simp)
  exact SWPoint.ext_pair (by
    rw [coordRepr_toList_injective hx, coordRepr_toList_injective hy])

/-- Equal scalar encodings come from the same scalar. -/
theorem scalarBytes_injective : Function.Injective scalarBytes := by
  intro s t h
  simp only [scalarBytes, List.cons.injEq, true_and] at h
  exact scalarRepr_toList_injective h

/-- The encoding is a prefix code: an element's bytes followed by anything determine the element
and the continuation. The tag byte fixes the constructor and hence the length; each payload is
injective. -/
theorem encodeElt_append_inj {a b : TranscriptElt Fp VestaG} {s t : List UInt8}
    (h : encodeElt a ++ s = encodeElt b ++ t) : a = b ∧ s = t := by
  rcases a with P | x | _ <;> rcases b with Q | y | _
  · simp only [encodeElt, pointBytes, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hPQ, hst⟩ := List.append_inj h (by simp)
    exact ⟨congrArg TranscriptElt.point (pointBytes_injective
      (by simp only [pointBytes, hPQ])), hst⟩
  · exact absurd (List.cons.inj h).1 (by decide)
  · exact absurd (List.cons.inj h).1 (by decide)
  · exact absurd (List.cons.inj h).1 (by decide)
  · simp only [encodeElt, scalarBytes, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hxy, hst⟩ := List.append_inj h (by simp)
    exact ⟨congrArg TranscriptElt.scalar (scalarRepr_toList_injective hxy), hst⟩
  · exact absurd (List.cons.inj h).1 (by decide)
  · exact absurd (List.cons.inj h).1 (by decide)
  · exact absurd (List.cons.inj h).1 (by decide)
  · exact ⟨rfl, (List.cons.inj h).2⟩

/-- **Prefix-freeness of the transcript encoding.** One typed transcript's bytes are a prefix of
another's exactly when the typed transcript is a prefix. -/
theorem encodeTranscript_prefix_iff {s t : List (TranscriptElt Fp VestaG)} :
    encodeTranscript s <+: encodeTranscript t ↔ s <+: t := by
  constructor
  · intro h
    induction s generalizing t with
    | nil => exact List.nil_prefix
    | cons a s ih =>
        cases t with
        | nil =>
            exfalso
            have hnil := List.prefix_nil.mp h
            cases a <;> simp [encodeTranscript, encodeElt, pointBytes, scalarBytes] at hnil
        | cons b t =>
            obtain ⟨r, hr⟩ := h
            rw [encodeTranscript_cons, encodeTranscript_cons, List.append_assoc] at hr
            obtain ⟨rfl, hs⟩ := encodeElt_append_inj hr
            exact List.cons_prefix_cons.mpr ⟨rfl, ih ⟨r, hs⟩⟩
  · rintro ⟨r, rfl⟩
    rw [encodeTranscript_append]
    exact List.prefix_append _ _

/-- **Injectivity of the transcript encoding.** Distinct typed transcripts are distinct byte
strings, hence distinct oracle queries. -/
theorem encodeTranscript_injective : Function.Injective encodeTranscript := by
  intro s t h
  have h₁ : s <+: t := encodeTranscript_prefix_iff.mp (by rw [h])
  have h₂ : t <+: s := encodeTranscript_prefix_iff.mp (by rw [h])
  exact h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)

/-! ## The deployed squeeze -/

/-- The digest halo2 finalizes at a squeeze: BLAKE2b-512, personalized `Halo2-Transcript`, over
every byte absorbed so far, the squeeze's own `0x00` tag included. -/
def squeezeDigest (t : List (TranscriptElt Fp VestaG)) : Vector UInt8 64 :=
  Blake2b.digest64 Blake2b.halo2Personal (encodeTranscript t)

/-- `Challenge255::new`: the 64-byte digest read as a little-endian 512-bit integer, reduced modulo
`p` — `pasta_curves`' `from_uniform_bytes`, which computes `d₀ + d₁ · 2²⁵⁶` in the field from the
two 256-bit halves. This is the integer map whose bias `challenge255` prices. -/
def challengeOfDigest (d : Vector UInt8 64) : Fp :=
  ((LEOS2IP d : ℕ) : Fp)

/-- The digest integer is a 512-bit value, the sample space `challenge255` reduces. -/
theorem LEOS2IP_digest_lt (d : Vector UInt8 64) : LEOS2IP d < 2 ^ 512 := by
  have h := LEOS2IP_lt d
  rwa [show 8 * 64 = 512 from rfl] at h

/-- **Halo2's deployed Fiat–Shamir oracle.** The squeeze is BLAKE2b over the tagged byte encoding
of the typed prefix, reduced to a scalar; `deriveChallenges halo2Transcript` is the deployed
challenge derivation from the transcript bytes up. -/
def halo2Transcript : FiatShamir Fp VestaG :=
  ⟨fun t => challengeOfDigest (squeezeDigest t)⟩

/-- The deployed squeeze, unfolded: the digest of the absorbed bytes, reduced to a scalar. -/
theorem halo2Transcript_squeeze (t : List (TranscriptElt Fp VestaG)) :
    halo2Transcript.squeeze t = challengeOfDigest (squeezeDigest t) := rfl

/-- Distinct typed prefixes reach the hash as distinct byte strings; equal squeezes can only come
from a BLAKE2b collision. -/
theorem squeezeDigest_eq_of_encodeTranscript_eq {s t : List (TranscriptElt Fp VestaG)}
    (h : encodeTranscript s = encodeTranscript t) : squeezeDigest s = squeezeDigest t := by
  unfold squeezeDigest
  rw [h]

end Zcash.Snark
