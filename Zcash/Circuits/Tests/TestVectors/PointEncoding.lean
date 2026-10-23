import CompElliptic.Encodings.Pasta
import Zcash.Circuits.Specs.Pallas
import Zcash.Meta.AxiomCheck

/-!
# Pallas point encodings for the zcash-test-vectors checks

zcash-test-vectors gives points as 32-byte compressed encodings. A check compresses the model's
point and compares the encoding, read as a little-endian integer, with the vector's; injectivity
of compression on the curve then lifts that to the point: the model's point is the only curve
point with that encoding. No decompression or square root is needed.

## What is checked

* `encode` is the integer that CompElliptic's `toBytes` (the compressed point encoding of the
  protocol specification, §5.4.9) denotes little-endian: `x` in the low 255 bits and the parity
  of `y` in bit 255. `LEOS2IP_toBytes` proves the two agree on every valid point; the identity
  `(0, 0)` encodes as `0` in both;
* `eq_of_encode_eq`: compression is injective on curve points;
* `IsEncodingOf n X`: `X` is a curve point, it compresses to `n`, and no other curve point does.
  `IsEncodingOf.of_encode` builds it from the first two.
-/

namespace Zcash.Circuits.Tests.TestVectors.PointEncoding

open Zcash.Circuits
open CompElliptic (toBytes LEOS2IP)

/-- Pallas point compression, as an integer: `x` in the low 255 bits, the parity of `y` in
bit 255. -/
def encode (pt : Point Fp) : Nat := pt.x.val + (pt.y.val % 2) * 2 ^ 255

/-- The low `m` bytes of `n`, read back little-endian, are `n mod 256^m`. -/
theorem ofDigits_bytes (n m : Nat) :
    Nat.ofDigits 256 (List.ofFn fun i : Fin m => n / 256 ^ (i : Nat) % 256) = n % 256 ^ m := by
  induction m generalizing n with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ',
      ← Nat.div_div_eq_div_mul, ih, Nat.mod_mul]

/-- `encode` is the integer CompElliptic's `toBytes` denotes little-endian. -/
theorem LEOS2IP_toBytes (pt : Point Fp) (h : pt.Valid) :
    LEOS2IP (toBytes (pt.toSW h)) = encode pt := by
  have hbyte (a : Nat) : (UInt8.ofNat (a % 256)).toNat = a % 256 := by
    rw [UInt8.toNat_ofNat']; omega
  simp only [LEOS2IP, toBytes, CompElliptic.I2LEOSP, Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, hbyte, Point.toSW_x, Point.toSW_y]
  have h256 : (256 : Nat) ^ 32 = 2 ^ (255 + 1) := by norm_num
  rw [ofDigits_bytes, h256, Nat.mod_eq_of_lt (CompElliptic.encodedInt_lt (k := 255) pt.x pt.y)]
  rfl

/-- Compression is injective on curve points. -/
theorem eq_of_encode_eq {P Q : Point Fp} (hP : P.OnCurve) (hQ : Q.OnCurve)
    (h : encode P = encode Q) : P = Q := by
  have hp : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD < 2 ^ 255 := by decide
  have hPx := ZMod.val_lt P.x
  have hQx := ZMod.val_lt Q.x
  have hPy := Nat.mod_lt P.y.val two_pos
  have hQy := Nat.mod_lt Q.y.val two_pos
  unfold encode at h
  have hx : P.x.val = Q.x.val := by omega
  have hpar : P.y.val % 2 = Q.y.val % 2 := by omega
  have hx' : Q.x = P.x := (ZMod.val_injective _ hx).symm
  have hPx0 : P.x ≠ 0 := by
    intro h0
    obtain ⟨x, y⟩ := P
    subst h0
    exact Point.no_onCurve_of_x_zero y hP
  rcases Point.y_eq_or_neg_of_same_x (Or.inl hP) (Or.inl hQ) hPx0 (hx' ▸ hPx0) hx' with hy | hy
  · cases P; cases Q; simp_all
  · by_cases hy0 : P.y = 0
    · cases P; cases Q; simp_all
    · exfalso
      have : NeZero P.y := ⟨hy0⟩
      have hneg := ZMod.val_neg_of_ne_zero P.y
      rw [← hy] at hneg
      have hodd : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD % 2 = 1 := by decide
      have hlt := ZMod.val_lt P.y
      have hpos : 0 < P.y.val := (ZMod.val_pos).mpr hy0
      omega

/-- The encoding `n` denotes exactly the curve point `X`: `X` is on the curve, compresses to
`n`, and is the only curve point that does. -/
def IsEncodingOf (n : Nat) (X : Point Fp) : Prop :=
  X.OnCurve ∧ encode X = n ∧ ∀ Q : Point Fp, Q.OnCurve → encode Q = n → Q = X

/-- A curve point that compresses to `n` is the point `n` denotes. -/
theorem IsEncodingOf.of_encode {n : Nat} {X : Point Fp} (hX : X.OnCurve) (h : encode X = n) :
    IsEncodingOf n X :=
  ⟨hX, h, fun _ hQ hQn => eq_of_encode_eq hQ hX (hQn.trans h.symm)⟩

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.PointEncoding.LEOS2IP_toBytes
assert_axioms Zcash.Circuits.Tests.TestVectors.PointEncoding.IsEncodingOf.of_encode

end Zcash.Circuits.Tests.TestVectors.PointEncoding
