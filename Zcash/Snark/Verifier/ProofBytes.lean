import Mathlib.Data.Fin.Tuple.Basic
import Zcash.Snark.Verifier.Transcript

/-!
# Halo2's proof-string byte layer

`ProofString` starts where halo2's `Blake2bRead` finishes: at typed points and scalars. This module
writes down the reads beneath it — `read_point` and `read_scalar` from halo2's `transcript.rs`,
with `pasta_curves`' `from_bytes` and `from_repr` — as a decoder over the raw proof bytes, and the
prover's `write_point`/`write_scalar` as the serializer.

* `decodeScalar32` accepts exactly 32 bytes as a little-endian integer and only when it is below
  `p` (`from_repr`'s canonicality check).
* `decodePoint32` accepts exactly 32 bytes: bit 255 is the parity of `y`, the low 255 bits are `x`
  and must be below `q`; `y` is the square root of `x³ + 5` with the signalled parity. The
  all-zero string, which `from_bytes` decodes to the identity, is rejected: the deployed
  transcript refuses to absorb the identity, and no Vesta point has `x = 0`
  (`Vesta.no_onCurve_x_zero`), so the rejection here is the deployed rejection one step earlier.
* `readProof?` reads a whole proof in the verifier's read order — the order `deriveChallenges`
  absorbs in — and `serializeProof` writes one back.

The element decoders are canonical in both directions (`decodeScalar32_eq_some_iff`,
`decodePoint32_eq_some_iff`): a decode succeeds exactly on the encoding of the element it
returns. So non-canonical scalars, out-of-range coordinates, non-residue `x`, the identity, and
truncation are all rejected, and the typed proof the verifier goes on to hash is the unique
preimage of the bytes it read. `readVec_serializeVec` and `readVec_eq_some` lift both directions
to the vectors the proof is made of.

The random capture families check `readProof?` against the deployed verifier's own consumption of
their raw proof bytes, and `serializeProof` against the same bytes.
-/

namespace Zcash.Snark

open CompElliptic CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta
open Zcash.Arithmetic (scalarFieldOrder)

/-! ## Little-endian integers of byte lists -/

/-- The little-endian integer a byte list denotes. -/
def leInt (bs : List UInt8) : ℕ := Nat.ofDigits 256 (bs.map UInt8.toNat)

/-- On a fixed-length vector, `leInt` is `LEOS2IP`. -/
theorem leInt_toList {m : ℕ} (S : Vector UInt8 m) : leInt S.toList = LEOS2IP S := rfl

/-- The first byte is the least significant digit. -/
theorem leInt_cons (b : UInt8) (bs : List UInt8) : leInt (b :: bs) = b.toNat + 256 * leInt bs := by
  simp [leInt, Nat.ofDigits_cons]

/-- A little-endian integer is below `256 ^ length`. -/
theorem leInt_lt (bs : List UInt8) : leInt bs < 256 ^ bs.length := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (l := bs.map UInt8.toNat) (by norm_num) (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact UInt8.toNat_lt y)
  simpa [leInt, List.length_map] using h

/-- A 32-byte string denotes a 256-bit integer. -/
theorem leInt_lt_of_length_32 {bs : List UInt8} (h : bs.length = 32) : leInt bs < 2 ^ 256 := by
  have := leInt_lt bs
  rw [h] at this
  exact lt_of_lt_of_eq this (by norm_num)

/-- A string of zero bytes denotes zero. -/
@[simp] theorem leInt_replicate_zero (n : ℕ) :
    leInt (List.replicate n (0 : UInt8)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leInt_cons, ih]

/-- Reading the explicit 32-byte little-endian rendering used by the malformed-coordinate
fixtures recovers the integer it renders. -/
theorem leInt_ofFn_32 (n : Fin (2 ^ 256)) :
    leInt (List.ofFn fun i : Fin 32 => UInt8.ofNat (n.val / 256 ^ i.val % 256)) = n.val := by
  have h : (List.ofFn fun i : Fin 32 => UInt8.ofNat (n.val / 256 ^ i.val % 256)) =
      (I2LEOSP 256 n).toList := by
    rw [I2LEOSP, Vector.toList_ofFn]
  rw [h, leInt_toList, LEOS2IP_I2LEOSP_256]

/-- Each byte is recovered from the little-endian integer: byte `i` is digit `i` in base 256. -/
theorem leInt_div_pow_mod (bs : List UInt8) :
    ∀ i : ℕ, ∀ hi : i < bs.length, leInt bs / 256 ^ i % 256 = bs[i].toNat := by
  induction bs with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [leInt_cons, pow_zero, Nat.div_one, List.getElem_cons_zero]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (UInt8.toNat_lt b)
      | succ i =>
          simp only [leInt_cons, List.getElem_cons_succ]
          rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
            Nat.div_eq_of_lt (UInt8.toNat_lt b), Nat.zero_add]
          exact ih i (by simpa using hi)

/-- The 32 little-endian bytes of an integer are the bytes it was read from. -/
theorem ofFn_leInt {bs : List UInt8} (h : bs.length = 32) {n : ℕ} (hn : n = leInt bs) :
    (List.ofFn fun i : Fin 32 => UInt8.ofNat (n / 256 ^ i.val % 256)) = bs := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [hn, leInt_div_pow_mod bs i h2]
  exact UInt8.ofNat_toNat

/-- A scalar's `to_repr` is the byte string its canonical value was read from. -/
theorem scalarRepr_toList_eq {s : Fp} {bs : List UInt8} (h : bs.length = 32)
    (hv : s.val = leInt bs) : (scalarRepr s).toList = bs := by
  rw [scalarRepr, I2LEOSP, Vector.toList_ofFn]
  exact ofFn_leInt h hv

/-- A point's compressed encoding is the byte string its sign-and-`x` integer was read from. -/
theorem toBytes_toList_eq {P : VestaG} {bs : List UInt8} (h : bs.length = 32)
    (hv : P.x.val + P.y.val % 2 * 2 ^ 255 = leInt bs) : (toBytes P).toList = bs := by
  rw [toBytes, I2LEOSP, Vector.toList_ofFn]
  exact ofFn_leInt h hv

/-! ## Decoding one scalar

`read_scalar` takes 32 bytes; `from_repr` accepts them only when the little-endian integer is
below `p`, so a scalar has exactly one accepted encoding. -/

/-- `from_repr`: exactly 32 canonical little-endian bytes, or rejection. -/
def decodeScalar32 (enc : List UInt8) : Option Fp :=
  if enc.length = 32 then
    if leInt enc < scalarFieldOrder then some ((leInt enc : ℕ) : Fp) else none
  else none

/-- **Canonical scalar decoding.** Decoding succeeds exactly on the scalar's 32-byte `to_repr`. -/
theorem decodeScalar32_eq_some_iff {enc : List UInt8} {s : Fp} :
    decodeScalar32 enc = some s ↔ enc = (scalarRepr s).toList := by
  constructor
  · intro hd
    unfold decodeScalar32 at hd
    split_ifs at hd with h hlt
    simp only [Option.some.injEq] at hd
    subst hd
    refine (scalarRepr_toList_eq h ?_).symm
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hlt
  · intro heq
    rw [heq]
    unfold decodeScalar32
    rw [if_pos (by simp), leInt_toList, LEOS2IP_scalarRepr, if_pos (ZMod.val_lt s),
      ZMod.natCast_zmod_val]

/-! ## Decoding one point

`read_point` takes 32 bytes and hands them to `pasta_curves`' `from_bytes`: bit 255 is the parity
of `y`, the low 255 bits must be a canonical `x`, and `y` is the square root of `x³ + 5` with that
parity. -/

/-- The sign bit of a compressed encoding: `2^255`. Named so that the decoders' arithmetic stays
symbolic under `simp`. -/
def signBit : ℕ := 2 ^ 255

/-- The sign bit, unfolded. -/
theorem signBit_eq : signBit = 2 ^ 255 := rfl

/-- The sign bit is a positive divisor. -/
theorem signBit_pos : 0 < signBit := by rw [signBit_eq]; positivity

/-- The Vesta base field fits below the sign bit, so a canonical `x` never sets it. -/
theorem vestaBase_card_lt_signBit : PALLAS_SCALAR_CARD < signBit := by
  rw [signBit_eq]; decide

/-- The parity-matching square root: `r` if its canonical value has parity `ysign`, else `-r`
(`from_bytes`' `conditional_select`). -/
def paritySelect (r : VestaBaseField) (ysign : ℕ) : VestaBaseField :=
  if r.val % 2 = ysign then r else -r

/-- `from_bytes` on exactly 32 bytes, with the identity rejected as the transcript would reject
it. -/
def decodePoint32 (enc : List UInt8) : Option VestaG :=
  if enc.length = 32 then
    if leInt enc % signBit < PALLAS_SCALAR_CARD then
      match vestaBase.sqrt? (((leInt enc % signBit : ℕ) : VestaBaseField) ^ 3
          + Vesta.a * ((leInt enc % signBit : ℕ) : VestaBaseField) + Vesta.b) with
      | none => none
      | some r =>
          if hc : OnCurve Vesta.a Vesta.b (((leInt enc % signBit : ℕ) : VestaBaseField),
              paritySelect r (leInt enc / signBit)) then
            some ⟨_, _, Or.inl hc⟩
          else none
    else none
  else none

/-- The Vesta base field has odd order, so negation flips the parity of a nonzero value. -/
theorem neg_val_parity_ne {r : VestaBaseField} (hr : r ≠ 0) : (-r).val % 2 ≠ r.val % 2 := by
  rw [ZMod.neg_val, if_neg hr]
  have hlt := ZMod.val_lt r
  have hpos : 0 < r.val := Nat.pos_of_ne_zero (fun h => hr ((ZMod.val_eq_zero r).mp h))
  have hodd : PALLAS_SCALAR_CARD % 2 = 1 := by decide
  omega

/-- The selected root has the signalled parity, for a nonzero root and a one-bit sign. -/
theorem paritySelect_val_mod_two {r : VestaBaseField} (hr : r ≠ 0) {ysign : ℕ}
    (hsign : ysign < 2) : (paritySelect r ysign).val % 2 = ysign := by
  unfold paritySelect
  split_ifs with h
  · exact h
  · have := neg_val_parity_ne hr
    omega

/-- A point other than the identity is on the curve. -/
theorem onCurve_of_ne_zero {P : VestaG} (hP : P ≠ 0) : OnCurve Vesta.a Vesta.b (P.x, P.y) := by
  rcases P.onCurve with h | h
  · exact h
  · exact absurd (SWPoint.ext_pair (P := P) (Q := 0) h) hP

/-- A point with a nonzero `x` is not the identity. -/
theorem ne_zero_of_x_ne_zero {P : VestaG} (hx : P.x ≠ 0) : P ≠ 0 := by
  intro h
  exact hx (by rw [h]; rfl)

/-- The radicand `read_point` takes a root of is never zero: `x³ + 5 = 0` has no solution in the
Vesta base field. -/
theorem radicand_ne_zero (x : VestaBaseField) : x ^ 3 + Vesta.a * x + Vesta.b ≠ 0 := by
  intro h
  apply Vesta.neg_five_not_isCube
  refine ⟨x, ?_⟩
  have ha : Vesta.a = 0 := rfl
  have hb : Vesta.b = 5 := rfl
  rw [ha, hb, zero_mul, _root_.add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A nonzero `x` has a nonzero radicand root: `x = 0` would make the radicand `5`, a non-residue. -/
theorem x_ne_zero_of_sqrt {x r : VestaBaseField}
    (h : vestaBase.sqrt? (x ^ 3 + Vesta.a * x + Vesta.b) = some r) : x ≠ 0 := by
  intro hx
  have hrr := Fields.TonelliShanks.sqrt?_mul_self vestaBase h
  rw [hx] at hrr
  apply Vesta.five_not_isSquare
  refine ⟨r, ?_⟩
  have ha : Vesta.a = 0 := rfl
  have hb : Vesta.b = 5 := rfl
  rw [hrr, ha, hb]
  ring

/-- **Canonical point decoding.** Decoding succeeds exactly on the 32-byte compressed encoding of
a non-identity point. -/
theorem decodePoint32_eq_some_iff {enc : List UInt8} {P : VestaG} :
    decodePoint32 enc = some P ↔ P ≠ 0 ∧ enc = (toBytes P).toList := by
  have hq := vestaBase_card_lt_signBit
  constructor
  · intro hd
    unfold decodePoint32 at hd
    split_ifs at hd with h hx
    have hvlt : leInt enc < 2 ^ 256 := leInt_lt_of_length_32 h
    generalize hsq : vestaBase.sqrt? (((leInt enc % signBit : ℕ) : VestaBaseField) ^ 3
        + Vesta.a * ((leInt enc % signBit : ℕ) : VestaBaseField) + Vesta.b) = sq at hd
    cases sq with
    | none => simp at hd
    | some r =>
        simp only at hd
        split_ifs at hd with hc
        simp only [Option.some.injEq] at hd
        subst hd
        have hrr := Fields.TonelliShanks.sqrt?_mul_self vestaBase hsq
        have hr0 : r ≠ 0 := by
          intro hr
          rw [hr, mul_zero] at hrr
          exact radicand_ne_zero _ hrr.symm
        have hxval : (((leInt enc % signBit : ℕ) : VestaBaseField)).val = leInt enc % signBit := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hx
        have hsign : leInt enc / signBit < 2 := by
          apply Nat.div_lt_of_lt_mul
          rw [signBit_eq, ← pow_succ]
          exact hvlt
        refine ⟨ne_zero_of_x_ne_zero (x_ne_zero_of_sqrt hsq), ?_⟩
        refine (toBytes_toList_eq h ?_).symm
        simp only
        rw [hxval, paritySelect_val_mod_two hr0 hsign, ← signBit_eq]
        exact Nat.mod_add_div' (leInt enc) signBit
  · rintro ⟨hP, heq⟩
    rw [heq]
    have hOn := onCurve_of_ne_zero hP
    have hy0 : P.y ≠ 0 := fun hy => Vesta.no_onCurve_y_zero P.x (hy ▸ hOn)
    have hxlt : P.x.val < signBit := lt_trans (ZMod.val_lt P.x) hq
    have hint : leInt (toBytes P).toList = P.x.val + P.y.val % 2 * signBit := by
      rw [leInt_toList, toBytes, LEOS2IP_I2LEOSP_256, signBit_eq]
    have hmod : leInt (toBytes P).toList % signBit = P.x.val := by
      rw [hint, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hxlt
    have hdiv : leInt (toBytes P).toList / signBit = P.y.val % 2 := by
      rw [hint, Nat.add_mul_div_right _ _ signBit_pos, Nat.div_eq_of_lt hxlt, Nat.zero_add]
    unfold decodePoint32
    rw [if_pos (by simp), if_pos (by rw [hmod]; exact ZMod.val_lt P.x)]
    simp only [hmod, hdiv, ZMod.natCast_zmod_val]
    have hyy : P.y * P.y = P.x ^ 3 + Vesta.a * P.x + Vesta.b := by
      have hc : P.y ^ 2 = P.x ^ 3 + Vesta.a * P.x + Vesta.b := hOn
      rw [← hc]
      ring
    obtain ⟨r, hr⟩ := Fields.TonelliShanks.sqrt?_isSome_of_isSquare vestaBase
      (⟨P.y, hyy.symm⟩ : IsSquare (P.x ^ 3 + Vesta.a * P.x + Vesta.b))
    rw [hr]
    simp only
    have hrr := Fields.TonelliShanks.sqrt?_mul_self vestaBase hr
    have hcases : r = P.y ∨ r = -P.y := mul_self_eq_mul_self_iff.mp (hrr.trans hyy.symm)
    have hsel : paritySelect r (P.y.val % 2) = P.y := by
      unfold paritySelect
      rcases hcases with rfl | rfl
      · rw [if_pos rfl]
      · rw [if_neg (neg_val_parity_ne hy0), _root_.neg_neg]
    simp only [hsel]
    rw [dif_pos hOn]

/-- `decodePoint32` rejects 32 bytes whose low 255 bits read at or above the base-field order:
the non-canonical-coordinate branch, stated so the rejection can be shown without rewriting
under the decoder's dependent branches. -/
theorem decodePoint32_eq_none_of_x_ge {enc : List UInt8} (hlen : enc.length = 32)
    (hge : ¬ leInt enc % signBit < PALLAS_SCALAR_CARD) : decodePoint32 enc = none := by
  unfold decodePoint32
  rw [if_pos hlen, if_neg hge]

/-- `decodePoint32` rejects 32 bytes whose curve-equation radicand has no square root: the
no-point branch, stated so the rejection can be shown without rewriting under the decoder's
dependent branches. -/
theorem decodePoint32_eq_none_of_sqrt_none {enc : List UInt8} (hlen : enc.length = 32)
    (hlt : leInt enc % signBit < PALLAS_SCALAR_CARD)
    (hsq : vestaBase.sqrt? (((leInt enc % signBit : ℕ) : VestaBaseField) ^ 3
      + Vesta.a * ((leInt enc % signBit : ℕ) : VestaBaseField) + Vesta.b) = none) :
    decodePoint32 enc = none := by
  unfold decodePoint32
  rw [if_pos hlen, if_pos hlt, hsq]

/-- A square-root routine cannot return a value for a proved non-square. This uses its checked
output equation, not native evaluation of the routine. -/
theorem sqrt?_eq_none_of_not_isSquare {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : Fields.TonelliShanks F) {a : F} (ha : ¬ IsSquare a) : d.sqrt? a = none := by
  cases h : d.sqrt? a with
  | none => rfl
  | some r =>
      exfalso
      exact ha ⟨r, (Fields.TonelliShanks.sqrt?_mul_self d h).symm⟩

/-- The all-zero compressed encoding is rejected: it asks for a point with `x = 0`, for which the
Vesta curve equation has no solution. -/
theorem decodePoint32_zero_eq_none :
    decodePoint32 (List.replicate 32 0) = none := by
  have hsqrt : vestaBase.sqrt? (5 : VestaBaseField) = none :=
    sqrt?_eq_none_of_not_isSquare vestaBase Vesta.five_not_isSquare
  have h0 : leInt (List.replicate 32 0) % signBit = 0 := by
    rw [leInt_replicate_zero, Nat.zero_mod]
  refine decodePoint32_eq_none_of_sqrt_none (by simp) ?_ ?_
  · rw [h0]
    norm_num [PALLAS_SCALAR_CARD]
  · rw [h0]
    simpa [Vesta.a, Vesta.b] using hsqrt

/-- Encoding the base-field modulus as a compressed `x` is rejected as non-canonical. -/
theorem decodePoint32_baseModulus_eq_none :
    decodePoint32
      (List.ofFn fun i : Fin 32 =>
        UInt8.ofNat (PALLAS_SCALAR_CARD / 256 ^ i.val % 256)) = none := by
  have hq256 : PALLAS_SCALAR_CARD < 2 ^ 256 := by
    exact lt_trans vestaBase_card_lt_signBit (by norm_num [signBit])
  have hle :
      leInt (List.ofFn fun i : Fin 32 =>
        UInt8.ofNat (PALLAS_SCALAR_CARD / 256 ^ i.val % 256)) = PALLAS_SCALAR_CARD := by
    simpa using leInt_ofFn_32 ⟨PALLAS_SCALAR_CARD, hq256⟩
  refine decodePoint32_eq_none_of_x_ge (by simp) ?_
  rw [hle, Nat.mod_eq_of_lt vestaBase_card_lt_signBit]
  exact Nat.lt_irrefl _

/-- `13` is a quadratic non-residue in the Vesta base field. -/
theorem thirteen_not_isSquare : ¬ IsSquare (13 : VestaBaseField) := by
  rw [ZMod.euler_criterion PALLAS_SCALAR_CARD (by decide : (13 : VestaBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- The compressed encoding with `x = 2` is rejected because its curve-equation radicand is the
non-residue `13`. -/
theorem decodePoint32_two_eq_none :
    decodePoint32 (2 :: List.replicate 31 0) = none := by
  have hsqrt : vestaBase.sqrt? (13 : VestaBaseField) = none :=
    sqrt?_eq_none_of_not_isSquare vestaBase thirteen_not_isSquare
  have h2 : leInt (2 :: List.replicate 31 0) % signBit = 2 := by
    rw [show leInt (2 :: List.replicate 31 0) = 2 by decide]
    exact Nat.mod_eq_of_lt (by norm_num [signBit_eq])
  refine decodePoint32_eq_none_of_sqrt_none (by simp) ?_ ?_
  · rw [h2]
    norm_num [PALLAS_SCALAR_CARD]
  · rw [h2]
    have : (((2 : ℕ) : VestaBaseField)) ^ 3 + Vesta.a * ((2 : ℕ) : VestaBaseField) + Vesta.b
        = 13 := by
      have ha : Vesta.a = 0 := rfl
      have hb : Vesta.b = 5 := rfl
      rw [ha, hb]
      norm_num
    rw [this]
    exact hsqrt

/-! ## Stream readers -/

-- Decidable equality on the typed proof, so a decoded proof can be compared with a captured one:
-- every field is a finite function into a type with decidable equality.
deriving instance DecidableEq for PermSetEval, LookupEval, ProofString

/-- A reader over the proof bytes: consume a prefix and return the value with the remainder, or
reject. -/
abbrev ProofReader := StateT (List UInt8) Option

/-- Take 32 bytes from the stream and decode them; fewer than 32 bytes is a truncated proof. -/
def read32 {α : Type} (decode : List UInt8 → Option α) : ProofReader α := fun bs =>
  if 32 ≤ bs.length then (decode (bs.take 32)).map fun x => (x, bs.drop 32) else none

/-- halo2 `read_scalar`. -/
def scalarReader : ProofReader Fp := read32 decodeScalar32

/-- halo2 `read_point`. -/
def pointReader : ProofReader VestaG := read32 decodePoint32

/-- A 32-byte decoder that succeeds exactly on an encoder's output reads exactly that output. -/
theorem read32_eq_some_iff {α : Type} {decode : List UInt8 → Option α} {enc : α → List UInt8}
    (hlen : ∀ x, (enc x).length = 32)
    (hiff : ∀ e x, e.length = 32 → (decode e = some x ↔ e = enc x))
    {bs : List UInt8} {x : α} {rest : List UInt8} :
    (read32 decode).run bs = some (x, rest) ↔ bs = enc x ++ rest := by
  constructor
  · intro h
    unfold read32 at h
    simp only [StateT.run] at h
    split_ifs at h with h32
    obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    have htake : (bs.take 32).length = 32 := by simp [List.length_take, h32]
    conv_lhs => rw [← List.take_append_drop 32 bs]
    rw [(hiff _ _ htake).mp hy]
  · rintro rfl
    unfold read32
    simp only [StateT.run]
    rw [if_pos (by simp [hlen]), List.take_left' (hlen x), List.drop_left' (hlen x),
      (hiff _ _ (hlen x)).mpr rfl]
    rfl

/-- `read_scalar` succeeds exactly on `write_scalar`'s output followed by the remainder. -/
theorem scalarReader_eq_some_iff {bs : List UInt8} {s : Fp} {rest : List UInt8} :
    scalarReader.run bs = some (s, rest) ↔ bs = (scalarRepr s).toList ++ rest :=
  read32_eq_some_iff (fun _ => by simp) (fun _ _ _ => decodeScalar32_eq_some_iff)

/-- `read_point` succeeds exactly on `write_point`'s output for a non-identity point followed by
the remainder. -/
theorem pointReader_eq_some_iff {bs : List UInt8} {P : VestaG} {rest : List UInt8} :
    pointReader.run bs = some (P, rest) ↔ P ≠ 0 ∧ bs = (toBytes P).toList ++ rest := by
  constructor
  · intro h
    unfold pointReader read32 at h
    simp only [StateT.run] at h
    split_ifs at h with h32
    obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    have htake : (bs.take 32).length = 32 := by simp [List.length_take, h32]
    obtain ⟨hP, henc⟩ := decodePoint32_eq_some_iff.mp hy
    refine ⟨hP, ?_⟩
    conv_lhs => rw [← List.take_append_drop 32 bs]
    rw [henc]
  · rintro ⟨hP, heq⟩
    rw [heq]
    unfold pointReader read32
    simp only [StateT.run]
    have hlen : (toBytes P).toList.length = 32 := by simp
    rw [if_pos (by simp), List.take_left' hlen, List.drop_left' hlen,
      decodePoint32_eq_some_iff.mpr ⟨hP, rfl⟩]
    rfl

/-- If the first 32-byte point encoding is rejected, appending any stream suffix cannot make that
point read succeed. -/
theorem pointReader_eq_none_of_prefix {enc rest : List UInt8} (hlen : enc.length = 32)
    (hdecode : decodePoint32 enc = none) : pointReader.run (enc ++ rest) = none := by
  unfold pointReader read32
  simp only [StateT.run]
  rw [if_pos (by simp [hlen]), List.take_left' hlen, hdecode]
  rfl

/-- Read `n` elements in index order, the reader at index `i` producing element `i`. -/
def readVec {α : Type} : (n : ℕ) → (Fin n → ProofReader α) → ProofReader (Fin n → α)
  | 0, _ => pure (fun i => i.elim0)
  | n + 1, r => do
      let x ← r 0
      let rest ← readVec n (fun i => r i.succ)
      pure (Fin.cons x rest)

/-- The bytes of `n` elements in index order under a per-index encoder. -/
def serializeVec {α : Type} (n : ℕ) (enc : Fin n → α → List UInt8) (f : Fin n → α) :
    List UInt8 :=
  (List.ofFn fun i => enc i (f i)).flatten

/-- No elements serialize to no bytes. -/
@[simp] theorem serializeVec_zero {α : Type} (enc : Fin 0 → α → List UInt8) (f : Fin 0 → α) :
    serializeVec 0 enc f = [] := by
  simp [serializeVec]

/-- Element `0` is written first, then the rest in order. -/
theorem serializeVec_succ {α : Type} (n : ℕ) (enc : Fin (n + 1) → α → List UInt8)
    (f : Fin (n + 1) → α) :
    serializeVec (n + 1) enc f
      = enc 0 (f 0) ++ serializeVec n (fun i => enc i.succ) (fun i => f i.succ) := by
  simp [serializeVec, List.ofFn_succ]

/-- **Vector round trip.** Readers that read back their encoders read a serialized vector back. -/
theorem readVec_serializeVec {α : Type} (n : ℕ) (r : Fin n → ProofReader α)
    (enc : Fin n → α → List UInt8)
    (h : ∀ i x rest, (r i).run (enc i x ++ rest) = some (x, rest))
    (f : Fin n → α) (rest : List UInt8) :
    (readVec n r).run (serializeVec n enc f ++ rest) = some (f, rest) := by
  induction n generalizing rest with
  | zero =>
      simp only [readVec, serializeVec_zero, List.nil_append, StateT.run_pure, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq, and_true]
      funext i
      exact i.elim0
  | succ n ih =>
      rw [serializeVec_succ, List.append_assoc]
      simp only [readVec, StateT.run_bind, h, Option.bind_eq_bind, Option.bind_some]
      rw [ih (fun i => r i.succ) (fun i => enc i.succ) (fun i x rest => h i.succ x rest)]
      simp only [Option.bind_some, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq, and_true]
      exact Fin.cons_self_tail f

/-- **Vector canonicality.** Readers that succeed only on their encoders make a successful vector
read the serialization of what it returns. -/
theorem readVec_eq_some {α : Type} (n : ℕ) (r : Fin n → ProofReader α)
    (enc : Fin n → α → List UInt8)
    (h : ∀ i x bs rest, (r i).run bs = some (x, rest) → bs = enc i x ++ rest)
    (f : Fin n → α) (bs rest : List UInt8)
    (hread : (readVec n r).run bs = some (f, rest)) :
    bs = serializeVec n enc f ++ rest := by
  induction n generalizing bs rest with
  | zero =>
      simp only [readVec, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hread
      simp [hread.2]
  | succ n ih =>
      simp only [readVec, StateT.run_bind, Option.bind_eq_bind] at hread
      obtain ⟨⟨x, bs₁⟩, hx, hrest⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨⟨g, bs₂⟩, hg, hpure⟩ := Option.bind_eq_some_iff.mp hrest
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      rw [serializeVec_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [List.append_assoc, h 0 x bs bs₁ hx]
      congr 1
      exact ih (fun i => r i.succ) (fun i => enc i.succ) (fun i x bs rest => h i.succ x bs rest)
        g bs₁ _ hg

/-- Read `m × n` elements proof-major: for each proof, its `n` elements. -/
def readGrid {α : Type} (m n : ℕ) (r : ProofReader α) : ProofReader (Fin m → Fin n → α) :=
  readVec m fun _ => readVec n fun _ => r

/-- A nonempty proof-major grid fails immediately when its first element reader fails. -/
theorem readGrid_eq_none_of_first {α : Type} {m n : ℕ} {r : ProofReader α}
    {bs : List UInt8} (h : r.run bs = none) :
    (readGrid (m + 1) (n + 1) r).run bs = none := by
  simp [readGrid, readVec, h]

/-- The nonempty-grid failure at counts only known nonzero, so a caller need not rewrite a
shape's projections into successor form inside the reader's dependent type. -/
theorem readGrid_eq_none_of_first_of_ne_zero {α : Type} {m n : ℕ} {r : ProofReader α}
    {bs : List UInt8} (hm : m ≠ 0) (hn : n ≠ 0) (h : r.run bs = none) :
    (readGrid m n r).run bs = none := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact readGrid_eq_none_of_first h

/-- The bytes of `m × n` elements proof-major. -/
def serializeGrid {α : Type} (m n : ℕ) (enc : α → List UInt8) (f : Fin m → Fin n → α) :
    List UInt8 :=
  serializeVec m (fun _ g => serializeVec n (fun _ => enc) g) f

/-- **Grid canonicality.** A successful proof-major grid read reconstructs its consumed bytes. -/
theorem readGrid_eq_some {α : Type} (m n : ℕ) (r : ProofReader α)
    (enc : α → List UInt8)
    (h : ∀ x bs rest, r.run bs = some (x, rest) → bs = enc x ++ rest)
    (f : Fin m → Fin n → α) (bs rest : List UInt8)
    (hread : (readGrid m n r).run bs = some (f, rest)) :
    bs = serializeGrid m n enc f ++ rest := by
  exact readVec_eq_some m (fun _ => readVec n fun _ => r)
    (fun _ g => serializeVec n (fun _ => enc) g)
    (fun _ g input output hg =>
      readVec_eq_some n (fun _ => r) (fun _ => enc)
        (fun _ x input output hx => h x input output hx) g input output hg)
    f bs rest hread

/-- Read two points in sequence. -/
def pointPairReader : ProofReader (VestaG × VestaG) := do
  let first ← pointReader
  let second ← pointReader
  pure (first, second)

/-- Serialize two compressed points in sequence. -/
def serializePointPair (points : VestaG × VestaG) : List UInt8 :=
  (toBytes points.1).toList ++ (toBytes points.2).toList

/-- **Point-pair canonicality.** A successful pair read reconstructs its consumed bytes. -/
theorem pointPairReader_eq_some {bs rest : List UInt8} {points : VestaG × VestaG}
    (hread : pointPairReader.run bs = some (points, rest)) :
    bs = serializePointPair points ++ rest := by
  simp only [pointPairReader, StateT.run_bind, Option.bind_eq_bind] at hread
  obtain ⟨⟨first, bs₁⟩, hfirst, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨⟨second, bs₂⟩, hsecond, hpure⟩ := Option.bind_eq_some_iff.mp hread
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change pointReader.run bs₁ = some (second, bs₂) at hsecond
  rw [(pointReader_eq_some_iff.mp hfirst).2, (pointReader_eq_some_iff.mp hsecond).2]
  simp only [serializePointPair, List.append_assoc]

/-- Read one permutation set's evaluations: `eval`, `nextEval`, and `lastEval` exactly when the set
is not the last (halo2 `permutation::verifier::Committed::evaluate`). -/
def permSetReader (hasLast : Bool) : ProofReader (PermSetEval Fp) := do
  let eval ← scalarReader
  let nextEval ← scalarReader
  if hasLast then do
    let lastEval ← scalarReader
    pure { eval, nextEval, lastEval := some lastEval }
  else
    pure { eval, nextEval, lastEval := none }

/-- The bytes of one permutation set's evaluations. -/
def serializePermSet (e : PermSetEval Fp) : List UInt8 :=
  (scalarRepr e.eval).toList ++ (scalarRepr e.nextEval).toList
    ++ (e.lastEval.map fun s => (scalarRepr s).toList).getD []

/-- **Permutation-set canonicality.** A successful shape-directed read reconstructs exactly the
bytes selected by its returned `lastEval`. -/
theorem permSetReader_eq_some {hasLast : Bool} {bs rest : List UInt8} {e : PermSetEval Fp}
    (hread : (permSetReader hasLast).run bs = some (e, rest)) :
    bs = serializePermSet e ++ rest := by
  cases hasLast with
  | false =>
      simp only [permSetReader, StateT.run_bind, Option.bind_eq_bind, Bool.false_eq_true,
        if_false] at hread
      obtain ⟨⟨eval, bs₁⟩, heval, hread⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨⟨nextEval, bs₂⟩, hnext, hpure⟩ := Option.bind_eq_some_iff.mp hread
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      change scalarReader.run bs₁ = some (nextEval, bs₂) at hnext
      rw [scalarReader_eq_some_iff.mp heval, scalarReader_eq_some_iff.mp hnext]
      simp only [serializePermSet, Option.map_none, Option.getD_none, List.append_nil,
        List.append_assoc]
  | true =>
      simp only [permSetReader, StateT.run_bind, Option.bind_eq_bind, if_true] at hread
      obtain ⟨⟨eval, bs₁⟩, heval, hread⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨⟨nextEval, bs₂⟩, hnext, hread⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨⟨lastEval, bs₃⟩, hlast, hpure⟩ := Option.bind_eq_some_iff.mp hread
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      change scalarReader.run bs₁ = some (nextEval, bs₂) at hnext
      change scalarReader.run bs₂ = some (lastEval, bs₃) at hlast
      rw [scalarReader_eq_some_iff.mp heval, scalarReader_eq_some_iff.mp hnext,
        scalarReader_eq_some_iff.mp hlast]
      simp only [serializePermSet, Option.map_some, Option.getD_some, List.append_assoc]

/-- Read one lookup's five evaluations in halo2's order. -/
def lookupReader : ProofReader (LookupEval Fp) := do
  let productEval ← scalarReader
  let productNextEval ← scalarReader
  let permutedInputEval ← scalarReader
  let permutedInputInvEval ← scalarReader
  let permutedTableEval ← scalarReader
  pure { productEval, productNextEval, permutedInputEval, permutedInputInvEval, permutedTableEval }

/-- The bytes of one lookup's five evaluations. -/
def serializeLookup (e : LookupEval Fp) : List UInt8 :=
  (scalarRepr e.productEval).toList ++ (scalarRepr e.productNextEval).toList
    ++ (scalarRepr e.permutedInputEval).toList ++ (scalarRepr e.permutedInputInvEval).toList
    ++ (scalarRepr e.permutedTableEval).toList

/-- **Lookup canonicality.** A successful lookup read reconstructs its five scalar encodings. -/
theorem lookupReader_eq_some {bs rest : List UInt8} {e : LookupEval Fp}
    (hread : lookupReader.run bs = some (e, rest)) :
    bs = serializeLookup e ++ rest := by
  simp only [lookupReader, StateT.run_bind, Option.bind_eq_bind] at hread
  obtain ⟨⟨productEval, bs₁⟩, hproduct, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨⟨productNextEval, bs₂⟩, hproductNext, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  obtain ⟨⟨permutedInputEval, bs₃⟩, hinput, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨⟨permutedInputInvEval, bs₄⟩, hinputInv, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  obtain ⟨⟨permutedTableEval, bs₅⟩, htable, hpure⟩ := Option.bind_eq_some_iff.mp hread
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change scalarReader.run bs₁ = some (productNextEval, bs₂) at hproductNext
  change scalarReader.run bs₂ = some (permutedInputEval, bs₃) at hinput
  change scalarReader.run bs₃ = some (permutedInputInvEval, bs₄) at hinputInv
  change scalarReader.run bs₄ = some (permutedTableEval, bs₅) at htable
  rw [scalarReader_eq_some_iff.mp hproduct, scalarReader_eq_some_iff.mp hproductNext,
    scalarReader_eq_some_iff.mp hinput, scalarReader_eq_some_iff.mp hinputInv,
    scalarReader_eq_some_iff.mp htable]
  simp only [serializeLookup, List.append_assoc]

/-- The compressed bytes of a point (`write_point`). -/
def pointBytesCompressed (P : VestaG) : List UInt8 := (toBytes P).toList

/-- The bytes of a scalar (`write_scalar`). -/
def scalarBytesRaw (s : Fp) : List UInt8 := (scalarRepr s).toList

/-- halo2 `verify_proof`'s reads, in order: the proof string as the deployed verifier parses it.
Squeezes consume no bytes, so this is `deriveChallenges`' absorb order restricted to proof reads,
with the two IPA scalars `c` and `f` read after the last squeeze. -/
def readProof? (shape : Shape) : ProofReader (ProofString shape Fp VestaG) := do
  let adviceCommitments ← readGrid shape.numProofs shape.numAdviceColumns pointReader
  let lookupPermuted ← readGrid shape.numProofs shape.numLookups pointPairReader
  let permutationProduct ← readGrid shape.numProofs shape.numPermutationSets pointReader
  let lookupProduct ← readGrid shape.numProofs shape.numLookups pointReader
  let vanishingRandom ← pointReader
  let hPieces ← readVec shape.numQuotientPieces fun _ => pointReader
  let instanceEvals ← readGrid shape.numProofs shape.numInstanceQueries scalarReader
  let adviceEvals ← readGrid shape.numProofs shape.numAdviceQueries scalarReader
  let fixedEvals ← readVec shape.numFixedQueries fun _ => scalarReader
  let vanishingRandomEval ← scalarReader
  let permutationCommonEvals ← readVec shape.numPermutationColumns fun _ => scalarReader
  let permutationSetEvals ← readVec shape.numProofs fun _ =>
    readVec shape.numPermutationSets fun s =>
      permSetReader (decide (s.val + 1 < shape.numPermutationSets))
  let lookupEvals ← readGrid shape.numProofs shape.numLookups lookupReader
  let multiopenQPrime ← pointReader
  let multiopenU ← readVec shape.numPointSets fun _ => scalarReader
  let ipaS ← pointReader
  let ipaRounds ← readVec shape.k fun _ => pointPairReader
  let ipaC ← scalarReader
  let ipaF ← scalarReader
  pure {
    adviceCommitments
    lookupPermutedInput := fun p l => (lookupPermuted p l).1
    lookupPermutedTable := fun p l => (lookupPermuted p l).2
    permutationProduct
    lookupProduct
    vanishingRandom
    hPieces
    instanceEvals
    adviceEvals
    fixedEvals
    vanishingRandomEval
    permutationCommonEvals
    permutationSetEvals
    lookupEvals
    multiopenQPrime
    multiopenU
    ipaS
    ipaRounds
    ipaC
    ipaF }

/-- A proof with at least one proof and one advice column fails when its leading compressed point
fails. This lifts element rejection without evaluating the rest of a captured proof. -/
theorem readProof?_eq_none_of_first_point {shape : Shape} {bs : List UInt8}
    (hproofs : shape.numProofs ≠ 0) (hadvice : shape.numAdviceColumns ≠ 0)
    (hpoint : pointReader.run bs = none) : (readProof? shape).run bs = none := by
  unfold readProof?
  simp only [StateT.run_bind]
  rw [readGrid_eq_none_of_first_of_ne_zero hproofs hadvice hpoint]
  rfl

/-- The prover's byte string for a typed proof: `write_point`/`write_scalar` in `readProof?`'s
order. The deployed verifier ignores trailing bytes; the consensus rules fix the proof length
(ZIP 225: `2720 + 2272 · nActionsOrchard`), so a proof of the right length either parses exactly or
is rejected, which is the form the capture checks state. -/
def serializeProof {shape : Shape} (ps : ProofString shape Fp VestaG) : List UInt8 :=
  serializeGrid shape.numProofs shape.numAdviceColumns pointBytesCompressed ps.adviceCommitments
    ++ serializeGrid shape.numProofs shape.numLookups serializePointPair
        (fun p l => (ps.lookupPermutedInput p l, ps.lookupPermutedTable p l))
    ++ serializeGrid shape.numProofs shape.numPermutationSets pointBytesCompressed
        ps.permutationProduct
    ++ serializeGrid shape.numProofs shape.numLookups pointBytesCompressed ps.lookupProduct
    ++ pointBytesCompressed ps.vanishingRandom
    ++ serializeVec shape.numQuotientPieces (fun _ => pointBytesCompressed) ps.hPieces
    ++ serializeGrid shape.numProofs shape.numInstanceQueries scalarBytesRaw ps.instanceEvals
    ++ serializeGrid shape.numProofs shape.numAdviceQueries scalarBytesRaw ps.adviceEvals
    ++ serializeVec shape.numFixedQueries (fun _ => scalarBytesRaw) ps.fixedEvals
    ++ scalarBytesRaw ps.vanishingRandomEval
    ++ serializeVec shape.numPermutationColumns (fun _ => scalarBytesRaw)
        ps.permutationCommonEvals
    ++ serializeGrid shape.numProofs shape.numPermutationSets serializePermSet
        ps.permutationSetEvals
    ++ serializeGrid shape.numProofs shape.numLookups serializeLookup ps.lookupEvals
    ++ pointBytesCompressed ps.multiopenQPrime
    ++ serializeVec shape.numPointSets (fun _ => scalarBytesRaw) ps.multiopenU
    ++ pointBytesCompressed ps.ipaS
    ++ serializeVec shape.k (fun _ => serializePointPair) ps.ipaRounds
    ++ scalarBytesRaw ps.ipaC
    ++ scalarBytesRaw ps.ipaF

/-- **Whole-proof canonicality.** Every successful deployed-order parse reconstructs exactly the
bytes it consumed, followed by the unread suffix.

This direction is intentionally the public contract. An arbitrary typed `ProofString` can contain
identity points or a permutation `lastEval` with the wrong shape, so `serializeProof` is total but
need not produce an accepted byte string for every typed input. -/
theorem readProof?_eq_some_serialize {shape : Shape} {bs rest : List UInt8}
    {ps : ProofString shape Fp VestaG}
    (hread : (readProof? shape).run bs = some (ps, rest)) :
    bs = serializeProof ps ++ rest := by
  unfold readProof? at hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceCommitments, bs₁⟩, hadviceCommitments, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupPermuted, bs₂⟩, hlookupPermuted, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationProduct, bs₃⟩, hpermutationProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupProduct, bs₄⟩, hlookupProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandom, bs₅⟩, hvanishingRandom, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨hPieces, bs₆⟩, hhPieces, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨instanceEvals, bs₇⟩, hinstanceEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceEvals, bs₈⟩, hadviceEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨fixedEvals, bs₉⟩, hfixedEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandomEval, bs₁₀⟩, hvanishingRandomEval, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationCommonEvals, bs₁₁⟩, hpermutationCommonEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationSetEvals, bs₁₂⟩, hpermutationSetEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupEvals, bs₁₃⟩, hlookupEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenQPrime, bs₁₄⟩, hmultiopenQPrime, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenU, bs₁₅⟩, hmultiopenU, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaS, bs₁₆⟩, hipaS, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaRounds, bs₁₇⟩, hipaRounds, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaC, bs₁₈⟩, hipaC, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaF, bs₁₉⟩, hipaF, hpure⟩ := Option.bind_eq_some_iff.mp hread
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change (readGrid shape.numProofs shape.numLookups pointPairReader).run bs₁ =
    some (lookupPermuted, bs₂) at hlookupPermuted
  change (readGrid shape.numProofs shape.numPermutationSets pointReader).run bs₂ =
    some (permutationProduct, bs₃) at hpermutationProduct
  change (readGrid shape.numProofs shape.numLookups pointReader).run bs₃ =
    some (lookupProduct, bs₄) at hlookupProduct
  change pointReader.run bs₄ = some (vanishingRandom, bs₅) at hvanishingRandom
  change (readVec shape.numQuotientPieces fun _ => pointReader).run bs₅ =
    some (hPieces, bs₆) at hhPieces
  change (readGrid shape.numProofs shape.numInstanceQueries scalarReader).run bs₆ =
    some (instanceEvals, bs₇) at hinstanceEvals
  change (readGrid shape.numProofs shape.numAdviceQueries scalarReader).run bs₇ =
    some (adviceEvals, bs₈) at hadviceEvals
  change (readVec shape.numFixedQueries fun _ => scalarReader).run bs₈ =
    some (fixedEvals, bs₉) at hfixedEvals
  change scalarReader.run bs₉ = some (vanishingRandomEval, bs₁₀) at hvanishingRandomEval
  change (readVec shape.numPermutationColumns fun _ => scalarReader).run bs₁₀ =
    some (permutationCommonEvals, bs₁₁) at hpermutationCommonEvals
  change (readVec shape.numProofs fun _ =>
    readVec shape.numPermutationSets fun s =>
      permSetReader (decide (s.val + 1 < shape.numPermutationSets))).run bs₁₁ =
    some (permutationSetEvals, bs₁₂) at hpermutationSetEvals
  change (readGrid shape.numProofs shape.numLookups lookupReader).run bs₁₂ =
    some (lookupEvals, bs₁₃) at hlookupEvals
  change pointReader.run bs₁₃ = some (multiopenQPrime, bs₁₄) at hmultiopenQPrime
  change (readVec shape.numPointSets fun _ => scalarReader).run bs₁₄ =
    some (multiopenU, bs₁₅) at hmultiopenU
  change pointReader.run bs₁₅ = some (ipaS, bs₁₆) at hipaS
  change (readVec shape.k fun _ => pointPairReader).run bs₁₆ =
    some (ipaRounds, bs₁₇) at hipaRounds
  change scalarReader.run bs₁₇ = some (ipaC, bs₁₈) at hipaC
  change scalarReader.run bs₁₈ = some (ipaF, bs₁₉) at hipaF
  have hadviceCommitmentBytes := readGrid_eq_some shape.numProofs shape.numAdviceColumns
    pointReader pointBytesCompressed
    (fun x input output hx => (pointReader_eq_some_iff.mp hx).2)
    adviceCommitments bs bs₁ hadviceCommitments
  have hlookupPermutedBytes := readGrid_eq_some shape.numProofs shape.numLookups
    pointPairReader serializePointPair
    (fun _ input output hx => pointPairReader_eq_some hx)
    lookupPermuted bs₁ bs₂ hlookupPermuted
  have hpermutationProductBytes := readGrid_eq_some shape.numProofs shape.numPermutationSets
    pointReader pointBytesCompressed
    (fun x input output hx => (pointReader_eq_some_iff.mp hx).2)
    permutationProduct bs₂ bs₃ hpermutationProduct
  have hlookupProductBytes := readGrid_eq_some shape.numProofs shape.numLookups
    pointReader pointBytesCompressed
    (fun x input output hx => (pointReader_eq_some_iff.mp hx).2)
    lookupProduct bs₃ bs₄ hlookupProduct
  have hvanishingRandomBytes := (pointReader_eq_some_iff.mp hvanishingRandom).2
  have hhPieceBytes := readVec_eq_some shape.numQuotientPieces (fun _ => pointReader)
    (fun _ => pointBytesCompressed)
    (fun _ x input output hx => (pointReader_eq_some_iff.mp hx).2)
    hPieces bs₅ bs₆ hhPieces
  have hinstanceEvalBytes := readGrid_eq_some shape.numProofs shape.numInstanceQueries
    scalarReader scalarBytesRaw
    (fun _ input output hx => scalarReader_eq_some_iff.mp hx)
    instanceEvals bs₆ bs₇ hinstanceEvals
  have hadviceEvalBytes := readGrid_eq_some shape.numProofs shape.numAdviceQueries
    scalarReader scalarBytesRaw
    (fun _ input output hx => scalarReader_eq_some_iff.mp hx)
    adviceEvals bs₇ bs₈ hadviceEvals
  have hfixedEvalBytes := readVec_eq_some shape.numFixedQueries (fun _ => scalarReader)
    (fun _ => scalarBytesRaw)
    (fun _ _ input output hx => scalarReader_eq_some_iff.mp hx)
    fixedEvals bs₈ bs₉ hfixedEvals
  have hvanishingRandomEvalBytes := scalarReader_eq_some_iff.mp hvanishingRandomEval
  have hpermutationCommonEvalBytes := readVec_eq_some shape.numPermutationColumns
    (fun _ => scalarReader) (fun _ => scalarBytesRaw)
    (fun _ _ input output hx => scalarReader_eq_some_iff.mp hx)
    permutationCommonEvals bs₁₀ bs₁₁ hpermutationCommonEvals
  have hpermutationSetEvalBytes :
      bs₁₁ = serializeGrid shape.numProofs shape.numPermutationSets serializePermSet
        permutationSetEvals ++ bs₁₂ := by
    unfold serializeGrid
    exact readVec_eq_some shape.numProofs
      (fun _ => readVec shape.numPermutationSets fun s =>
        permSetReader (decide (s.val + 1 < shape.numPermutationSets)))
      (fun _ g => serializeVec shape.numPermutationSets (fun _ => serializePermSet) g)
      (fun _ g input output hg =>
        readVec_eq_some shape.numPermutationSets
          (fun s => permSetReader (decide (s.val + 1 < shape.numPermutationSets)))
          (fun _ => serializePermSet)
          (fun _ _ input output hx => permSetReader_eq_some hx)
          g input output hg)
      permutationSetEvals bs₁₁ bs₁₂ hpermutationSetEvals
  have hlookupEvalBytes := readGrid_eq_some shape.numProofs shape.numLookups
    lookupReader serializeLookup
    (fun _ input output hx => lookupReader_eq_some hx)
    lookupEvals bs₁₂ bs₁₃ hlookupEvals
  have hmultiopenQPrimeBytes := (pointReader_eq_some_iff.mp hmultiopenQPrime).2
  have hmultiopenUBytes := readVec_eq_some shape.numPointSets (fun _ => scalarReader)
    (fun _ => scalarBytesRaw)
    (fun _ _ input output hx => scalarReader_eq_some_iff.mp hx)
    multiopenU bs₁₄ bs₁₅ hmultiopenU
  have hipaSBytes := (pointReader_eq_some_iff.mp hipaS).2
  have hipaRoundBytes := readVec_eq_some shape.k (fun _ => pointPairReader)
    (fun _ => serializePointPair)
    (fun _ _ input output hx => pointPairReader_eq_some hx)
    ipaRounds bs₁₆ bs₁₇ hipaRounds
  have hipaCBytes := scalarReader_eq_some_iff.mp hipaC
  have hipaFBytes := scalarReader_eq_some_iff.mp hipaF
  have hlookupPermutedEta :
      (fun p l => ((lookupPermuted p l).1, (lookupPermuted p l).2)) = lookupPermuted := by
    funext p l
    exact Prod.eta _
  rw [hadviceCommitmentBytes, hlookupPermutedBytes, hpermutationProductBytes,
    hlookupProductBytes, hvanishingRandomBytes, hhPieceBytes, hinstanceEvalBytes,
    hadviceEvalBytes, hfixedEvalBytes, hvanishingRandomEvalBytes,
    hpermutationCommonEvalBytes, hpermutationSetEvalBytes, hlookupEvalBytes,
    hmultiopenQPrimeBytes, hmultiopenUBytes, hipaSBytes, hipaRoundBytes, hipaCBytes,
    hipaFBytes]
  simp only [serializeProof, pointBytesCompressed, scalarBytesRaw, hlookupPermutedEta,
    List.append_assoc]

/-- Exact parsing is the empty-suffix form of whole-proof canonicality. -/
theorem serializeProof_eq_of_readProof?_eq_some {shape : Shape} {bs : List UInt8}
    {ps : ProofString shape Fp VestaG}
    (hread : (readProof? shape).run bs = some (ps, [])) :
    serializeProof ps = bs := by
  simpa using (readProof?_eq_some_serialize hread).symm

/-! ## Byte accounting

Every element `readProof?` reads is exactly 32 bytes, and the element counts are shape
constants, so a successful parse consumed a byte count fixed by the shape alone —
`proofLength`. `readProof?_length` states that accounting. It is what ties a captured proof
string's length to the consensus proof size (ZIP 225: `2720 + 2272 · nActionsOrchard`), and it
rejects any parse of a truncated proof by arithmetic, with no evaluation of the decoder over
the truncated bytes. -/

/-- Any successful 32-byte element read consumed exactly 32 bytes. -/
theorem read32_length {α : Type} {decode : List UInt8 → Option α} {bs rest : List UInt8} {x : α}
    (h : (read32 decode).run bs = some (x, rest)) : bs.length = 32 + rest.length := by
  unfold read32 at h
  simp only [StateT.run] at h
  split_ifs at h with h32
  obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  simp only [List.length_drop]
  omega

/-- A successful vector read consumed the sum of its element reads' costs. -/
theorem readVec_length {α : Type} :
    ∀ (n : ℕ) (r : Fin n → ProofReader α) (c : Fin n → ℕ),
      (∀ i x bs rest, (r i).run bs = some (x, rest) → bs.length = c i + rest.length) →
      ∀ {bs rest : List UInt8} {f : Fin n → α},
        (readVec n r).run bs = some (f, rest) → bs.length = (List.ofFn c).sum + rest.length
  | 0, _, _, _, bs, rest, _, h => by
      simp only [readVec, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      simp [h.2]
  | n + 1, r, c, hc, bs, rest, f, h => by
      simp only [readVec, StateT.run_bind, Option.bind_eq_bind] at h
      obtain ⟨⟨x, bs₁⟩, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨g, bs₂⟩, hg, hpure⟩ := Option.bind_eq_some_iff.mp h
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      have hg' : (readVec n fun i => r i.succ).run bs₁ = some (g, bs₂) := hg
      have h1 := hc 0 x bs bs₁ hx
      have h2 := readVec_length n (fun i => r i.succ) (fun i => c i.succ)
        (fun i x bs rest hr => hc i.succ x bs rest hr) hg'
      have hsum : (List.ofFn c).sum = c 0 + (List.ofFn fun i => c i.succ).sum := by
        rw [List.ofFn_succ, List.sum_cons]
      omega

/-- The sum of `n` copies of one cost. -/
private theorem sum_replicate_nat (n c : ℕ) : (List.replicate n c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

/-- A vector of same-cost element reads consumed `n · c` bytes. -/
theorem readVec_length_const {α : Type} {n : ℕ} {r : Fin n → ProofReader α} {c : ℕ}
    (hc : ∀ i x bs rest, (r i).run bs = some (x, rest) → bs.length = c + rest.length)
    {bs rest : List UInt8} {f : Fin n → α}
    (h : (readVec n r).run bs = some (f, rest)) : bs.length = n * c + rest.length := by
  have := readVec_length n r (fun _ => c) hc h
  rwa [List.ofFn_const, sum_replicate_nat] at this

/-- A successful grid read of same-cost elements consumed `m · (n · c)` bytes. -/
theorem readGrid_length {α : Type} {m n : ℕ} {r : ProofReader α} {c : ℕ}
    (hc : ∀ x bs rest, r.run bs = some (x, rest) → bs.length = c + rest.length)
    {bs rest : List UInt8} {f : Fin m → Fin n → α}
    (h : (readGrid m n r).run bs = some (f, rest)) : bs.length = m * (n * c) + rest.length :=
  readVec_length_const
    (fun _ _ _ _ hg =>
      readVec_length_const (fun _ x bs rest hx => hc x bs rest hx) hg) h

/-- A successful point-pair read consumed 64 bytes. -/
theorem pointPairReader_length {bs rest : List UInt8} {pq : VestaG × VestaG}
    (h : pointPairReader.run bs = some (pq, rest)) : bs.length = 64 + rest.length := by
  simp only [pointPairReader, StateT.run_bind, Option.bind_eq_bind] at h
  obtain ⟨⟨first, bs₁⟩, hfirst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨second, bs₂⟩, hsecond, hpure⟩ := Option.bind_eq_some_iff.mp h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change pointReader.run bs₁ = some (second, bs₂) at hsecond
  have h1 := read32_length hfirst
  have h2 := read32_length hsecond
  omega

/-- A successful permutation-set read consumed 96 bytes with a `lastEval`, 64 without. -/
theorem permSetReader_length {hasLast : Bool} {bs rest : List UInt8} {e : PermSetEval Fp}
    (h : (permSetReader hasLast).run bs = some (e, rest)) :
    bs.length = (if hasLast then 96 else 64) + rest.length := by
  cases hasLast with
  | false =>
      simp only [permSetReader, StateT.run_bind, Option.bind_eq_bind, Bool.false_eq_true,
        if_false] at h
      obtain ⟨⟨eval, bs₁⟩, heval, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨nextEval, bs₂⟩, hnext, hpure⟩ := Option.bind_eq_some_iff.mp h
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      change scalarReader.run bs₁ = some (nextEval, bs₂) at hnext
      have h1 := read32_length heval
      have h2 := read32_length hnext
      simp only [Bool.false_eq_true, if_false]
      omega
  | true =>
      simp only [permSetReader, StateT.run_bind, Option.bind_eq_bind, if_true] at h
      obtain ⟨⟨eval, bs₁⟩, heval, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨nextEval, bs₂⟩, hnext, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨lastEval, bs₃⟩, hlast, hpure⟩ := Option.bind_eq_some_iff.mp h
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      change scalarReader.run bs₁ = some (nextEval, bs₂) at hnext
      change scalarReader.run bs₂ = some (lastEval, bs₃) at hlast
      have h1 := read32_length heval
      have h2 := read32_length hnext
      have h3 := read32_length hlast
      simp only [if_true]
      omega

/-- A successful lookup-evaluation read consumed 160 bytes. -/
theorem lookupReader_length {bs rest : List UInt8} {e : LookupEval Fp}
    (h : lookupReader.run bs = some (e, rest)) : bs.length = 160 + rest.length := by
  simp only [lookupReader, StateT.run_bind, Option.bind_eq_bind] at h
  obtain ⟨⟨productEval, bs₁⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨productNextEval, bs₂⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨permutedInputEval, bs₃⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨permutedInputInvEval, bs₄⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨permutedTableEval, bs₅⟩, h5, hpure⟩ := Option.bind_eq_some_iff.mp h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change scalarReader.run bs₁ = some (productNextEval, bs₂) at h2
  change scalarReader.run bs₂ = some (permutedInputEval, bs₃) at h3
  change scalarReader.run bs₃ = some (permutedInputInvEval, bs₄) at h4
  change scalarReader.run bs₄ = some (permutedTableEval, bs₅) at h5
  have l1 := read32_length h1
  have l2 := read32_length h2
  have l3 := read32_length h3
  have l4 := read32_length h4
  have l5 := read32_length h5
  omega

/-- The exact byte count `readProof?` accepts for a shape: 32 bytes per element, with the
element counts read off the shape, and each permutation set contributing its shape-selected
two or three scalars. At the deployed Orchard shape this is the consensus proof size
(ZIP 225: `2720 + 2272 · nActionsOrchard`). -/
def proofLength (shape : Shape) : ℕ :=
  shape.numProofs * (shape.numAdviceColumns * 32)
    + shape.numProofs * (shape.numLookups * 64)
    + shape.numProofs * (shape.numPermutationSets * 32)
    + shape.numProofs * (shape.numLookups * 32)
    + 32
    + shape.numQuotientPieces * 32
    + shape.numProofs * (shape.numInstanceQueries * 32)
    + shape.numProofs * (shape.numAdviceQueries * 32)
    + shape.numFixedQueries * 32
    + 32
    + shape.numPermutationColumns * 32
    + shape.numProofs * (List.ofFn fun s : Fin shape.numPermutationSets =>
        if s.val + 1 < shape.numPermutationSets then (96 : ℕ) else 64).sum
    + shape.numProofs * (shape.numLookups * 160)
    + 32
    + shape.numPointSets * 32
    + 32
    + shape.k * 64
    + 64

/-- **Byte accounting.** A successful deployed-order parse consumed exactly `proofLength shape`
bytes ahead of its unread suffix. -/
theorem readProof?_length {shape : Shape} {bs rest : List UInt8}
    {ps : ProofString shape Fp VestaG}
    (hread : (readProof? shape).run bs = some (ps, rest)) :
    bs.length = proofLength shape + rest.length := by
  unfold readProof? at hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceCommitments, bs₁⟩, hadviceCommitments, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupPermuted, bs₂⟩, hlookupPermuted, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationProduct, bs₃⟩, hpermutationProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupProduct, bs₄⟩, hlookupProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandom, bs₅⟩, hvanishingRandom, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨hPieces, bs₆⟩, hhPieces, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨instanceEvals, bs₇⟩, hinstanceEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceEvals, bs₈⟩, hadviceEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨fixedEvals, bs₉⟩, hfixedEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandomEval, bs₁₀⟩, hvanishingRandomEval, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationCommonEvals, bs₁₁⟩, hpermutationCommonEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationSetEvals, bs₁₂⟩, hpermutationSetEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupEvals, bs₁₃⟩, hlookupEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenQPrime, bs₁₄⟩, hmultiopenQPrime, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenU, bs₁₅⟩, hmultiopenU, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaS, bs₁₆⟩, hipaS, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaRounds, bs₁₇⟩, hipaRounds, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaC, bs₁₈⟩, hipaC, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaF, bs₁₉⟩, hipaF, hpure⟩ := Option.bind_eq_some_iff.mp hread
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change (readGrid shape.numProofs shape.numLookups pointPairReader).run bs₁ =
    some (lookupPermuted, bs₂) at hlookupPermuted
  change (readGrid shape.numProofs shape.numPermutationSets pointReader).run bs₂ =
    some (permutationProduct, bs₃) at hpermutationProduct
  change (readGrid shape.numProofs shape.numLookups pointReader).run bs₃ =
    some (lookupProduct, bs₄) at hlookupProduct
  change pointReader.run bs₄ = some (vanishingRandom, bs₅) at hvanishingRandom
  change (readVec shape.numQuotientPieces fun _ => pointReader).run bs₅ =
    some (hPieces, bs₆) at hhPieces
  change (readGrid shape.numProofs shape.numInstanceQueries scalarReader).run bs₆ =
    some (instanceEvals, bs₇) at hinstanceEvals
  change (readGrid shape.numProofs shape.numAdviceQueries scalarReader).run bs₇ =
    some (adviceEvals, bs₈) at hadviceEvals
  change (readVec shape.numFixedQueries fun _ => scalarReader).run bs₈ =
    some (fixedEvals, bs₉) at hfixedEvals
  change scalarReader.run bs₉ = some (vanishingRandomEval, bs₁₀) at hvanishingRandomEval
  change (readVec shape.numPermutationColumns fun _ => scalarReader).run bs₁₀ =
    some (permutationCommonEvals, bs₁₁) at hpermutationCommonEvals
  change (readVec shape.numProofs fun _ =>
    readVec shape.numPermutationSets fun s =>
      permSetReader (decide (s.val + 1 < shape.numPermutationSets))).run bs₁₁ =
    some (permutationSetEvals, bs₁₂) at hpermutationSetEvals
  change (readGrid shape.numProofs shape.numLookups lookupReader).run bs₁₂ =
    some (lookupEvals, bs₁₃) at hlookupEvals
  change pointReader.run bs₁₃ = some (multiopenQPrime, bs₁₄) at hmultiopenQPrime
  change (readVec shape.numPointSets fun _ => scalarReader).run bs₁₄ =
    some (multiopenU, bs₁₅) at hmultiopenU
  change pointReader.run bs₁₅ = some (ipaS, bs₁₆) at hipaS
  change (readVec shape.k fun _ => pointPairReader).run bs₁₆ =
    some (ipaRounds, bs₁₇) at hipaRounds
  change scalarReader.run bs₁₇ = some (ipaC, bs₁₈) at hipaC
  change scalarReader.run bs₁₈ = some (ipaF, bs₁₉) at hipaF
  have l1 := readGrid_length (fun x bs rest hx => read32_length hx) hadviceCommitments
  have l2 := readGrid_length (fun x bs rest hx => pointPairReader_length hx) hlookupPermuted
  have l3 := readGrid_length (fun x bs rest hx => read32_length hx) hpermutationProduct
  have l4 := readGrid_length (fun x bs rest hx => read32_length hx) hlookupProduct
  have l5 := read32_length hvanishingRandom
  have l6 := readVec_length_const (fun _ x bs rest hx => read32_length hx) hhPieces
  have l7 := readGrid_length (fun x bs rest hx => read32_length hx) hinstanceEvals
  have l8 := readGrid_length (fun x bs rest hx => read32_length hx) hadviceEvals
  have l9 := readVec_length_const (fun _ x bs rest hx => read32_length hx) hfixedEvals
  have l10 := read32_length hvanishingRandomEval
  have l11 := readVec_length_const (fun _ x bs rest hx => read32_length hx)
    hpermutationCommonEvals
  have l12 := readVec_length_const
    (fun _ g bs rest hg =>
      readVec_length shape.numPermutationSets
        (fun s => permSetReader (decide (s.val + 1 < shape.numPermutationSets)))
        (fun s => if s.val + 1 < shape.numPermutationSets then (96 : ℕ) else 64)
        (fun s x bs rest hx => by
          have := permSetReader_length hx
          simpa [decide_eq_true_eq] using this) hg)
    hpermutationSetEvals
  have l13 := readGrid_length (fun x bs rest hx => lookupReader_length hx) hlookupEvals
  have l14 := read32_length hmultiopenQPrime
  have l15 := readVec_length_const (fun _ x bs rest hx => read32_length hx) hmultiopenU
  have l16 := read32_length hipaS
  have l17 := readVec_length_const (fun _ x bs rest hx => pointPairReader_length hx) hipaRounds
  have l18 := read32_length hipaC
  have l19 := read32_length hipaF
  unfold proofLength
  omega

/-- Every accepted proof carries at least its two final IPA scalars. -/
theorem proofLength_ge_64 (shape : Shape) : 64 ≤ proofLength shape := by
  unfold proofLength
  omega

/-- **Truncation is rejected, by accounting.** No strict prefix of an exactly-parsed proof
string parses: a parse of the prefix would consume `proofLength shape` bytes the prefix does
not have. Nothing is evaluated over the truncated bytes. -/
theorem readProof?_none_of_truncated {shape : Shape} {bs : List UInt8} {n : ℕ}
    {ps : ProofString shape Fp VestaG}
    (hread : (readProof? shape).run bs = some (ps, [])) (hn : n < bs.length) :
    (readProof? shape).run (bs.take n) = none := by
  cases h : (readProof? shape).run (bs.take n) with
  | none => rfl
  | some pr =>
      exfalso
      obtain ⟨ps', rest'⟩ := pr
      have h1 := readProof?_length hread
      have h2 := readProof?_length h
      have h3 : (bs.take n).length = n := by
        rw [List.length_take]
        omega
      simp only [List.length_nil] at h1
      omega

/-- **A non-canonical final scalar is rejected.** Replacing the last 32 bytes of an
exactly-parsed proof string with any 32 bytes reading at or above `p` fails the parse: by
whole-proof canonicality a successful parse would end in the `to_repr` bytes of its own final
scalar, whose little-endian value is canonical. -/
theorem readProof?_none_of_noncanonical_final_scalar {shape : Shape} {bs V : List UInt8}
    {ps : ProofString shape Fp VestaG}
    (hread : (readProof? shape).run bs = some (ps, []))
    (hVlen : V.length = 32) (hVge : scalarFieldOrder ≤ leInt V) :
    (readProof? shape).run (bs.take (bs.length - 32) ++ V) = none := by
  cases h : (readProof? shape).run (bs.take (bs.length - 32) ++ V) with
  | none => rfl
  | some pr =>
      exfalso
      obtain ⟨ps', rest'⟩ := pr
      have hL := readProof?_length hread
      simp only [List.length_nil] at hL
      have h64 := proofLength_ge_64 shape
      have hAlen : (bs.take (bs.length - 32)).length = bs.length - 32 := by
        rw [List.length_take]
        omega
      have hinlen : (bs.take (bs.length - 32) ++ V).length = bs.length := by
        rw [List.length_append, hAlen, hVlen]
        omega
      have hlen := readProof?_length h
      have hrest : rest' = [] := by
        have : rest'.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero this
      subst hrest
      have hser := readProof?_eq_some_serialize h
      rw [List.append_nil] at hser
      obtain ⟨Y, hY⟩ : ∃ Y, serializeProof ps' = Y ++ (scalarRepr ps'.ipaF).toList := ⟨_, rfl⟩
      have hYlen : Y.length = bs.length - 32 := by
        have h1 : (serializeProof ps').length = bs.length := by rw [← hser]; exact hinlen
        rw [hY, List.length_append] at h1
        simp only [Vector.length_toList] at h1
        omega
      have hsuffix : (scalarRepr ps'.ipaF).toList = V := by
        have heq : bs.take (bs.length - 32) ++ V = Y ++ (scalarRepr ps'.ipaF).toList := by
          rw [← hY, ← hser]
        exact (List.append_inj_right heq (by rw [hAlen, hYlen])).symm
      have hlhs : leInt (scalarRepr ps'.ipaF).toList = ps'.ipaF.val := by
        rw [leInt_toList, LEOS2IP_scalarRepr]
      rw [hsuffix] at hlhs
      have hcan : ps'.ipaF.val < scalarFieldOrder := ZMod.val_lt _
      omega

/-! ## The sign bit

Bit 255 of a compressed encoding is the parity of `y`; the low 255 bits are `x`. Negation fixes
`x` and flips the parity over an odd-order field, so flipping the top bit of a non-identity
point's encoding is exactly the negated point's encoding, and a proof string with its leading
point's sign bit flipped parses to the same proof with that one commitment negated. -/

/-- The bytes of `a` followed by the bytes of `b` read as `leInt a + 256^|a| · leInt b`. -/
theorem leInt_append (a b : List UInt8) :
    leInt (a ++ b) = leInt a + 256 ^ a.length * leInt b := by
  simp [leInt, List.map_append, Nat.ofDigits_append, List.length_map]

/-- A single byte reads as its value. -/
theorem leInt_singleton (b : UInt8) : leInt [b] = b.toNat := by
  rw [leInt_cons]
  simp [leInt]

/-- 32-byte strings are determined by the integer they read as: the bytes are its digits. -/
theorem leInt_inj_32 {a b : List UInt8} (ha : a.length = 32) (hb : b.length = 32)
    (h : leInt a = leInt b) : a = b := by
  rw [← ofFn_leInt ha rfl, ← ofFn_leInt hb rfl, h]

/-- The first `n` bytes read as the integer's low `n` digits. -/
theorem leInt_take (bs : List UInt8) (n : ℕ) (hn : n ≤ bs.length) :
    leInt (bs.take n) = leInt bs % 256 ^ n := by
  conv_rhs => rw [← List.take_append_drop n bs]
  rw [leInt_append, List.length_take, Nat.min_eq_left hn, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by
    have := leInt_lt (bs.take n)
    rwa [List.length_take, Nat.min_eq_left hn] at this)).symm

/-- **The sign bit is the parity of `y`.** Flipping the top bit of a non-identity point's
compressed encoding gives exactly the negated point's encoding. -/
theorem toBytes_neg_flip {P : VestaG} (hP : P ≠ 0) :
    (toBytes P).toList.take 31 ++ [(toBytes P).toList.getD 31 0 ^^^ 0x80]
      = (toBytes (-P)).toList := by
  have hy0 : P.y ≠ 0 := fun hy => Vesta.no_onCurve_y_zero P.x (hy ▸ onCurve_of_ne_zero hP)
  have hs2 : P.y.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hs' : (-P).y.val % 2 = 1 - P.y.val % 2 := by
    have hne : (-P.y).val % 2 ≠ P.y.val % 2 := neg_val_parity_ne hy0
    have h1 : (-P.y).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [SWPoint.neg_y]
    omega
  have hNP : leInt (toBytes P).toList = P.x.val + P.y.val % 2 * signBit := by
    rw [leInt_toList, toBytes, LEOS2IP_I2LEOSP_256, signBit_eq]
  have hNQ : leInt (toBytes (-P)).toList = P.x.val + (1 - P.y.val % 2) * signBit := by
    have hNQ0 : leInt (toBytes (-P)).toList = (-P).x.val + (-P).y.val % 2 * signBit := by
      rw [leInt_toList, toBytes, LEOS2IP_I2LEOSP_256, signBit_eq]
    rw [hNQ0, hs', SWPoint.neg_x]
  have hxlt : P.x.val < signBit := lt_trans (ZMod.val_lt P.x) vestaBase_card_lt_signBit
  have hsig : signBit = 256 ^ 31 * 128 := by rw [signBit_eq]; norm_num
  have hxdiv : P.x.val / 256 ^ 31 < 128 := by
    apply Nat.div_lt_of_lt_mul
    omega
  have hlen : (toBytes P).toList.length = 32 := by simp
  have hsplit : ∀ t : ℕ, t < 2 → (P.x.val + t * signBit) / 256 ^ 31 % 256
      = P.x.val / 256 ^ 31 + t * 128 := by
    intro t ht
    have h4 : P.x.val + t * signBit = P.x.val + t * 128 * 256 ^ 31 := by rw [hsig]; ring
    rw [h4, Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < 256 ^ 31)]
    exact Nat.mod_eq_of_lt (by omega)
  have hb31 : (toBytes P).toList[31].toNat = P.x.val / 256 ^ 31 + P.y.val % 2 * 128 := by
    rw [← leInt_div_pow_mod (toBytes P).toList 31 (by simp [hlen]), hNP, hsplit _ hs2]
  have hxor : ∀ (a : Fin 128) (t : Fin 2),
      (a.val + t.val * 128) ^^^ 128 = a.val + (1 - t.val) * 128 := by decide +kernel
  have hc : ((toBytes P).toList.getD 31 0 ^^^ 0x80).toNat
      = P.x.val / 256 ^ 31 + (1 - P.y.val % 2) * 128 := by
    rw [List.getD_eq_getElem _ _ (by simp [hlen]), UInt8.toNat_xor, hb31]
    exact hxor ⟨_, hxdiv⟩ ⟨_, hs2⟩
  have htklen : ((toBytes P).toList.take 31).length = 31 := by
    rw [List.length_take, hlen]
    omega
  have htake : leInt ((toBytes P).toList.take 31) = leInt (toBytes P).toList % 256 ^ 31 :=
    leInt_take _ 31 (by omega)
  have h256 : (256 : ℕ) ^ 31 = 452312848583266388373324160190187140051835877600158453279131187530910662656 := by norm_num
  apply leInt_inj_32 (by rw [List.length_append, htklen]; rfl) (by simp)
  rw [leInt_append, htklen, leInt_singleton, hc, hNQ, htake, hNP, hsig, h256]
  omega

/-- A successful vector read with its first element's bytes replaced by bytes its reader reads
back as `x'`, leaving the same remainder, succeeds with only the first slot changed: the later
element reads run on the same suffix. -/
theorem readVec_run_replace_head {α : Type} {n : ℕ} {r : Fin (n + 1) → ProofReader α}
    {bs bs' rest : List UInt8} {f : Fin (n + 1) → α} {x' : α}
    (h : (readVec (n + 1) r).run bs = some (f, rest))
    (hx' : ∀ mid, (r 0).run bs = some (f 0, mid) → (r 0).run bs' = some (x', mid)) :
    (readVec (n + 1) r).run bs' = some (Fin.cons x' (fun i => f i.succ), rest) := by
  simp only [readVec, StateT.run_bind, Option.bind_eq_bind] at h ⊢
  obtain ⟨⟨x, bs₁⟩, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨g, bs₂⟩, hg, hpure⟩ := Option.bind_eq_some_iff.mp h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨hf, rfl⟩ := hpure
  have hg' : (readVec n fun i => r i.succ).run bs₁ = some (g, bs₂) := hg
  have hx0 : (r 0).run bs = some (f 0, bs₁) := by
    rw [← hf, Fin.cons_zero]
    exact hx
  have hgf : g = fun i => f i.succ := by
    funext i
    rw [← hf, Fin.cons_succ]
  rw [hx' bs₁ hx0]
  simp only [Option.bind_some, hg', StateT.run_pure, Option.pure_def, hgf]

/-- The grid form of head replacement, at counts only known nonzero: the replacement lands at
grid position `(0, 0)` and every other slot survives. -/
theorem readGrid_run_replace_head {α : Type} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {r : ProofReader α} {bs bs' rest : List UInt8} {f : Fin m → Fin n → α} {x' : α}
    (h : (readGrid m n r).run bs = some (f, rest))
    (hx' : ∀ mid,
      r.run bs = some (f ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩, mid) →
      r.run bs' = some (x', mid)) :
    ∃ f', (readGrid m n r).run bs' = some (f', rest)
      ∧ f' ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩ = x' := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hrow : ∀ mid,
      (readVec (n' + 1) fun _ => r).run bs = some (f 0, mid) →
      (readVec (n' + 1) fun _ => r).run bs'
        = some (Fin.cons x' (fun i => f 0 i.succ), mid) := by
    intro mid hmid
    refine readVec_run_replace_head hmid fun mid₂ hmid₂ => hx' mid₂ ?_
    simpa using hmid₂
  refine ⟨Fin.cons (Fin.cons x' (fun i => f 0 i.succ)) (fun i => f i.succ),
    readVec_run_replace_head (r := fun _ => readVec (n' + 1) fun _ => r) h hrow, ?_⟩
  simp [Fin.cons_zero]

/-- **Sign-of-first-commitment locality.** Replacing the leading compressed point of a parsed
proof string with bytes that read back as another point `Q` still parses, with the same unread
suffix, and the replacement lands in the first advice commitment. The continuation of the read
depends only on the suffix bytes, which the replacement leaves alone. -/
theorem readProof?_run_replace_first_advice {shape : Shape} {bs bs' rest : List UInt8}
    {ps : ProofString shape Fp VestaG} {Q : VestaG}
    (hm : shape.numProofs ≠ 0) (hn : shape.numAdviceColumns ≠ 0)
    (hread : (readProof? shape).run bs = some (ps, rest))
    (hx' : ∀ mid, pointReader.run bs = some
        (ps.adviceCommitments ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩, mid) →
      pointReader.run bs' = some (Q, mid)) :
    ∃ ps' : ProofString shape Fp VestaG,
      (readProof? shape).run bs' = some (ps', rest)
      ∧ ps'.adviceCommitments ⟨0, Nat.pos_of_ne_zero hm⟩ ⟨0, Nat.pos_of_ne_zero hn⟩ = Q := by
  unfold readProof? at hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceCommitments, bs₁⟩, hadviceCommitments, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupPermuted, bs₂⟩, hlookupPermuted, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationProduct, bs₃⟩, hpermutationProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupProduct, bs₄⟩, hlookupProduct, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandom, bs₅⟩, hvanishingRandom, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨hPieces, bs₆⟩, hhPieces, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨instanceEvals, bs₇⟩, hinstanceEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨adviceEvals, bs₈⟩, hadviceEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨fixedEvals, bs₉⟩, hfixedEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨vanishingRandomEval, bs₁₀⟩, hvanishingRandomEval, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationCommonEvals, bs₁₁⟩, hpermutationCommonEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨permutationSetEvals, bs₁₂⟩, hpermutationSetEvals, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨lookupEvals, bs₁₃⟩, hlookupEvals, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenQPrime, bs₁₄⟩, hmultiopenQPrime, hread⟩ :=
    Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨multiopenU, bs₁₅⟩, hmultiopenU, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaS, bs₁₆⟩, hipaS, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaRounds, bs₁₇⟩, hipaRounds, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaC, bs₁₈⟩, hipaC, hread⟩ := Option.bind_eq_some_iff.mp hread
  rw [StateT.run_bind] at hread
  obtain ⟨⟨ipaF, bs₁₉⟩, hipaF, hpure⟩ := Option.bind_eq_some_iff.mp hread
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  change (readGrid shape.numProofs shape.numLookups pointPairReader).run bs₁ =
    some (lookupPermuted, bs₂) at hlookupPermuted
  change (readGrid shape.numProofs shape.numPermutationSets pointReader).run bs₂ =
    some (permutationProduct, bs₃) at hpermutationProduct
  change (readGrid shape.numProofs shape.numLookups pointReader).run bs₃ =
    some (lookupProduct, bs₄) at hlookupProduct
  change pointReader.run bs₄ = some (vanishingRandom, bs₅) at hvanishingRandom
  change (readVec shape.numQuotientPieces fun _ => pointReader).run bs₅ =
    some (hPieces, bs₆) at hhPieces
  change (readGrid shape.numProofs shape.numInstanceQueries scalarReader).run bs₆ =
    some (instanceEvals, bs₇) at hinstanceEvals
  change (readGrid shape.numProofs shape.numAdviceQueries scalarReader).run bs₇ =
    some (adviceEvals, bs₈) at hadviceEvals
  change (readVec shape.numFixedQueries fun _ => scalarReader).run bs₈ =
    some (fixedEvals, bs₉) at hfixedEvals
  change scalarReader.run bs₉ = some (vanishingRandomEval, bs₁₀) at hvanishingRandomEval
  change (readVec shape.numPermutationColumns fun _ => scalarReader).run bs₁₀ =
    some (permutationCommonEvals, bs₁₁) at hpermutationCommonEvals
  change (readVec shape.numProofs fun _ =>
    readVec shape.numPermutationSets fun s =>
      permSetReader (decide (s.val + 1 < shape.numPermutationSets))).run bs₁₁ =
    some (permutationSetEvals, bs₁₂) at hpermutationSetEvals
  change (readGrid shape.numProofs shape.numLookups lookupReader).run bs₁₂ =
    some (lookupEvals, bs₁₃) at hlookupEvals
  change pointReader.run bs₁₃ = some (multiopenQPrime, bs₁₄) at hmultiopenQPrime
  change (readVec shape.numPointSets fun _ => scalarReader).run bs₁₄ =
    some (multiopenU, bs₁₅) at hmultiopenU
  change pointReader.run bs₁₅ = some (ipaS, bs₁₆) at hipaS
  change (readVec shape.k fun _ => pointPairReader).run bs₁₆ =
    some (ipaRounds, bs₁₇) at hipaRounds
  change scalarReader.run bs₁₇ = some (ipaC, bs₁₈) at hipaC
  change scalarReader.run bs₁₈ = some (ipaF, bs₁₉) at hipaF
  obtain ⟨g', hg', hg'0⟩ := readGrid_run_replace_head hm hn hadviceCommitments hx'
  refine ⟨{
    adviceCommitments := g'
    lookupPermutedInput := fun p l => (lookupPermuted p l).1
    lookupPermutedTable := fun p l => (lookupPermuted p l).2
    permutationProduct
    lookupProduct
    vanishingRandom
    hPieces
    instanceEvals
    adviceEvals
    fixedEvals
    vanishingRandomEval
    permutationCommonEvals
    permutationSetEvals
    lookupEvals
    multiopenQPrime
    multiopenU
    ipaS
    ipaRounds
    ipaC
    ipaF }, ?_, hg'0⟩
  unfold readProof?
  rw [StateT.run_bind, hg']
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hlookupPermuted]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hpermutationProduct]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hlookupProduct]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hvanishingRandom]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hhPieces]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hinstanceEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hadviceEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hfixedEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hvanishingRandomEval]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hpermutationCommonEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hpermutationSetEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hlookupEvals]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hmultiopenQPrime]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hmultiopenU]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hipaS]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hipaRounds]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hipaC]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [StateT.run_bind, hipaF]
  simp only [Option.bind_eq_bind, Option.bind_some, StateT.run_pure]
  rfl

end Zcash.Snark
