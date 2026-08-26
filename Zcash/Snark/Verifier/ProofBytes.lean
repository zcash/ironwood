import Mathlib.Data.Fin.Tuple.Basic
import Zcash.Snark.Verifier.Transcript

/-!
# Halo2's proof-string byte layer

`ProofString` starts where halo2's `Blake2bRead` finishes: at typed points and scalars. This module
writes down the reads beneath it — `read_point` and `read_scalar` from halo2's `transcript.rs`,
with `pasta_curves`' `from_bytes` and `from_repr` — as a decoder over the raw proof bytes, and the
prover's `write_point`/`write_scalar` as the serializer.

* `decodeScalar32` takes 32 bytes as a little-endian integer and accepts it only below `p`
  (`from_repr`'s canonicality check).
* `decodePoint32` takes 32 bytes: bit 255 is the parity of `y`, the low 255 bits are `x` and must
  be below `q`; `y` is the square root of `x³ + 5` with the signalled parity. The all-zero string,
  which `from_bytes` decodes to the identity, is rejected: the deployed transcript refuses to
  absorb the identity, and no Vesta point has `x = 0` (`Vesta.no_onCurve_x_zero`), so the
  rejection here is the deployed rejection one step earlier.
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

/-- The empty string denotes zero. -/
@[simp] theorem leInt_nil : leInt [] = 0 := rfl

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

/-- `from_repr`: 32 canonical little-endian bytes, or rejection. -/
def decodeScalar32 (enc : List UInt8) : Option Fp :=
  if leInt enc < scalarFieldOrder then some ((leInt enc : ℕ) : Fp) else none

/-- **Canonical scalar decoding.** On 32 bytes, decoding succeeds exactly on the scalar's own
`to_repr`. -/
theorem decodeScalar32_eq_some_iff {enc : List UInt8} (h : enc.length = 32) {s : Fp} :
    decodeScalar32 enc = some s ↔ enc = (scalarRepr s).toList := by
  constructor
  · intro hd
    unfold decodeScalar32 at hd
    split_ifs at hd with hlt
    simp only [Option.some.injEq] at hd
    subst hd
    refine (scalarRepr_toList_eq h ?_).symm
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hlt
  · intro heq
    rw [heq]
    unfold decodeScalar32
    rw [leInt_toList, LEOS2IP_scalarRepr, if_pos (ZMod.val_lt s), ZMod.natCast_zmod_val]

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

/-- `from_bytes` on 32 bytes, with the identity rejected as the transcript would reject it. -/
def decodePoint32 (enc : List UInt8) : Option VestaG :=
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

/-- **Canonical point decoding.** On 32 bytes, decoding succeeds exactly on the compressed encoding
of a non-identity point. -/
theorem decodePoint32_eq_some_iff {enc : List UInt8} (h : enc.length = 32) {P : VestaG} :
    decodePoint32 enc = some P ↔ P ≠ 0 ∧ enc = (toBytes P).toList := by
  have hq := vestaBase_card_lt_signBit
  have hvlt : leInt enc < 2 ^ 256 := leInt_lt_of_length_32 h
  constructor
  · intro hd
    unfold decodePoint32 at hd
    split_ifs at hd with hx
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
    rw [if_pos (by rw [hmod]; exact ZMod.val_lt P.x)]
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
  read32_eq_some_iff (fun _ => by simp) (fun _ _ h => decodeScalar32_eq_some_iff h)

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
    obtain ⟨hP, henc⟩ := (decodePoint32_eq_some_iff htake).mp hy
    refine ⟨hP, ?_⟩
    conv_lhs => rw [← List.take_append_drop 32 bs]
    rw [henc]
  · rintro ⟨hP, heq⟩
    rw [heq]
    unfold pointReader read32
    simp only [StateT.run]
    have hlen : (toBytes P).toList.length = 32 := by simp
    rw [if_pos (by simp), List.take_left' hlen, List.drop_left' hlen,
      (decodePoint32_eq_some_iff hlen).mpr ⟨hP, rfl⟩]
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

/-- The bytes of `m × n` elements proof-major. -/
def serializeGrid {α : Type} (m n : ℕ) (enc : α → List UInt8) (f : Fin m → Fin n → α) :
    List UInt8 :=
  serializeVec m (fun _ g => serializeVec n (fun _ => enc) g) f

/-- Read one permutation set's evaluations: `eval`, `nextEval`, and `lastEval` exactly when the set
is not the last (halo2 `permutation::verifier::Committed::evaluate`). -/
def permSetReader (hasLast : Bool) : ProofReader (PermSetEval Fp) := do
  let eval ← scalarReader
  let nextEval ← scalarReader
  let lastEval ← if hasLast then (some <$> scalarReader) else pure none
  pure { eval, nextEval, lastEval }

/-- The bytes of one permutation set's evaluations. -/
def serializePermSet (e : PermSetEval Fp) : List UInt8 :=
  (scalarRepr e.eval).toList ++ (scalarRepr e.nextEval).toList
    ++ (e.lastEval.map fun s => (scalarRepr s).toList).getD []

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

/-- The compressed bytes of a point (`write_point`). -/
def pointBytesCompressed (P : VestaG) : List UInt8 := (toBytes P).toList

/-- The bytes of a scalar (`write_scalar`). -/
def scalarBytesRaw (s : Fp) : List UInt8 := (scalarRepr s).toList

/-- halo2 `verify_proof`'s reads, in order: the proof string as the deployed verifier parses it.
Squeezes consume no bytes, so this is `deriveChallenges`' absorb order restricted to proof reads,
with the two IPA scalars `c` and `f` read after the last squeeze. -/
def readProof? (shape : Shape) : ProofReader (ProofString shape Fp VestaG) := do
  let adviceCommitments ← readGrid shape.numProofs shape.numAdviceColumns pointReader
  let lookupPermuted ← readGrid shape.numProofs shape.numLookups (do
    let input ← pointReader
    let table ← pointReader
    pure (input, table))
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
  let ipaRounds ← readVec shape.k fun _ => do
    let l ← pointReader
    let r ← pointReader
    pure (l, r)
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

/-- The prover's byte string for a typed proof: `write_point`/`write_scalar` in `readProof?`'s
order. -/
def serializeProof {shape : Shape} (ps : ProofString shape Fp VestaG) : List UInt8 :=
  serializeGrid shape.numProofs shape.numAdviceColumns pointBytesCompressed ps.adviceCommitments
    ++ serializeVec shape.numProofs (fun _ g => serializeVec shape.numLookups
        (fun _ pr => pointBytesCompressed pr.1 ++ pointBytesCompressed pr.2) g)
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
    ++ serializeVec shape.k (fun _ pr => pointBytesCompressed pr.1 ++ pointBytesCompressed pr.2)
        ps.ipaRounds
    ++ scalarBytesRaw ps.ipaC
    ++ scalarBytesRaw ps.ipaF

/-- Read a proof that must consume its byte string exactly. The deployed verifier itself ignores
trailing bytes; the consensus rules fix the proof length, so a proof of the right length either
parses exactly or is rejected. -/
def decodeProofExact? (shape : Shape) (bs : List UInt8) : Option (ProofString shape Fp VestaG) :=
  match (readProof? shape).run bs with
  | some (ps, []) => some ps
  | _ => none

end Zcash.Snark
