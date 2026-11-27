import Zcash.Common.Hash.Blake2bSimd.Portable
import Zcash.Common.Hash.Blake2bSimd.GutsSpec
import Zcash.Common.Hash.Blake2bSimd.LoopSpec
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases

/-!
# `blake2b_simd`'s portable compression is Ironwood's `compress`

The portable `compress_block` (`Portable.lean`) and `Common/Hash/Blake2b.lean`'s `compress` take
a block, the state and the byte count, and give the same new state (`compressBlock_eq_compress`).
They agree step by step: `g` is `mix`, so each round is Ironwood's `round`, and the working
vector, message words and fold back are the same. The only difference in form is the last-node
word, which `blake2b_simd` xors in and Ironwood leaves out; with the flag off it is zero.

The module also records what the portable `g` writes, as `gWords` of the four positions it mixes
(`g_eq_set`, `g_get_a` to `g_get_other`); the AVX2 proof compares its lanes against that.
-/

namespace Zcash.Common.Blake2bSimd

attribute [local irreducible] Blake2b.rotr in
/-- The portable `g` on four distinct positions is Ironwood's `mix`. -/
theorem g_eq_mix (v : Vector Word 16) (a b c d : Fin 16) (x y : Word)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    Portable.g v a b c d x y = Blake2b.mix v a b c d x y := by
  have hab' : a.val ≠ b.val := Fin.val_ne_of_ne hab
  have hac' : a.val ≠ c.val := Fin.val_ne_of_ne hac
  have had' : a.val ≠ d.val := Fin.val_ne_of_ne had
  have hbc' : b.val ≠ c.val := Fin.val_ne_of_ne hbc
  have hbd' : b.val ≠ d.val := Fin.val_ne_of_ne hbd
  have hcd' : c.val ≠ d.val := Fin.val_ne_of_ne hcd
  ext i hi
  simp only [Portable.g, Blake2b.mix, Blake2b.upd, Vector.get, Fin.getElem_fin, Vector.getElem_set,
    rotateRight, if_neg hab', if_neg hac', if_neg had', if_neg hbc', if_neg hbd',
    if_neg hcd',
    if_neg hab'.symm, if_neg hac'.symm, if_neg had'.symm, if_neg hbc'.symm, if_neg hbd'.symm,
    if_neg hcd'.symm, Vector.getElem_toArray, if_true]
  split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals (subst_vars; simp [Ne.symm hbd', Ne.symm hcd', Ne.symm hbc'])

/-- Portable round `r` is Ironwood's `round` with row `r` of `sigma`. -/
theorem round_eq_round (r : Fin 12) (m v : Vector Word 16) :
    Portable.round r m v = Blake2b.round m (Blake2b.sigma.get r) v := by
  simp only [Portable.round, Blake2b.round, SIGMA, Vector.get, Fin.getElem_fin]
  simp (disch := decide) only [g_eq_mix]
  rfl

/-- A fold over `List.finRange 12`, unrolled. -/
theorem foldl_finRange_12 {α : Type} (f : α → Fin 12 → α) (v : α) :
    (List.finRange 12).foldl f v =
      f (f (f (f (f (f (f (f (f (f (f (f v 0) 1) 2) 3) 4) 5) 6) 7) 8) 9) 10) 11 := rfl

/-- The portable working vector is Ironwood's: the state, then `IV` with the counter words and
the final flag folded in. The last-node word is xored with `flagWord false`, which is zero. -/
theorem startVector_eq (h : Vector Word 8) (t : ℕ) (last : Bool) :
    (#v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV[0], IV[1], IV[2], IV[3],
       IV[4] ^^^ Blake2b.counterLow t, IV[5] ^^^ Blake2b.counterHigh t,
       IV[6] ^^^ flagWord last, IV[7] ^^^ flagWord false] : Vector Word 16) =
      (let v : Vector UInt64 16 := h ++ Blake2b.IV
       let v := Blake2b.upd v 12 (v.get 12 ^^^ Blake2b.counterLow t)
       let v := Blake2b.upd v 13 (v.get 13 ^^^ Blake2b.counterHigh t)
       if last then Blake2b.upd v 14 (v.get 14 ^^^ 0xffffffffffffffff) else v) := by
  obtain ⟨⟨l⟩, hl⟩ := h
  match l, hl with
  | [h0, h1, h2, h3, h4, h5, h6, h7], _ =>
    simp only [flagWord, Bool.false_eq_true, if_false, UInt64.xor_zero]
    cases last <;> rfl

/-- The portable message words are Ironwood's `loadBlock` of the block. -/
theorem loadBlock_eq (block : Vector UInt8 128) :
    (Vector.ofFn fun i : Fin 16 =>
      wordFromLeBytes (Vector.ofFn fun k : Fin 8 => block[8 * i.val + k.val]'(by omega))) =
      Blake2b.loadBlock block.toList := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Blake2b.loadBlock]
  rw [wordFromLeBytes]
  refine congrArg Blake2b.wordLE (List.ext_getElem ?_ ?_)
  · simp only [Vector.length_toList, List.length_take, List.length_drop]; omega
  · intro k h1 h2
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_take, List.getElem_drop]

/-- The portable fold back into the state is Ironwood's: xor is associative. -/
theorem foldBack_eq (h : Vector Word 8) (w : Vector Word 16) :
    (Vector.ofFn fun i : Fin 8 => h[i] ^^^ (w[i.val] ^^^ w[i.val + 8])) =
      Vector.ofFn fun i : Fin 8 =>
        h.get i ^^^ w.get ⟨i.val, by omega⟩ ^^^ w.get ⟨i.val + 8, by omega⟩ := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Vector.get, Fin.getElem_fin]
  exact (UInt64.xor_assoc _ _ _).symm

/-- **The portable compression is Ironwood's `compress`.** On every block, state, byte count `t`
and final flag, with the last-node flag off. -/
theorem compressBlock_eq_compress (block : Vector UInt8 128) (h : Vector Word 8) (t : ℕ)
    (last : Bool) :
    Portable.compressBlock block h (BitVec.ofNat 128 t) (flagWord last) (flagWord false) =
      Blake2b.compress h (Blake2b.loadBlock block.toList) t last := by
  simp only [Portable.compressBlock, Blake2b.compress, Blake2b.compressWords, countLow_ofNat,
    countHigh_ofNat, loadBlock_eq, startVector_eq, round_eq_round, foldl_finRange_12, foldBack_eq]

/-- The portable `compress_block` refines `compress`. -/
theorem Portable.refines : Refines Portable.compressBlock := compressBlock_eq_compress

/-- The mixing function on four words and two message words: the new values of positions `a`,
`b`, `c`, `d`. -/
def gWords (a b c d x y : Word) : Word × Word × Word × Word :=
  let a := a + b + x
  let d := rotateRight (d ^^^ a) 32
  let c := c + d
  let b := rotateRight (b ^^^ c) 24
  let a := a + b + y
  let d := rotateRight (d ^^^ a) 16
  let c := c + d
  let b := rotateRight (b ^^^ c) 63
  (a, b, c, d)

/-- The portable `g` writes `gWords` of its four positions back into them. -/
theorem g_eq_set (v : Vector Word 16) (a b c d : Fin 16) (x y : Word)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    Portable.g v a b c d x y =
      ((((v.set a (gWords v[a] v[b] v[c] v[d] x y).1).set b
        (gWords v[a] v[b] v[c] v[d] x y).2.1).set c (gWords v[a] v[b] v[c] v[d] x y).2.2.1).set d
        (gWords v[a] v[b] v[c] v[d] x y).2.2.2) := by
  rw [g_eq_mix v a b c d x y hab hac had hbc hbd hcd]
  simp only [Blake2b.mix, Blake2b.upd, gWords, Vector.get, rotateRight]
  rfl

section reads

variable (v : Vector Word 16) (a b c d : Fin 16) (x y : Word)
  (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)

include hab hac had hbc hbd hcd

/-- After `g`, position `a` holds `gWords`' first value. -/
theorem g_get_a (i : ℕ) (hi : i < 16) (h : i = a.val) :
    (Portable.g v a b c d x y)[i] = (gWords v[a] v[b] v[c] v[d] x y).1 := by
  subst h
  rw [g_eq_set v a b c d x y hab hac had hbc hbd hcd]
  simp [
    Fin.val_ne_of_ne hab.symm, Fin.val_ne_of_ne hac.symm, Fin.val_ne_of_ne had.symm]

/-- After `g`, position `b` holds `gWords`' second value. -/
theorem g_get_b (i : ℕ) (hi : i < 16) (h : i = b.val) :
    (Portable.g v a b c d x y)[i] = (gWords v[a] v[b] v[c] v[d] x y).2.1 := by
  subst h
  rw [g_eq_set v a b c d x y hab hac had hbc hbd hcd]
  simp [
    Fin.val_ne_of_ne hbc.symm, Fin.val_ne_of_ne hbd.symm]

/-- After `g`, position `c` holds `gWords`' third value. -/
theorem g_get_c (i : ℕ) (hi : i < 16) (h : i = c.val) :
    (Portable.g v a b c d x y)[i] = (gWords v[a] v[b] v[c] v[d] x y).2.2.1 := by
  subst h
  rw [g_eq_set v a b c d x y hab hac had hbc hbd hcd]
  simp [Fin.val_ne_of_ne hcd.symm]

/-- After `g`, position `d` holds `gWords`' fourth value. -/
theorem g_get_d (i : ℕ) (hi : i < 16) (h : i = d.val) :
    (Portable.g v a b c d x y)[i] = (gWords v[a] v[b] v[c] v[d] x y).2.2.2 := by
  subst h
  rw [g_eq_set v a b c d x y hab hac had hbc hbd hcd]
  simp []

/-- `g` leaves every position other than `a`, `b`, `c`, `d` as it was. -/
theorem g_get_other (i : ℕ) (hi : i < 16)
    (h : i ≠ a.val ∧ i ≠ b.val ∧ i ≠ c.val ∧ i ≠ d.val) :
    (Portable.g v a b c d x y)[i] = v[i] := by
  rw [g_eq_set v a b c d x y hab hac had hbc hbd hcd]
  simp [Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2]

end reads

end Zcash.Common.Blake2bSimd
