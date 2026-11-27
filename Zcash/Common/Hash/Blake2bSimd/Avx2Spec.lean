import Zcash.Common.Hash.Blake2bSimd.Avx2
import Zcash.Common.Hash.Blake2bSimd.X86Spec
import Zcash.Common.Hash.Blake2bSimd.PortableSpec
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

/-!
# `blake2b_simd`'s AVX2 compression is the portable one

`Avx2.compressBlock` and `Portable.compressBlock` give the same new state on every input
(`Avx2.compressBlock_eq_portable`), so the AVX2 one also refines Ironwood's `compress`.

The AVX2 code holds the sixteen working words as four rows of four (`rowsOf`). The proof shows
that each AVX2 round on the rows is the portable round on the working vector (`round_rowsOf`):

* `g1` then `g2` apply `gWords` to each lane (`g2_g1`), which is the portable `g` on the four
  columns (`colHalf`), since the columns are disjoint;
* with `diagonalize` and `undiagonalize` around them, they are `g` on the four diagonals
  (`diagHalf`);
* each `b0` holds the message words `SIGMA` names (`rounds_msgIdx`), checked for all twelve rows
  of `rounds`, the table read from the Rust, so an entry that selects the wrong words fails the
  build.
-/

namespace Zcash.Common.Blake2bSimd

open X86 Avx2

/-- `_mm256_shuffle_epi32` with `_MM_SHUFFLE!(1, 0, 3, 2)` swaps the 64-bit lanes in each
128-bit half. -/
theorem swapHalves (a : M256i) :
    mm256ShuffleEpi32 (Avx2.mmShuffle 1 0 3 2) a = #v[a[1], a[0], a[3], a[2]] := by
  have : mm256ShuffleEpi32 (Avx2.mmShuffle 1 0 3 2) a =
      ofLanes32 (shuffle (lanes32 a) (lanes32 a) #v[2, 3, 0, 1, 6, 7, 4, 5]) := rfl
  rw [this]
  apply Vector.ext
  intro w hw
  interval_cases w
  · rw [ofLanes32_shuffle a a _ 0 (by omega) 1 (by omega) rfl rfl]
    exact append_getElem_lt a a 1 (by omega)
  · rw [ofLanes32_shuffle a a _ 1 (by omega) 0 (by omega) rfl rfl]
    exact append_getElem_lt a a 0 (by omega)
  · rw [ofLanes32_shuffle a a _ 2 (by omega) 3 (by omega) rfl rfl]
    exact append_getElem_lt a a 3 (by omega)
  · rw [ofLanes32_shuffle a a _ 3 (by omega) 2 (by omega) rfl rfl]
    exact append_getElem_lt a a 2 (by omega)

/-- `_mm256_permute4x64_epi64` with `_MM_SHUFFLE!(2, 1, 0, 3)` rotates the lanes up by one. -/
theorem permute2103 (a : M256i) :
    mm256Permute4x64Epi64 (Avx2.mmShuffle 2 1 0 3) a = #v[a[3], a[0], a[1], a[2]] := by
  apply Vector.ext
  intro i hi
  rw [mm256Permute4x64Epi64, shuffle_getElem]
  interval_cases i
  · exact append_getElem_lt a _ 3 (by omega)
  · exact append_getElem_lt a _ 0 (by omega)
  · exact append_getElem_lt a _ 1 (by omega)
  · exact append_getElem_lt a _ 2 (by omega)

/-- `_mm256_permute4x64_epi64` with `_MM_SHUFFLE!(1, 0, 3, 2)` rotates the lanes by two. -/
theorem permute1032 (a : M256i) :
    mm256Permute4x64Epi64 (Avx2.mmShuffle 1 0 3 2) a = #v[a[2], a[3], a[0], a[1]] := by
  apply Vector.ext
  intro i hi
  rw [mm256Permute4x64Epi64, shuffle_getElem]
  interval_cases i
  · exact append_getElem_lt a _ 2 (by omega)
  · exact append_getElem_lt a _ 3 (by omega)
  · exact append_getElem_lt a _ 0 (by omega)
  · exact append_getElem_lt a _ 1 (by omega)

/-- `_mm256_permute4x64_epi64` with `_MM_SHUFFLE!(0, 3, 2, 1)` rotates the lanes down by one. -/
theorem permute0321 (a : M256i) :
    mm256Permute4x64Epi64 (Avx2.mmShuffle 0 3 2 1) a = #v[a[1], a[2], a[3], a[0]] := by
  apply Vector.ext
  intro i hi
  rw [mm256Permute4x64Epi64, shuffle_getElem]
  interval_cases i
  · exact append_getElem_lt a _ 1 (by omega)
  · exact append_getElem_lt a _ 2 (by omega)
  · exact append_getElem_lt a _ 3 (by omega)
  · exact append_getElem_lt a _ 0 (by omega)

/-- `rot n`: each lane rotated right by `n` places, for `0 < n`. -/
theorem rot_eq (n : Fin 64) (hn : 0 < n.val) (x : M256i) :
    Avx2.rot n x = x.map (rotateRight · (UInt64.ofNat n.val)) := by
  apply Vector.ext
  intro i hi
  have h1 : ¬ (⟨n.val, by omega⟩ : Fin 256).val ≥ 64 := by
    simp only [ge_iff_le, Nat.not_le]; omega
  have h2 : ¬ (⟨64 - n.val, by omega⟩ : Fin 256).val ≥ 64 := by
    simp only [ge_iff_le, Nat.not_le]; omega
  simp only [Avx2.rot, mm256OrSi256, mm256SrliEpi64, mm256SlliEpi64, if_neg h1, if_neg h2,
    Vector.getElem_zipWith, Vector.getElem_map]
  rw [rotateRight, Blake2b.rotr]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_sub, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have := n.isLt
  rw [show UInt64.toNat 64 = 64 from rfl]
  omega

/-- Addition modulo `2^64` reordered: AVX2 adds the message word before `b`, portable after. -/
theorem add_swap (a m b : Word) : a + m + b = a + b + m := by
  rw [UInt64.add_assoc, UInt64.add_comm m b, ← UInt64.add_assoc]

/-- `g1` then `g2` mix each lane of the rows with that lane of the message vectors. -/
theorem g2_g1 (a b c d x y : M256i) :
    g2 (g1 (a, b, c, d) x) y =
      (Vector.ofFn fun l : Fin 4 => (gWords a[l] b[l] c[l] d[l] x[l] y[l]).1,
       Vector.ofFn fun l : Fin 4 => (gWords a[l] b[l] c[l] d[l] x[l] y[l]).2.1,
       Vector.ofFn fun l : Fin 4 => (gWords a[l] b[l] c[l] d[l] x[l] y[l]).2.2.1,
       Vector.ofFn fun l : Fin 4 => (gWords a[l] b[l] c[l] d[l] x[l] y[l]).2.2.2) := by
  simp only [g1, g2, rot_eq 32 (by decide), rot_eq 24 (by decide), rot_eq 16 (by decide),
    rot_eq 63 (by decide), mm256AddEpi64, mm256XorSi256]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
  · apply Vector.ext
    intro l hl
    simp only [Vector.getElem_zipWith, Vector.getElem_map, Vector.getElem_ofFn, gWords,
      Fin.getElem_fin,
      show UInt64.ofNat ((32 : Fin 64) : ℕ) = 32 from rfl,
      show UInt64.ofNat ((24 : Fin 64) : ℕ) = 24 from rfl,
      show UInt64.ofNat ((16 : Fin 64) : ℕ) = 16 from rfl,
      show UInt64.ofNat ((63 : Fin 64) : ℕ) = 63 from rfl]
    rw [add_swap a[l] x[l] b[l]]
    try rw [add_swap (a[l] + b[l] + x[l]) y[l]]

/-- The working vector as AVX2's four rows. -/
def rowsOf (v : Vector Word 16) : Rows :=
  (#v[v[0], v[1], v[2], v[3]], #v[v[4], v[5], v[6], v[7]], #v[v[8], v[9], v[10], v[11]],
   #v[v[12], v[13], v[14], v[15]])

/-- The portable round's first half: `g` on the four columns. -/
def colG (v : Vector Word 16) (x y : M256i) : Vector Word 16 :=
  Portable.g (Portable.g (Portable.g (Portable.g v 0 4 8 12 x[0] y[0]) 1 5 9 13 x[1] y[1])
    2 6 10 14 x[2] y[2]) 3 7 11 15 x[3] y[3]

/-- Row `a` after `colG`: lane `l` is `gWords`' first value on column `l`. -/
theorem colG_row_a (v : Vector Word 16) (x y : M256i) :
    (rowsOf (colG v x y)).1 = Vector.ofFn fun l : Fin 4 =>
      (gWords (rowsOf v).1[l] (rowsOf v).2.1[l] (rowsOf v).2.2.1[l] (rowsOf v).2.2.2[l]
        x[l] y[l]).1 := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, colG]
  interval_cases l <;>
    simp (disch := decide) only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, g_get_a,
      g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `b` after `colG`: lane `l` is `gWords`' second value on column `l`. -/
theorem colG_row_b (v : Vector Word 16) (x y : M256i) :
    (rowsOf (colG v x y)).2.1 = Vector.ofFn fun l : Fin 4 =>
      (gWords (rowsOf v).1[l] (rowsOf v).2.1[l] (rowsOf v).2.2.1[l] (rowsOf v).2.2.2[l]
        x[l] y[l]).2.1 := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, colG]
  interval_cases l <;>
    simp (disch := decide) only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, g_get_b,
      g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `c` after `colG`: lane `l` is `gWords`' third value on column `l`. -/
theorem colG_row_c (v : Vector Word 16) (x y : M256i) :
    (rowsOf (colG v x y)).2.2.1 = Vector.ofFn fun l : Fin 4 =>
      (gWords (rowsOf v).1[l] (rowsOf v).2.1[l] (rowsOf v).2.2.1[l] (rowsOf v).2.2.2[l]
        x[l] y[l]).2.2.1 := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, colG]
  interval_cases l <;>
    simp (disch := decide) only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      g_get_c, g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `d` after `colG`: lane `l` is `gWords`' fourth value on column `l`. -/
theorem colG_row_d (v : Vector Word 16) (x y : M256i) :
    (rowsOf (colG v x y)).2.2.2 = Vector.ofFn fun l : Fin 4 =>
      (gWords (rowsOf v).1[l] (rowsOf v).2.1[l] (rowsOf v).2.2.1[l] (rowsOf v).2.2.2[l]
        x[l] y[l]).2.2.2 := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, colG]
  interval_cases l <;>
    simp (disch := decide) only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      g_get_d, g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- `g1` then `g2` on the rows are the portable `g` on the four columns. -/
theorem colHalf (v : Vector Word 16) (x y : M256i) :
    g2 (g1 (rowsOf v) x) y = rowsOf (colG v x y) := by
  rw [g2_g1]
  exact Prod.ext (colG_row_a v x y).symm
    (Prod.ext (colG_row_b v x y).symm (Prod.ext (colG_row_c v x y).symm (colG_row_d v x y).symm))

/-- The portable round's second half: `g` on the four diagonals. -/
def diagG (v : Vector Word 16) (x y : M256i) : Vector Word 16 :=
  Portable.g (Portable.g (Portable.g (Portable.g v 0 5 10 15 x[1] y[1]) 1 6 11 12 x[2] y[2])
    2 7 8 13 x[3] y[3]) 3 4 9 14 x[0] y[0]

/-- `diagonalize` lines the diagonals up as columns: lane `l` of the rows holds the diagonal that
starts at row `b`'s lane `l`. -/
theorem diagonalize_rowsOf (v : Vector Word 16) :
    diagonalize (rowsOf v) =
      (#v[v[3], v[0], v[1], v[2]], #v[v[4], v[5], v[6], v[7]], #v[v[9], v[10], v[11], v[8]],
       #v[v[14], v[15], v[12], v[13]]) := by
  simp only [diagonalize, rowsOf, permute2103, permute1032, permute0321]
  rfl

/-- `undiagonalize` rotates rows `a`, `c`, `d` back. -/
theorem undiagonalize_eq (a b c d : M256i) :
    undiagonalize (a, b, c, d) =
      (#v[a[1], a[2], a[3], a[0]], b, #v[c[3], c[0], c[1], c[2]], #v[d[2], d[3], d[0], d[1]]) := by
  simp only [undiagonalize, permute2103, permute1032, permute0321]

/-- Row `a` after `diagG`, position by position. -/
theorem diagG_row_a (v : Vector Word 16) (x y : M256i) :
    (rowsOf (diagG v x y)).1 =
      #v[(gWords v[0] v[5] v[10] v[15] x[1] y[1]).1,
      (gWords v[1] v[6] v[11] v[12] x[2] y[2]).1,
      (gWords v[2] v[7] v[8] v[13] x[3] y[3]).1,
      (gWords v[3] v[4] v[9] v[14] x[0] y[0]).1] := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, diagG]
  interval_cases l <;>
    simp (disch := decide) only [Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, g_get_a,
      g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `b` after `diagG`, position by position. -/
theorem diagG_row_b (v : Vector Word 16) (x y : M256i) :
    (rowsOf (diagG v x y)).2.1 =
      #v[(gWords v[3] v[4] v[9] v[14] x[0] y[0]).2.1,
      (gWords v[0] v[5] v[10] v[15] x[1] y[1]).2.1,
      (gWords v[1] v[6] v[11] v[12] x[2] y[2]).2.1,
      (gWords v[2] v[7] v[8] v[13] x[3] y[3]).2.1] := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, diagG]
  interval_cases l <;>
    simp (disch := decide) only [Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, g_get_b,
      g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `c` after `diagG`, position by position. -/
theorem diagG_row_c (v : Vector Word 16) (x y : M256i) :
    (rowsOf (diagG v x y)).2.2.1 =
      #v[(gWords v[2] v[7] v[8] v[13] x[3] y[3]).2.2.1,
      (gWords v[3] v[4] v[9] v[14] x[0] y[0]).2.2.1,
      (gWords v[0] v[5] v[10] v[15] x[1] y[1]).2.2.1,
      (gWords v[1] v[6] v[11] v[12] x[2] y[2]).2.2.1] := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, diagG]
  interval_cases l <;>
    simp (disch := decide) only [Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      g_get_c, g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- Row `d` after `diagG`, position by position. -/
theorem diagG_row_d (v : Vector Word 16) (x y : M256i) :
    (rowsOf (diagG v x y)).2.2.2 =
      #v[(gWords v[1] v[6] v[11] v[12] x[2] y[2]).2.2.2,
      (gWords v[2] v[7] v[8] v[13] x[3] y[3]).2.2.2,
      (gWords v[3] v[4] v[9] v[14] x[0] y[0]).2.2.2,
      (gWords v[0] v[5] v[10] v[15] x[1] y[1]).2.2.2] := by
  apply Vector.ext
  intro l hl
  simp only [rowsOf, diagG]
  interval_cases l <;>
    simp (disch := decide) only [Fin.getElem_fin, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      g_get_d, g_get_other, Fin.coe_ofNat_eq_mod, Nat.reduceMod]

/-- `diagonalize`, `g1`, `g2`, `undiagonalize` on the rows are the portable `g` on the four
diagonals. -/
theorem diagHalf (v : Vector Word 16) (x y : M256i) :
    undiagonalize (g2 (g1 (diagonalize (rowsOf v)) x) y) = rowsOf (diagG v x y) := by
  rw [diagonalize_rowsOf, g2_g1, undiagonalize_eq]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rw [diagG_row_a]
    apply Vector.ext
    intro l hl
    interval_cases l <;> simp [Vector.getElem_ofFn]
  · rw [diagG_row_b]
    apply Vector.ext
    intro l hl
    interval_cases l <;> simp [Vector.getElem_ofFn]
  · rw [diagG_row_c]
    apply Vector.ext
    intro l hl
    interval_cases l <;> simp [Vector.getElem_ofFn]
  · rw [diagG_row_d]
    apply Vector.ext
    intro l hl
    interval_cases l <;> simp [Vector.getElem_ofFn]

/-- The eight AVX2 message vectors in terms of the sixteen message words: vector `k` holds words
`2k` and `2k + 1` in both halves. -/
def msgVecs (w : Vector Word 16) : Vector M256i 8 :=
  Vector.ofFn fun k : Fin 8 =>
    #v[w[2 * k.val], w[2 * k.val + 1], w[2 * k.val], w[2 * k.val + 1]]

/-- Message word `2x`, the low lane of message vector `x`. -/
def lowWord (x : Fin 8) : Fin 16 := ⟨2 * x.val, by omega⟩

/-- Message word `2x + 1`, the high lane of message vector `x`. -/
def highWord (x : Fin 8) : Fin 16 := ⟨2 * x.val + 1, by omega⟩

/-- The message word each lane of a `Shuffle` of `msgVecs` holds. -/
def Avx2.Shuffle.idx : Shuffle → Fin 4 → Fin 16
  | .lo x y => ![lowWord x, lowWord y, lowWord x, lowWord y]
  | .hi x y => ![highWord x, highWord y, highWord x, highWord y]
  | .alignr x y => ![highWord y, lowWord x, highWord y, lowWord x]
  | .blend x y => ![lowWord y, highWord x, lowWord y, highWord x]
  | .swap x => ![highWord x, lowWord x, highWord x, lowWord x]

/-- A `Shuffle` of `msgVecs w` holds the message words `idx` names. -/
theorem Avx2.Shuffle.apply_msgVecs (w : Vector Word 16) (t : Shuffle) :
    t.apply (msgVecs w) = Vector.ofFn fun l => w[t.idx l] := by
  cases t <;>
  simp only [Shuffle.apply, unpacklo, unpackhi, alignr8, blend33, swapHalves] <;>
  · apply Vector.ext
    intro l hl
    interval_cases l <;> simp [msgVecs, Avx2.Shuffle.idx, lowWord, highWord]

/-- The message word lane `l` of `b0 m t` holds: the low half from `t.1`, the high from `t.2`. -/
def msgIdx (t : Shuffle × Shuffle) (l : Fin 4) : Fin 16 :=
  if l.val < 2 then t.1.idx l else t.2.idx l

/-- `b0` of `msgVecs w` holds the message words `msgIdx` names. -/
theorem b0_msgVecs (w : Vector Word 16) (t : Shuffle × Shuffle) :
    b0 (msgVecs w) t = Vector.ofFn fun l => w[msgIdx t l] := by
  rw [b0, blendF0, Avx2.Shuffle.apply_msgVecs, Avx2.Shuffle.apply_msgVecs]
  apply Vector.ext
  intro l hl
  interval_cases l <;> simp [msgIdx]

/-- Each round's shuffles select the message words `SIGMA` names: the four column steps' first
and second words, then the four diagonal steps', with the diagonal starting at row `b`'s lane
`l` in lane `l`. -/
theorem rounds_msgIdx (r : Fin 12) :
    Vector.ofFn (msgIdx rounds[r][0]) = #v[SIGMA[r][0], SIGMA[r][2], SIGMA[r][4], SIGMA[r][6]] ∧
    Vector.ofFn (msgIdx rounds[r][1]) = #v[SIGMA[r][1], SIGMA[r][3], SIGMA[r][5], SIGMA[r][7]] ∧
    Vector.ofFn (msgIdx rounds[r][2]) =
      #v[SIGMA[r][14], SIGMA[r][8], SIGMA[r][10], SIGMA[r][12]] ∧
    Vector.ofFn (msgIdx rounds[r][3]) =
      #v[SIGMA[r][15], SIGMA[r][9], SIGMA[r][11], SIGMA[r][13]] := by
  revert r
  decide

/-- Reading the message words through an index table equal to `#v[a, b, c, d]`. -/
theorem ofFn_get_of_eq (w : Vector Word 16) (f : Fin 4 → Fin 16) (a b c d : Fin 16)
    (h : Vector.ofFn f = #v[a, b, c, d]) :
    (Vector.ofFn fun l => w[f l]) = #v[w[a], w[b], w[c], w[d]] := by
  have h0 : f 0 = a := by simpa using congrArg (·[0]) h
  have h1 : f 1 = b := by simpa using congrArg (·[1]) h
  have h2 : f 2 = c := by simpa using congrArg (·[2]) h
  have h3 : f 3 = d := by simpa using congrArg (·[3]) h
  apply Vector.ext
  intro l hl
  interval_cases l <;> simp [h0, h1, h2, h3]

/-- AVX2 round `r` on the rows is portable round `r` on the working vector. -/
theorem round_rowsOf (r : Fin 12) (w v : Vector Word 16) :
    Avx2.round (msgVecs w) rounds[r] (rowsOf v) = rowsOf (Portable.round r w v) := by
  obtain ⟨h0, h1, h2, h3⟩ := rounds_msgIdx r
  rw [Avx2.round, colHalf, diagHalf, b0_msgVecs, b0_msgVecs, b0_msgVecs, b0_msgVecs,
    ofFn_get_of_eq w _ _ _ _ _ h0, ofFn_get_of_eq w _ _ _ _ _ h1, ofFn_get_of_eq w _ _ _ _ _ h2,
    ofFn_get_of_eq w _ _ _ _ _ h3]
  rfl

/-- The AVX2 message vectors are the portable message words, two to a vector. -/
theorem avx2_msg_eq (block : Vector UInt8 128) :
    (Vector.ofFn fun k : Fin 8 =>
      mm256Broadcastsi128Si256 (mmLoaduSi128 (Vector.ofFn fun i : Fin 16 =>
        block[16 * k.val + i.val]'(by omega)))) =
      msgVecs (Vector.ofFn fun i : Fin 16 =>
        wordFromLeBytes (Vector.ofFn fun k : Fin 8 => block[8 * i.val + k.val]'(by omega))) := by
  apply Vector.ext
  intro k hk
  apply Vector.ext
  intro l hl
  simp only [Vector.getElem_ofFn, mm256Broadcastsi128Si256, shuffle_getElem, msgVecs]
  interval_cases l <;>
  simp only [mmLoaduSi128, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, Fin.coe_ofNat_eq_mod] <;>
  rw [append_getElem_lt _ _ _ (by omega), Vector.getElem_ofFn] <;>
  · refine congrArg wordFromLeBytes ?_
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    congr 1
    omega

/-- A fold over the twelve rounds of `rounds`, unrolled. -/
theorem foldl_rounds {α : Type} (f : α → Vector (Shuffle × Shuffle) 4 → α) (s : α) :
    rounds.toList.foldl f s =
      f (f (f (f (f (f (f (f (f (f (f (f s
        rounds[(0 : Fin 12)]) rounds[(1 : Fin 12)]) rounds[(2 : Fin 12)]) rounds[(3 : Fin 12)])
        rounds[(4 : Fin 12)]) rounds[(5 : Fin 12)]) rounds[(6 : Fin 12)]) rounds[(7 : Fin 12)])
        rounds[(8 : Fin 12)]) rounds[(9 : Fin 12)]) rounds[(10 : Fin 12)]) rounds[(11 : Fin 12)] :=
  rfl

/-- The AVX2 final fold: each state half xored with the two rows over it. -/
theorem avx2_foldBack (words : Vector Word 8) (V : Vector Word 16) :
    mm256StoreuSi256 (mm256XorSi256 (mm256XorSi256 (rowsOf V).1 (rowsOf V).2.2.1)
        (mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => words[i.val]))) ++
      mm256StoreuSi256 (mm256XorSi256 (mm256XorSi256 (rowsOf V).2.1 (rowsOf V).2.2.2)
        (mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => words[i.val + 4]))) =
      Vector.ofFn fun i : Fin 8 => words[i] ^^^ (V[i.val] ^^^ V[i.val + 8]) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, Vector.getElem_append, UInt64.xor_comm]
  simp only [mm256StoreuSi256, mm256XorSi256, mm256LoaduSi256, Vector.getElem_zipWith,
    Vector.getElem_ofFn, Fin.getElem_fin]
  interval_cases i <;> rfl

/-- The twelve AVX2 rounds are the twelve portable rounds. -/
theorem rounds_rowsOf (w v : Vector Word 16) :
    rounds.toList.foldl (fun s r => Avx2.round (msgVecs w) r s) (rowsOf v) =
      rowsOf (Portable.round 11 w (Portable.round 10 w (Portable.round 9 w (Portable.round 8 w
        (Portable.round 7 w (Portable.round 6 w (Portable.round 5 w (Portable.round 4 w
        (Portable.round 3 w (Portable.round 2 w (Portable.round 1 w
        (Portable.round 0 w v)))))))))))) := by
  rw [foldl_rounds]
  simp only [round_rowsOf]

/-- AVX2's four starting rows are the portable starting vector's rows. -/
theorem init_rows (h iv : Vector Word 8) (e0 e1 e2 e3 : Word) :
    (mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => h[i.val]),
      mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => h[i.val + 4]),
      mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => iv[i.val]),
      mm256XorSi256 (mm256LoaduSi256 (Vector.ofFn fun i : Fin 4 => iv[i.val + 4]))
        (mm256SetrEpi64x e0 e1 e2 e3)) =
    rowsOf #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], iv[0], iv[1], iv[2], iv[3],
      iv[4] ^^^ e0, iv[5] ^^^ e1, iv[6] ^^^ e2, iv[7] ^^^ e3] := by
  simp only [rowsOf, mm256LoaduSi256, mm256XorSi256, mm256SetrEpi64x]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
  · apply Vector.ext
    intro i hi
    interval_cases i <;> simp

/-- **The AVX2 compression is the portable one.** On every block, state, count and pair of flag
words. -/
theorem Avx2.compressBlock_eq_portable (block : Vector UInt8 128) (words : Vector Word 8)
    (count : Count) (lastBlock lastNode : Word) :
    Avx2.compressBlock block words count lastBlock lastNode =
      Portable.compressBlock block words count lastBlock lastNode := by
  rw [Avx2.compressBlock, Portable.compressBlock]
  simp only [init_rows, avx2_msg_eq, rounds_rowsOf]
  exact avx2_foldBack _ _

/-- The AVX2 `compress_block` refines `compress`. -/
theorem Avx2.refines : Refines Avx2.compressBlock := fun block h t last => by
  rw [Avx2.compressBlock_eq_portable]; exact compressBlock_eq_compress block h t last

end Zcash.Common.Blake2bSimd
