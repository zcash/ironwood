import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Argument.Lookup
import Zcash.Snark.Soundness.Argument.GrandProductBridge
import Zcash.Snark.Soundness.Argument.PermutationRows

/-!
# The lookup argument, assembled

`Soundness.Lookup.run_structure` proves the permuted columns' half: every permuted-input value
occurs somewhere in the permuted table. `GrandProductBridge` proves the product half: the running
product identity pins the permuted columns to the real ones — as two separate multiset identities,
since the lookup's two challenges sit on separate columns.

Neither alone says anything about the lookup. Together they do, and this module is that step: an
input value is a permuted-input value, which the run structure places in the permuted table, which
the multiset identities place in the real table.

* `lookup_subset_of_components` — the assembly, `{input} ⊆ {table}`, from the two column identities.
* `lookup_subset_of_prod_eval_eq` — the same with those identities supplied by the verifier's own
  product check and row constraints rather than assumed.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial Finset

/-- **The lookup assembly.** Every input value occurs in the table. The input identity moves an input
into the permuted columns, the run structure moves it across to the permuted table, and the table
identity moves it back to the real table. -/
theorem lookup_subset_of_components {ι : Type*} [Fintype ι] {a s inp tbl : ι → Fp}
    (hinp : Finset.univ.val.map a = Finset.univ.val.map inp)
    (htbl : Finset.univ.val.map s = Finset.univ.val.map tbl)
    (hrun : ∀ i, ∃ j, a i = s j) (i : ι) :
    ∃ j, inp i = tbl j := by
  -- the input value is a permuted-input value
  have hmem : inp i ∈ Finset.univ.val.map a := by
    rw [hinp]; exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨i₀, _, hi₀⟩ := Multiset.mem_map.mp hmem
  -- the run structure sends it to a permuted table entry
  obtain ⟨j, hj⟩ := hrun i₀
  -- which the table identity places in the real table
  have hsmem : s j ∈ Finset.univ.val.map tbl := by
    rw [← htbl]; exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
  obtain ⟨j', _, hj'⟩ := Multiset.mem_map.mp hsmem
  exact ⟨j', by rw [← hi₀, hj, ← hj']⟩

open Finset in
/-- **The lookup argument, closed at the verifier's checks.** The product identity is the telescoped
running product; `h0`/`hstep0`/`hstep` are the row constraints on the permuted columns; the two
challenge conditions are the priced root sets. The conclusion is the lookup relation: every input
value appears in the table. -/
theorem lookup_subset_of_prod_eval_eq {n : ℕ} (a s inp tbl : Fin (n + 1) → Fp) (β γ aPrev : Fp)
    (hprod : (∏ i, (β + a i)) * (∏ i, (γ + s i)) = (∏ i, (β + inp i)) * (∏ i, (γ + tbl i)))
    (hgoodγ : γ ∉ szBadSet (lookupProdDiffGamma (univ.val.map a) (univ.val.map s)
      (univ.val.map inp) (univ.val.map tbl) β))
    (hgoodβ : ∀ j, β ∉ szBadSet (lookupProdDiffCoeff (univ.val.map a) (univ.val.map s)
      (univ.val.map inp) (univ.val.map tbl) j))
    (h0 : a 0 = s 0) (hstep0 : a 0 = s 0 ∨ a 0 = aPrev)
    (hstep : ∀ i : Fin n, a i.succ = s i.succ ∨ a i.succ = a i.castSucc) (i : Fin (n + 1)) :
    ∃ j, inp i = tbl j := by
  have hmulti : ((univ.val.map a).map (fun u => β + u)).prod
        * ((univ.val.map s).map (fun u => γ + u)).prod
      = ((univ.val.map inp).map (fun u => β + u)).prod
        * ((univ.val.map tbl).map (fun u => γ + u)).prod := by
    simpa [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def] using hprod
  obtain ⟨hain, hstbl⟩ :=
    lookup_multisets_of_diff_eq_zero (lookup_multisets_of_prod_eval_eq hgoodγ hgoodβ hmulti)
  exact lookup_subset_of_components hain hstbl (run_structure a s aPrev h0 hstep0 hstep) i


/-! ## Reading the lookup constraints row by row

The same route as the permutation argument, on the lookup's five rules: the two boundary rules pin
the running product, the step rule is the recurrence, and the last two are exactly the run-structure
hypotheses `run_structure` consumes. -/

/-- The lookup evaluations as polynomials: the running product with its next-row rotation, and the
permuted input with its previous-row rotation. -/
def lookupEvalPolys (omega : Fp) (z aP sP : CPoly) :
    LookupEval (CPoly) :=
  { productEval := z
    productNextEval := comp z (C omega * X)
    permutedInputEval := aP
    permutedInputInvEval := comp aP (C omega⁻¹ * X)
    permutedTableEval := sP }

/-- The last-row rule in the lookup's order, `ℓ_last·(z² − z)`. -/
theorem running_product_end_flipped {lLastP zP : CPoly} {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣ lLastP * (zP ^ 2 - zP)) {r : Fp} (hr : r ^ n = 1)
    (hlast : lLastP.eval r ≠ 0) : zP.eval r = 0 ∨ zP.eval r = 1 :=
  running_product_end (by rwa [_root_.mul_comm] at hdvd) hr hlast

/-- **The lookup step rule is the recurrence.** At a row the verifier has switched on, the rule
vanishing says the running product advances by the ratio of the permuted factors to the compressed
input and table factors. -/
theorem lookup_row_recurrence {zP aP sP inpP tblP lLastP lBlindP : CPoly}
    (beta gamma : Fp) (omega : Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣
      ((zP.comp (C omega * X)) * (aP + C beta) * (sP + C gamma)
        - zP * (inpP + C beta) * (tblP + C gamma)) * (1 - (lLastP + lBlindP)))
    {i : ℕ} (hpow : (omega ^ i) ^ n = 1)
    (hactive : 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0) :
    zP.eval (omega ^ (i + 1)) * (aP.eval (omega ^ i) + beta) * (sP.eval (omega ^ i) + gamma)
      = zP.eval (omega ^ i) * (inpP.eval (omega ^ i) + beta)
        * (tblP.eval (omega ^ i) + gamma) := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_one, eval_comp_rotate] at hzero
  rcases mul_eq_zero.mp hzero with hbr | hact
  · rw [pow_succ, _root_.mul_comm (omega ^ i) omega]
    exact sub_eq_zero.mp hbr
  · exact absurd hact hactive

/-- The row-`0` rule `ℓ₀·(A′ − S′)` gives the run structure's base case. -/
theorem lookup_row_zero {l0P aP sP : CPoly} {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣ l0P * (aP - sP)) {r : Fp} (hr : r ^ n = 1)
    (hl0 : l0P.eval r ≠ 0) : aP.eval r = sP.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hl0
  · exact sub_eq_zero.mp h

/-- The run-structure rule `(A′ − S′)·(A′ − A′_prev)` gives the step disjunction: each row's
permuted input either matches the table there or repeats the previous row. -/
theorem lookup_row_step {aP sP aPrevP lLastP lBlindP : CPoly} {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣
      (aP - sP) * (aP - aPrevP) * (1 - (lLastP + lBlindP))) {r : Fp} (hr : r ^ n = 1)
    (hactive : 1 - (lLastP.eval r + lBlindP.eval r) ≠ 0) :
    aP.eval r = sP.eval r ∨ aP.eval r = aPrevP.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  simp only [eval_mul, eval_sub, eval_add, eval_one] at hzero
  rcases mul_eq_zero.mp hzero with hbr | hact
  · rcases mul_eq_zero.mp hbr with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · exact absurd hact hactive


open Finset in
/-- **The lookup's five rules, from the constraint identity.** Each rule is located inside the
deployed constraint list, so the identity's consequence — every constraint vanishes on the domain —
transfers to each rule individually. -/
theorem lookup_rules_dvd_of_identity (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z aP sP : CPoly) (inputExprs tableExprs : List (Expr Fp))
    {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : CPoly) {n : ℕ} (hn : n ≠ 0) (p : Fin np)
    (hlk : (lookupEvalPolys omega z aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j)) :
    (X ^ n - 1 : CPoly) ∣ l0P * (1 - z)
    ∧ (X ^ n - 1 : CPoly) ∣ lLastP * (z ^ 2 - z)
    ∧ (X ^ n - 1 : CPoly) ∣
        ((z.comp (C omega * X)) * (aP + C beta) * (sP + C gamma)
          - z * (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
              (inputExprs.map (Expr.map C)) + C beta)
            * (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
              (tableExprs.map (Expr.map C)) + C gamma)) * (1 - (lLastP + lBlindP))
    ∧ (X ^ n - 1 : CPoly) ∣ l0P * (aP - sP)
    ∧ (X ^ n - 1 : CPoly) ∣
        (aP - sP) * (aP - aP.comp (C omega⁻¹ * X)) * (1 - (lLastP + lBlindP)) := by
  have hall := constraints_dvd_of_good_y _ hpoly hn hidentity hgoodY
  have hmem : ∀ v : CPoly,
      v ∈ lookupExpressions (lookupEvalPolys omega z aP sP) (inputExprs.map (Expr.map C))
        (tableExprs.map (Expr.map C)) fixedCols (adviceCols p) (instanceCols p)
        (C theta) (C beta) (C gamma) l0P lLastP lBlindP →
      (X ^ n - 1 : CPoly) ∣ v := fun v hv =>
    hall v (mem_constraintPolys_of_mem_lookupExpressions fixedCols adviceCols instanceCols gates
      sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP p hlk hv)
  refine ⟨hmem _ ?_, hmem _ ?_, hmem _ ?_, hmem _ ?_, hmem _ ?_⟩ <;>
    simp [lookupExpressions_eq, lookupEvalPolys]

open Finset in
/-- **The lookup relation from the constraint identity.** Every hypothesis is either the verifier's
polynomial identity, a challenge avoiding a priced root set, or a condition on the verifying key's
constants. The conclusion is the lookup relation: each input value appears in the table — unless one
of the priced branches fires. -/
theorem deployed_lookup_subset_of_identity (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z aP sP : CPoly) (inputExprs tableExprs : List (Expr Fp))
    {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : CPoly) {n u : ℕ} (hn : n ≠ 0) (p : Fin np)
    (hlk : (lookupEvalPolys omega z aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0) :
    (∏ i ∈ range u, ((aP.eval (omega ^ i) + beta) * (sP.eval (omega ^ i) + gamma))
      = ∏ i ∈ range u, ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ i) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ i) + gamma))
    ∨ ∃ i ∈ range u, ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ i) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ i) + gamma) = 0 := by
  obtain ⟨hstart, hend, hstep, _, _⟩ := lookup_rules_dvd_of_identity omega beta gamma delta theta y
    chunkLen z aP sP inputExprs tableExprs fixedCols adviceCols instanceCols gates sets chunks
    lookups l0P lLastP lBlindP hpoly hn p hlk hidentity hgoodY
  refine prod_eq_or_factor_eq_zero (fun i => z.eval (omega ^ i)) _ _ ?_ ?_ ?_
  · intro i hi
    have := lookup_row_recurrence beta gamma omega hstep (hrow i) (hactive i hi)
    linear_combination this
  · simpa using running_product_start hstart (hrow 0) hl0
  · exact running_product_end_flipped hend (hrow u) hlast


open Finset in
/-- **The lookup relation, closed at the deployed constraints.** The product identity and the run
structure both come from the verifier's own rules, located inside the constraint list, so every
input value appears in the table — unless one of the priced branches fires. -/
theorem deployed_lookup_relation_of_identity (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z aP sP : CPoly) (inputExprs tableExprs : List (Expr Fp))
    {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : CPoly) {n m : ℕ} (hn : n ≠ 0) (p : Fin np)
    (homega : omega ≠ 0)
    (hlk : (lookupEvalPolys omega z aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m + 1, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ (m + 1)) ≠ 0)
    (hgoodγ : gamma ∉ szBadSet (lookupProdDiffGamma
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))) beta))
    (hgoodβ : ∀ j, beta ∉ szBadSet (lookupProdDiffCoeff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))) j))
    (i : Fin (m + 1)) :
    (∃ j : Fin (m + 1),
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))
          = (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ (j : ℕ)))
    ∨ ∃ t ∈ range (m + 1), ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ t) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ t) + gamma) = 0 := by
  obtain ⟨_, _, _, hrow0, hrunStep⟩ := lookup_rules_dvd_of_identity omega beta gamma delta theta y
    chunkLen z aP sP inputExprs tableExprs fixedCols adviceCols instanceCols gates sets chunks
    lookups l0P lLastP lBlindP hpoly hn p hlk hidentity hgoodY
  rcases deployed_lookup_subset_of_identity omega beta gamma delta theta y chunkLen z aP sP
      inputExprs tableExprs fixedCols adviceCols instanceCols gates sets chunks lookups
      l0P lLastP lBlindP hpoly hn p hlk hidentity hgoodY hrow hactive hl0 hlast with hprod | hzero
  · refine Or.inl ?_
    -- the row constraints give the run structure
    have h0 : aP.eval (omega ^ ((0 : Fin (m + 1)) : ℕ)) = sP.eval (omega ^ ((0 : Fin (m + 1)) : ℕ)) := by
      simpa using lookup_row_zero hrow0 (hrow 0) hl0
    have hstep : ∀ t : Fin m,
        aP.eval (omega ^ ((t.succ : Fin (m + 1)) : ℕ))
            = sP.eval (omega ^ ((t.succ : Fin (m + 1)) : ℕ))
          ∨ aP.eval (omega ^ ((t.succ : Fin (m + 1)) : ℕ))
            = aP.eval (omega ^ ((t.castSucc : Fin (m + 1)) : ℕ)) := by
      intro t
      have hprev : (aP.comp (C omega⁻¹ * X)).eval (omega ^ ((t : ℕ) + 1))
          = aP.eval (omega ^ (t : ℕ)) := by
        rw [eval_comp_rotate, pow_succ, _root_.mul_comm (omega ^ (t : ℕ)) omega, ← _root_.mul_assoc,
          inv_mul_cancel₀ homega, _root_.one_mul]
      have := lookup_row_step hrunStep (hrow ((t : ℕ) + 1))
        (hactive ((t : ℕ) + 1) (by omega))
      rw [hprev] at this
      simpa using this
    -- the product identity gives the two column identities
    have hsplit : (∏ j : Fin (m + 1), (beta + aP.eval (omega ^ (j : ℕ))))
          * (∏ j : Fin (m + 1), (gamma + sP.eval (omega ^ (j : ℕ))))
        = (∏ j : Fin (m + 1), (beta + (compressExprs fixedCols (adviceCols p) (instanceCols p)
              (C theta) (inputExprs.map (Expr.map C))).eval (omega ^ (j : ℕ))))
          * (∏ j : Fin (m + 1), (gamma + (compressExprs fixedCols (adviceCols p) (instanceCols p)
              (C theta) (tableExprs.map (Expr.map C))).eval (omega ^ (j : ℕ)))) := by
      simp only [← Finset.prod_mul_distrib]
      rw [Fin.prod_univ_eq_prod_range
            (fun x => (beta + aP.eval (omega ^ x)) * (gamma + sP.eval (omega ^ x))) (m + 1),
          Fin.prod_univ_eq_prod_range
            (fun x => (beta + (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
                (inputExprs.map (Expr.map C))).eval (omega ^ x))
              * (gamma + (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
                (tableExprs.map (Expr.map C))).eval (omega ^ x))) (m + 1)]
      simpa [_root_.add_comm] using hprod
    exact lookup_subset_of_prod_eval_eq _ _ _ _ beta gamma
      ((aP.comp (C omega⁻¹ * X)).eval (omega ^ ((0 : Fin (m + 1)) : ℕ)))
      hsplit hgoodγ hgoodβ h0 (Or.inl h0) hstep i
  · exact Or.inr hzero


/-! ## From compressed scalars to row tuples

Orchard's lookups have several columns; the verifier compresses each row by `θ` before the product
argument runs. The membership proved above is therefore between compressed scalars. These bring it
back to the tuples: the compression is the `foldPoly` of the row's expression values, so a `θ`
outside each pair's collision root set turns compressed equality into tuple equality. -/

/-- The values of a row of expressions at `ωⁱ` — the tuple the compression folds. -/
def rowTuple (fixedCols adviceCols instanceCols : ℕ → CPoly) (omega : Fp)
    (exprs : List (Expr Fp)) (i : ℕ) : List Fp :=
  exprs.map (fun e => e.eval (fun t => (fixedCols t).eval (omega ^ i))
    (fun t => (adviceCols t).eval (omega ^ i)) (fun t => (instanceCols t).eval (omega ^ i)))

/-- The θ-compression of a row of expression values is its fold polynomial at `θ`. -/
theorem compressExprs_eq_foldPoly_eval (fixedEvals adviceEvals instanceEvals : ℕ → Fp)
    (theta : Fp) (exprs : List (Expr Fp)) :
    compressExprs fixedEvals adviceEvals instanceEvals theta exprs
      = (foldPoly (exprs.map (fun e => e.eval fixedEvals adviceEvals instanceEvals))).eval theta := by
  rw [eval_foldPoly, compressExprs, List.foldl_map]

/-- The polynomial-level compression, evaluated at a row, is the row tuple's fold at `θ`. -/
theorem compress_eval_eq_foldPoly (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (theta : Fp) (exprs : List (Expr Fp)) (omega : Fp) (i : ℕ) :
    (compressExprs fixedCols adviceCols instanceCols (C theta)
        (exprs.map (Expr.map C))).eval (omega ^ i)
      = (foldPoly (rowTuple fixedCols adviceCols instanceCols omega exprs i)).eval theta := by
  have h := compressExprs_map (evalRingHom (omega ^ i)) fixedCols adviceCols instanceCols
    (C theta) (exprs.map (Expr.map C))
  simp only [coe_evalRingHom, eval_C] at h
  rw [h, List.map_map]
  have hid : ∀ e : Expr Fp,
      ((Expr.map (fun q : CPoly => q.eval (omega ^ i))) ∘ Expr.map C) e = e := by
    intro e
    simp only [Function.comp_apply, Expr.map_map, eval_C]
    exact Expr.map_id e
  rw [List.map_congr_left fun e _ => hid e]
  simp only [List.map_id']
  exact compressExprs_eq_foldPoly_eval _ _ _ theta exprs

open Finset in
/-- **The tuple-level lookup, from the constraint identity.** With `θ` outside each row pair's
collision root set, the compressed membership becomes membership of whole rows: every input row of
the lookup appears as a table row. The surviving branch is the priced vanishing factor. -/
theorem deployed_lookup_tuple_of_identity (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (zP aP sP : CPoly) (inputExprs tableExprs : List (Expr Fp))
    {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : CPoly) {n m : ℕ} (hn : n ≠ 0) (p : Fin np)
    (homega : omega ≠ 0)
    (harity : inputExprs.length = tableExprs.length)
    (hlk : (lookupEvalPolys omega zP aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m + 1, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ (m + 1)) ≠ 0)
    (hgoodγ : gamma ∉ szBadSet (lookupProdDiffGamma
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))) beta))
    (hgoodβ : ∀ j, beta ∉ szBadSet (lookupProdDiffCoeff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))) j))
    (hgoodθ : ∀ i j : Fin (m + 1), theta ∉ szBadSet
      (foldPoly (rowTuple fixedCols (adviceCols p) (instanceCols p) omega inputExprs (i : ℕ))
        - foldPoly (rowTuple fixedCols (adviceCols p) (instanceCols p) omega tableExprs (j : ℕ))))
    (i : Fin (m + 1)) :
    (∃ j : Fin (m + 1),
        rowTuple fixedCols (adviceCols p) (instanceCols p) omega inputExprs (i : ℕ)
          = rowTuple fixedCols (adviceCols p) (instanceCols p) omega tableExprs (j : ℕ))
    ∨ ∃ t ∈ range (m + 1), ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ t) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ t) + gamma) = 0 := by
  rcases deployed_lookup_relation_of_identity omega beta gamma delta theta y chunkLen zP aP sP
      inputExprs tableExprs fixedCols adviceCols instanceCols gates sets chunks lookups
      l0P lLastP lBlindP hpoly hn p homega hlk hidentity hgoodY hrow hactive hl0 hlast
      hgoodγ hgoodβ i with ⟨j, hj⟩ | hesc
  · refine Or.inl ⟨j, ?_⟩
    refine tuple_eq_of_foldPoly_eval_eq ?_ (hgoodθ i j) ?_
    · simp [rowTuple, harity]
    · rw [← compress_eval_eq_foldPoly, ← compress_eval_eq_foldPoly]
      exact hj
  · exact Or.inr hesc

end Zcash.Snark
