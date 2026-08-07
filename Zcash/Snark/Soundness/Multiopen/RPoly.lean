import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.LinearAlgebra.Lagrange
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# The r-polynomial core: interpolants, node values, and identity-from-samples

Generic pieces for the claimed-evaluation binding: `poly_eq_of_agree_on_family` (two polynomials of
bounded degree agreeing on enough distinct points are equal — samples force identity),
`lagrangePoly` (the interpolant of one point set, taking the claimed value at each node), and
`lagrangePoly_eval` (the deployed fold `lagrangeEval` is the interpolant's evaluation, so deployed
identities transfer to the polynomial).

The polynomial theory here is Mathlib's, not reinvented: `lagrangePoly` is `Lagrange.interpolate`,
`lagrangePoly_eval_node` is `Lagrange.eval_interpolate_at_node`. Only the fold bridge is local:
the deployed check runs a hand-rolled `foldl` (`lagrangeEval`), and `foldl_range_add_eq_sum`,
`foldl_range_guardProd_eq_prod`, and `guardProd_eq_prod_erase` rewrite it into the `Finset`
sum/product Mathlib evaluates the interpolant to. CompPoly mirrors the same Mathlib defs, so
switching to it would not remove this bridge.
-/

namespace Zcash.Snark

open Polynomial CompPoly

/-- **Identity from samples.** Two polynomials whose difference has degree at most `d` and which
agree at `d + 1` pairwise-distinct points are equal. -/
theorem poly_eq_of_agree_on_family {d : ℕ} {P Q : CPoly}
    (hdeg : (P - Q).natDegree ≤ d)
    (ξ : Fin (d + 1) → Fp) (hξ : Function.Injective ξ)
    (heval : ∀ r, CPolynomial.eval (ξ r) P = CPolynomial.eval (ξ r) Q) : P = Q := by
  refine sub_eq_zero.mp (CompPoly.CPolynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    _ hξ (fun r => ?_) ?_)
  · rw [CompPoly.CPolynomial.eval_sub, heval r, sub_self]
  · simpa using Nat.lt_succ_of_le hdeg

/-- The `foldl`-accumulated sum over `List.range` is the finite sum — the outer fold of the
deployed combined evaluation. -/
theorem foldl_range_add_eq_sum (f : ℕ → Fp) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ih]

/-- The guarded `foldl` product over `List.range` is the guarded finite product — the inner
(basis) fold of the deployed combined evaluation, the skipped index carrying `1`. -/
theorem foldl_range_guardProd_eq_prod (g : ℕ → Fp) (i n : ℕ) :
    (List.range n).foldl (fun p j => if j = i then p else p * g j) 1
      = ∏ j ∈ Finset.range n, if j = i then 1 else g j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.prod_range_succ, ih]
      by_cases hn : n = i <;> simp [hn]

/-- A guarded product over the full range is the product over the erased set. -/
theorem guardProd_eq_prod_erase {n : ℕ} (h : Fin n → Fp) (i : Fin n) :
    (∏ j : Fin n, if j = i then 1 else h j) = ∏ j ∈ Finset.univ.erase i, h j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

/-- The interpolant of a point/value list: the `r`-polynomial of one point set. Indexed by the
point list's positions; values read by `getD` to match the deployed fold. -/
def lagrangePoly (points evals : List Fp) : CPoly :=
  CPolynomial.CLagrange.interpolate Finset.univ (fun i : Fin points.length => points[i])
    (fun i : Fin points.length => evals.getD (i : ℕ) 0)

/-- The interpolant's Mathlib image is Mathlib's interpolant, so the `Lagrange` theory applies. -/
theorem toPoly_lagrangePoly (points evals : List Fp) :
    (lagrangePoly points evals).toPoly =
      Lagrange.interpolate Finset.univ (fun i : Fin points.length => points[i])
        (fun i : Fin points.length => evals.getD (i : ℕ) 0) :=
  CPolynomial.CLagrange.cinterpolate_eq_interpolate

/-- The interpolant takes the claimed value at each node (pairwise-distinct nodes). -/
theorem lagrangePoly_eval_node {points evals : List Fp}
    (hdist : Function.Injective (fun i : Fin points.length => points[i]))
    (i : Fin points.length) :
    CPolynomial.eval points[i] (lagrangePoly points evals) = evals.getD (i : ℕ) 0 := by
  rw [CPolynomial.eval_toPoly, toPoly_lagrangePoly]
  exact Lagrange.eval_interpolate_at_node _ hdist.injOn (Finset.mem_univ i)

/-- The deployed combined-evaluation fold (`lagrangeEval`, `Verifier/Checks.lean`) is the
interpolant's evaluation at `x`, for pairwise-distinct nodes. Stepped through in the body: the
outer fold is the basis-weighted sum, each inner guarded fold the evaluated Lagrange basis. -/
theorem lagrangePoly_eval {points evals : List Fp}
    (_hdist : Function.Injective (fun i : Fin points.length => points[i])) (x : Fp) :
    CPolynomial.eval x (lagrangePoly points evals) = lagrangeEval x points evals := by
  classical
  -- The deployed fold, as a range-indexed sum of guarded products.
  have houter : lagrangeEval x points evals
      = ∑ i ∈ Finset.range points.length, evals.getD i 0
          * ∏ j ∈ Finset.range points.length,
              if j = i then 1
              else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0) := by
    show (List.range points.length).foldl (fun acc i =>
        acc + evals.getD i 0 * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) 0 = _
    rw [foldl_range_add_eq_sum (fun i => evals.getD i 0
      * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) points.length]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hstep : (fun (p : Fp) j => if j = i then p
        else p * (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))
        = fun (p : Fp) j => if j = i then p
        else p * ((x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) := by
      funext p j
      rw [mul_div_assoc]
    rw [hstep]
    exact foldl_range_guardProd_eq_prod
      (fun j => (x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) i points.length
  rw [houter, ← Fin.sum_univ_eq_sum_range (fun i => evals.getD i 0
    * ∏ j ∈ Finset.range points.length,
        if j = i then 1 else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))]
  rw [CPolynomial.eval_toPoly, toPoly_lagrangePoly, Lagrange.interpolate_apply,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]
  congr 1
  rw [Lagrange.basis, eval_prod,
    ← guardProd_eq_prod_erase
      (fun j => (Lagrange.basisDivisor points[i] points[j]).eval x) i,
    ← Fin.prod_univ_eq_prod_range (fun j =>
      if j = (i : ℕ) then 1
      else (x - points.getD j 0) / (points.getD (i : ℕ) 0 - points.getD j 0))]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · simp [hj]
  · rw [if_neg hj, if_neg (fun h => hj (Fin.val_inj.mp h)),
      List.getD_eq_getElem points 0 j.isLt, List.getD_eq_getElem points 0 i.isLt,
      Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_mul_inv,
      mul_comm]
    rfl

/-! ## The combined evaluation in closed form

The deployed `multiopenEval` folds per-set contributions by `x₂` and clears each set's
denominators pointwise; the closed forms below expose the `x₂`-power sum and the cleared
per-set term, the shapes the sample-identity substitution consumes. -/

/-- The per-set contribution's denominator fold in closed form: starting value times the product
of the inverses. -/
theorem foldl_mul_inv_eq_prod (x3 : Fp) (points : List Fp) (e : Fp) :
    points.foldl (fun e point => e * (x3 - point)⁻¹) e
      = e * ∏ j ∈ Finset.range points.length, (x3 - points.getD j 0)⁻¹ := by
  induction points generalizing e with
  | nil => simp
  | cons p l ih =>
      rw [List.foldl_cons, ih, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- The `x₂` fold of `multiopenEval` in closed power form: ascending `x₂`-powers carry the per-set
cleared contributions in reverse fold order (the initial `0` kills the top term). -/
theorem multiopenEval_powerForm (x2 x3 : Fp) (sets : List (List Fp × List Fp × Fp)) :
    multiopenEval x2 x3 sets
      = ∑ j ∈ Finset.range sets.length,
          x2 ^ j * (((sets.reverse.getD j ([], [], 0)).2.2
              - lagrangeEval x3 (sets.reverse.getD j ([], [], 0)).1
                  (sets.reverse.getD j ([], [], 0)).2.1)
            * ∏ m ∈ Finset.range (sets.reverse.getD j ([], [], 0)).1.length,
                (x3 - (sets.reverse.getD j ([], [], 0)).1.getD m 0)⁻¹) := by
  have hfg : (fun (msmEval : Fp) (s : List Fp × List Fp × Fp) =>
      msmEval * x2 + s.1.foldl (fun e point => e * (x3 - point)⁻¹)
        (s.2.2 - lagrangeEval x3 s.1 s.2.1))
      = fun acc s => x2 • acc + (s.2.2 - lagrangeEval x3 s.1 s.2.1)
          * ∏ m ∈ Finset.range s.1.length, (x3 - s.1.getD m 0)⁻¹ := by
    funext acc s
    rw [foldl_mul_inv_eq_prod, smul_eq_mul, mul_comm x2 acc]
  show sets.foldl (fun msmEval s =>
      msmEval * x2 + s.1.foldl (fun e point => e * (x3 - point)⁻¹)
        (s.2.2 - lagrangeEval x3 s.1 s.2.1)) 0 = _
  rw [hfg, foldl_smul_add_powerForm x2
    (fun s : List Fp × List Fp × Fp => (s.2.2 - lagrangeEval x3 s.1 s.2.1)
      * ∏ m ∈ Finset.range s.1.length, (x3 - s.1.getD m 0)⁻¹) ([], [], 0) sets 0,
    smul_zero, zero_add]
  simp only [smul_eq_mul]

/-- **Coefficients from a vanishing power sum.** A power sum `∑_{j<n} ξ^j · c j` is the evaluation
at `ξ` of the degree-`<n` polynomial `∑_{j<n} C(c j)·Xʲ`; if it vanishes at `n` pairwise-distinct
`ξ`, that polynomial is zero, so every coefficient `c i` (`i < n`) is zero. -/
theorem coeffs_zero_of_power_sum_vanishes {n : ℕ} (c : ℕ → Fp)
    (ξ : Fin n → Fp) (hξ : Function.Injective ξ)
    (hvanish : ∀ r, ∑ j ∈ Finset.range n, ξ r ^ j * c j = 0) (i : Fin n) :
    c i = 0 := by
  classical
  have hn : 0 < n := i.pos
  have hcast : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  set P : Polynomial Fp := ∑ j ∈ Finset.range n, Polynomial.C (c j) * Polynomial.X ^ j with hPdef
  have hdeg : P.natDegree ≤ n - 1 := by
    rw [hPdef, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun r : Fin (n - 1 + 1) => ξ (Fin.cast hcast r))
      (hξ.comp (Fin.cast_injective hcast)) (fun r => ?_)
      (by simpa using Nat.lt_succ_of_le hdeg)
    rw [hPdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hvanish (Fin.cast hcast r)]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hcoeff : P.coeff i = c i := by
    rw [hPdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single (i : ℕ)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hji
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hji h.symm), mul_zero]
    · intro hni; exact absurd (Finset.mem_range.mpr i.isLt) hni
  rw [hP0, Polynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

/-! ## Degree of the deployed `r`-polynomial -/

/-- The `r`-polynomial of a point set has degree below the number of nodes. -/
theorem lagrangePoly_natDegree_lt {points evals : List Fp} (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i])) :
    (lagrangePoly points evals).natDegree < points.length := by
  rw [CPolynomial.natDegree_toPoly, toPoly_lagrangePoly]
  set P := Lagrange.interpolate (Finset.univ : Finset (Fin points.length))
    (fun i : Fin points.length => points[i])
    (fun i : Fin points.length => evals.getD (i : ℕ) 0) with hP
  have hd : P.degree < (points.length : ℕ) := by
    have h := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin points.length)))
      (v := fun i : Fin points.length => points[i])
      (r := fun i : Fin points.length => evals.getD (i : ℕ) 0) hnode.injOn
    simpa [hP, Finset.card_univ, Fintype.card_fin] using h
  by_cases h0 : P = 0
  · rw [h0, Polynomial.natDegree_zero]; exact hlen
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hd

end Zcash.Snark
