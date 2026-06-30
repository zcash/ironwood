import Mathlib
import Zcash.Snark.Core.Field
import Zcash.Snark.Verifier.Expressions

/-!
# The constraint layer: Schwartz–Zippel soundness of the vanishing check

The verifier's vanishing argument checks the quotient identity at the random evaluation point `x`: the
claimed quotient `h` satisfies `numerator = h · (Xⁿ − 1)`, where `numerator` is the gate / permutation /
lookup combination (the constraints combined by the challenge `y`, as assembled into `expected_h_eval`).
This module proves the soundness of that check by univariate Schwartz–Zippel (root counting): the
verifier samples one challenge, so the relevant bound is the number of roots of the constraint
polynomial.

* `quotientCheck` — the verifier's check at `x`: `numerator(x) = h(x) · (xⁿ − 1)`.
* `quotientCheck_sound` — if the identity fails as polynomials (the committed polynomials violate the
  constraint system), the check passes for at most `deg / |F|` of the challenges.
* `quotientCheck_complete` — if it holds as polynomials, the check passes at every challenge.

`numerator` and `h` are the polynomials carried by the proof; modeling `numerator` from the specific
Orchard gate `Expr`s (lifting `Zcash.Snark.Expr` to `Polynomial`) is the remaining connection to the
assembly — the soundness mechanism (root counting ⇒ `d/p`) is what this establishes.

Scope: what this establishes is **gate** satisfaction — the custom-gate portion of `numerator`. It does
not connect the permutation and lookup terms to the circuit-level copy and lookup constraints (the
combinatorial relations those arguments enforce); that is separate (tracked in #16). So "circuit
satisfaction" on this path means gate satisfaction.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- The verifier's vanishing/quotient check at the challenge `x`: the claimed quotient `h` satisfies the
constraint identity `numerator(x) = h(x) · (xⁿ − 1)`. `numerator` is the gate/permutation/lookup
combination; the verifier opens `h` to `numerator(x) / (xⁿ − 1)`. -/
@[reducible] def quotientCheck (numerator h : Polynomial Fp) (n : ℕ) (x : Fp) : Prop :=
  numerator.eval x = h.eval x * (x ^ n - 1)

/-- Constraint soundness (Schwartz–Zippel, univariate). If the quotient identity fails as polynomials —
`numerator ≠ h · (Xⁿ − 1)`, i.e. the committed polynomials violate the constraint system — then the
verifier's check passes for at most a `deg / |F|` fraction of the challenges. So a violated constraint
system is accepted with probability `≤ d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem quotientCheck_sound (numerator h : Polynomial Fp) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    ((univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0) / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) := by
  have hC : numerator - h * (X ^ n - 1) ≠ 0 := sub_ne_zero.mpr hne
  have hset : (univ.filter fun x => quotientCheck numerator h n x)
      = univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0 := by
    apply Finset.filter_congr
    intro x _
    simp only [quotientCheck, eval_sub, eval_mul, eval_pow, eval_X, eval_one, sub_eq_zero]
  rw [hset]
  have hcard : (univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0).card
      ≤ (numerator - h * (X ^ n - 1)).natDegree := by
    have he : (univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0)
        = (numerator - h * (X ^ n - 1)).roots.toFinset := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset,
        Polynomial.mem_roots hC, IsRoot.def]
    rw [he]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  gcongr

/-- Completeness, the companion to `quotientCheck_sound`: if the quotient identity holds as polynomials,
the verifier's check passes at every challenge. (Documented for the soundness/completeness pair; the
soundness path uses `quotientCheck_sound`.) -/
theorem quotientCheck_complete (numerator h : Polynomial Fp) (n : ℕ)
    (heq : numerator = h * (X ^ n - 1)) (x : Fp) : quotientCheck numerator h n x := by
  simp only [quotientCheck, heq, eval_mul, eval_sub, eval_pow, eval_X, eval_one]

/-- The constraint identity, derived from acceptance (not assumed). If the verifier's quotient check
passes at the challenge `x` and `x` is not a root of the constraint difference — the "good challenge"
event, whose complement is the `≤ deg/p` Schwartz–Zippel bad set bounded by `quotientCheck_sound` — then
the constraint identity holds as polynomials. This is the per-instance contrapositive that puts
`quotientCheck_sound` on the soundness path: acceptance and a good challenge give a committed-polynomial
set satisfying the constraint system, rather than taking that identity as a bare hypothesis. -/
theorem constraint_identity_of_accept (numerator h : Polynomial Fp) (n : ℕ) (x : Fp)
    (hcheck : quotientCheck numerator h n x)
    (hgood : numerator ≠ h * (X ^ n - 1) → (numerator - h * (X ^ n - 1)).eval x ≠ 0) :
    numerator = h * (X ^ n - 1) := by
  by_contra hne
  apply hgood hne
  have hval : numerator.eval x = (h * (X ^ n - 1)).eval x := by
    simpa [quotientCheck, eval_mul, eval_sub, eval_pow, eval_X, eval_one] using hcheck
  simp [eval_sub, hval]

/-! ## Lifting gate expressions to polynomials

The verifier evaluates each gate `Expr` at the claimed evaluations, which are the committed column
polynomials evaluated at `x`. `Expr.toPoly` lifts a gate to the corresponding univariate polynomial
(each query → its column polynomial), and `Expr.eval_toPoly` shows the lift commutes with evaluation:
evaluating the gate polynomial at `x` equals the verifier's gate evaluation. So the assembled gate value
(`Zcash.Snark.Expr.eval` at the evals) is a polynomial evaluation — the `numerator` of the
`quotientCheck` — connecting `quotientCheck_sound` to the actual Orchard gates. -/

/-- Lift a gate `Expr` to a univariate polynomial, replacing each query with its column polynomial. -/
noncomputable def Expr.toPoly (fixedCols adviceCols instanceCols : ℕ → Polynomial Fp) :
    Expr Fp → Polynomial Fp
  | .constant c => Polynomial.C c
  | .fixed i => fixedCols i
  | .advice i => adviceCols i
  | .instance i => instanceCols i
  | .negated a => -(Expr.toPoly fixedCols adviceCols instanceCols a)
  | .sum a b => Expr.toPoly fixedCols adviceCols instanceCols a
      + Expr.toPoly fixedCols adviceCols instanceCols b
  | .product a b => Expr.toPoly fixedCols adviceCols instanceCols a
      * Expr.toPoly fixedCols adviceCols instanceCols b
  | .scaled a c => Expr.toPoly fixedCols adviceCols instanceCols a * Polynomial.C c

/-- The lift commutes with evaluation: the gate polynomial at `x` equals the gate evaluated at the
columns' values at `x` — i.e. the verifier's gate evaluation is a polynomial evaluation. -/
theorem Expr.eval_toPoly (fixedCols adviceCols instanceCols : ℕ → Polynomial Fp) (x : Fp)
    (e : Expr Fp) :
    (Expr.toPoly fixedCols adviceCols instanceCols e).eval x
      = e.eval (fun i => (fixedCols i).eval x) (fun i => (adviceCols i).eval x)
          (fun i => (instanceCols i).eval x) := by
  induction e <;> simp_all [Expr.toPoly, Expr.eval]

/-! ## Combining the gates into the constraint numerator

The verifier combines all gate constraints by the challenge `y` into the single `numerator` of the
quotient identity (the `expected_h_eval` it compares against `h(x)·(xⁿ−1)`). Halo2 folds in list order as
`acc * y + v`; `combineGates` mirrors that order, and `eval_combineGates` shows evaluation commutes with
that fold — so the assembled `numerator` is a polynomial in the column polynomials, whose root count is
what `quotientCheck_sound` bounds. -/

/-- Evaluation commutes with Halo2's `acc * y + v` fold. -/
theorem eval_foldByY (y x : Fp) (acc : Polynomial Fp) (ps : List (Polynomial Fp)) :
    (ps.foldl (fun acc p => acc * Polynomial.C y + p) acc).eval x
      = (ps.map (fun p => p.eval x)).foldl (fun acc v => acc * y + v) (acc.eval x) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
        ih (acc * Polynomial.C y + p)

/-- The gate expressions lifted to polynomials, in verifier order. -/
noncomputable def gatePolys {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → Polynomial Fp)
    (gates : Fin n → Expr Fp) : List (Polynomial Fp) :=
  List.ofFn (fun i : Fin n => Expr.toPoly fixedCols adviceCols instanceCols (gates i))

/-- The constraint `numerator`: the gate polynomials (`Expr.toPoly`) combined by the same
`acc * y + v` fold that halo2 uses in `vanishing/verifier.rs`. -/
noncomputable def combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → Polynomial Fp)
    (y : Fp) (gates : Fin n → Expr Fp) : Polynomial Fp :=
  (gatePolys fixedCols adviceCols instanceCols gates).foldl (fun acc p => acc * Polynomial.C y + p) 0

/-- The structural fact that the combined numerator is the Halo2-order `y` fold of the gate evaluations:
the verifier's assembled gate value at `x` is `(combineGates …).eval x`, a single polynomial evaluation.
This connects the Orchard gates (`Expr`) to the `numerator` of `quotientCheck` / `quotientCheck_sound`. -/
theorem eval_combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → Polynomial Fp)
    (y : Fp) (gates : Fin n → Expr Fp) (x : Fp) :
    (combineGates fixedCols adviceCols instanceCols y gates).eval x
      = ((gatePolys fixedCols adviceCols instanceCols gates).map (fun p => p.eval x)).foldl
          (fun acc v => acc * y + v) 0 := by
  simp [combineGates, eval_foldByY]

end Zcash.Snark
