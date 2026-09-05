import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# The pre-`x` quotient reconstruction

The constraint difference polynomial that `constraints_supply_derived` bounds is
`combine − hpolyP·(Xⁿ−1)`, where `hpolyP` decodes the *reassembled* vanishing commitment
`Σᵢ hᵢ·(xⁿ)ⁱ` — so `hpolyP` is `x`-dependent through `xⁿ`, and its bad set is not pinned before
the `x` squeeze. This module reconstructs the genuinely pre-`x` quotient

  `Hpoly(X) := Σᵢ X^(n·i)·hᵢ(X)`

from the piece polynomials `hᵢ` (chosen openings of the pre-`x` piece commitments `ps.hPieces`),
and proves the one fact the good-challenge argument needs: **`hpolyP` and `Hpoly` agree in value
at `x`** (`Xⁿ`-scaled coefficients meet `X^(n·i)` monomials under `(xⁿ)ⁱ = x^(n·i)`). So the
verifier's check at `x` is the pre-`x` polynomial `combine − Hpoly·(Xⁿ−1)` vanishing at `x`, whose
bad set is fixed before the squeeze.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero Msm.eval_appendTerm)

open CompPoly.CPolynomial

variable {d : ℕ}

/-- The reassembled quotient *polynomial* at scalar `xn`: `Σᵢ C(xnⁱ)·hᵢ(X)`. This is the polynomial
whose commitment is halo2's reassembled `h` (`Σᵢ hᵢ·(xⁿ)ⁱ`), read as a polynomial in `X` with
`xⁿ`-scaled pieces — the `x`-dependent form `hpolyP` decodes. -/
def reassembledQuotient (xn : Fp) (hp : Fin d → CPoly) : CPoly :=
  ∑ i : Fin d, C (xn ^ (i : ℕ)) * hp i

/-- The pre-`x` quotient polynomial `Σᵢ X^(n·i)·hᵢ(X)` — the reassembly with the scalar `xⁿ` lifted
to the monomial `X^(n·i)`. Pre-`x`: it mentions only the piece polynomials and `n`. -/
def preXQuotient (n : ℕ) (hp : Fin d → CPoly) : CPoly :=
  ∑ i : Fin d, X ^ (n * (i : ℕ)) * hp i

/-- **The reassembly and the pre-`x` quotient agree in value at `x`.** Each term matches under
`(xⁿ)ⁱ = x^(n·i)`, so the `x`-dependent reassembled `hpolyP` never needs to enter the pinned bad
set — its evaluation at `x` is the pre-`x` quotient's. -/
theorem reassembledQuotient_eval_eq_preXQuotient_eval (n : ℕ) (hp : Fin d → CPoly) (x : Fp) :
    (reassembledQuotient (x ^ n) hp).eval x = (preXQuotient n hp).eval x := by
  rw [reassembledQuotient, preXQuotient, eval_finsetSum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval_mul, eval_mul, eval_C, eval_pow,
    eval_X, ← pow_mul]

/-- **The verifier's quotient check equals the pre-`x` check at `x`.** Replacing the reassembled
`hpolyP` (evaluated at `x`) by the pre-`x` quotient leaves the difference polynomial's value at `x`
unchanged: `(combine − hpolyP·(Xⁿ−1)).eval x = (combine − Hpoly·(Xⁿ−1)).eval x`. So `x` is bad for
the `x`-dependent check iff it is bad for the pinned pre-`x` polynomial. -/
theorem quotientCheck_eval_eq_preX (combine : CPoly) (n : ℕ) (hp : Fin d → CPoly)
    (x : Fp) :
    (combine - reassembledQuotient (x ^ n) hp * (X ^ n - 1)).eval x
      = (combine - preXQuotient n hp * (X ^ n - 1)).eval x := by
  rw [eval_sub, eval_sub, eval_mul, eval_mul,
    reassembledQuotient_eval_eq_preXQuotient_eval]

/-- **Bad-set transport to the pre-`x` polynomial.** If `x` is bad for the `x`-dependent quotient
check (`combine − hpolyP·(Xⁿ−1)`), then the pre-`x` difference vanishes at `x`; unless that pre-`x`
polynomial is identically zero (the constraint holds as polynomials), `x` lands in its pinned bad
set. `hpolyP = reassembledQuotient (xⁿ) hp` is the decoded reassembly. -/
theorem mem_szBadSet_reassembled_imp (combine : CPoly) (n : ℕ) (hp : Fin d → CPoly)
    {x : Fp}
    (hx : x ∈ szBadSet (combine - reassembledQuotient (x ^ n) hp * (X ^ n - 1))) :
    x ∈ szBadSet (combine - preXQuotient n hp * (X ^ n - 1))
    ∨ combine - preXQuotient n hp * (X ^ n - 1) = 0 := by
  rw [mem_szBadSet] at hx
  by_cases hQ : combine - preXQuotient n hp * (X ^ n - 1) = 0
  · exact Or.inr hQ
  · refine Or.inl (mem_szBadSet.mpr ⟨hQ, ?_⟩)
    rw [← quotientCheck_eval_eq_preX]
    exact hx.2

/-! ## The commit-side reconstruction

The decoded quotient column opens the reassembled commitment `Σᵢ (xⁿ)ⁱ·Hᵢ`; the same element is
opened by the `(xⁿ)ⁱ`-scaled sum of the pieces' own openings. So the decoded column is that scaled
sum, or binding breaks — and its polynomial is `reassembledQuotient (xⁿ)` of the piece
polynomials, exactly the `x`-dependent form whose evaluation the identity above pins. -/

/-- `coeffsToPoly` is additive. -/
private theorem coeffsToPoly_add {m : ℕ} (a a' : Fin m → Fp) :
    coeffsToPoly (a + a') = coeffsToPoly a + coeffsToPoly a' := by
  rw [coeffsToPoly, coeffsToPoly, coeffsToPoly]
  simp only [Pi.add_apply, C_add, _root_.add_mul, Finset.sum_add_distrib]

/-- `coeffsToPoly` sends a scalar multiple to the constant-scaled polynomial. -/
private theorem coeffsToPoly_smul {m : ℕ} (c : Fp) (a : Fin m → Fp) :
    coeffsToPoly (c • a) = C c * coeffsToPoly a := by
  rw [coeffsToPoly, coeffsToPoly]
  simp only [Pi.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `coeffsToPoly` sends an `(xⁿ)ⁱ`-scaled coefficient sum to the reassembled quotient of the
piece polynomials: it is linear, so the scalar `(xⁿ)ⁱ` becomes the constant `C((xⁿ)ⁱ)`. -/
theorem coeffsToPoly_scaledSum {k : ℕ} (xn : Fp) (hp : Fin d → Fin (2 ^ k) → Fp) :
    coeffsToPoly (∑ i : Fin d, xn ^ (i : ℕ) • hp i)
      = reassembledQuotient xn (fun i => coeffsToPoly (hp i)) := by
  rw [reassembledQuotient]
  induction (Finset.univ : Finset (Fin d)) using Finset.induction with
  | empty => simp [coeffsToPoly]
  | @insert a s h ih =>
      rw [Finset.sum_insert h, Finset.sum_insert h, coeffsToPoly_add, coeffsToPoly_smul, ih]

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- `commit` over an `(xⁿ)ⁱ`-scaled finite sum distributes: `⟨Σᵢ cᵢ•aᵢ, G⟩ = Σᵢ cᵢ•⟨aᵢ, G⟩`. -/
private theorem commit_scaledSum (urs : URS G) (xn : Fp) (hp : Fin d → Fin (2 ^ urs.k) → Fp) :
    commit urs (∑ i : Fin d, xn ^ (i : ℕ) • hp i)
      = ∑ i : Fin d, xn ^ (i : ℕ) • commit urs (hp i) := by
  induction (Finset.univ : Finset (Fin d)) using Finset.induction with
  | empty => simp [commit]
  | @insert a s h ih =>
      rw [Finset.sum_insert h, Finset.sum_insert h, commit_add, commit_smul, ih]

/-- Computed form of quotient-piece binding.  A disagreement returns the actual augmented-basis
collision coefficients, so callers can feed this branch directly to their DLOG reduction. -/
def decodedQuotientEqReassembledOrRelationWitness (urs : URS G) (xn : Fp)
    {a : Fin (2 ^ urs.k) → Fp} {cu cw : Fp}
    {hp : Fin d → Fin (2 ^ urs.k) → Fp} {hpu hpw : Fin d → Fp} {H : Fin d → G}
    (hpiece : ∀ i, commit urs (hp i) + hpu i • urs.u + hpw i • urs.w = H i)
    (hopen : commit urs a + cu • urs.u + cw • urs.w = ∑ i : Fin d, xn ^ (i : ℕ) • H i) :
    (coeffsToPoly a = reassembledQuotient xn (fun i => coeffsToPoly (hp i))) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hsum : commit urs (∑ i : Fin d, xn ^ (i : ℕ) • hp i)
      + (∑ i : Fin d, xn ^ (i : ℕ) * hpu i) • urs.u
      + (∑ i : Fin d, xn ^ (i : ℕ) * hpw i) • urs.w
      = ∑ i : Fin d, xn ^ (i : ℕ) • H i := by
    rw [commit_scaledSum, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul, ← hpiece i, _root_.smul_add, _root_.smul_add]
  let sumCoeffs := ∑ i : Fin d, xn ^ (i : ℕ) • hp i
  let sumU := ∑ i : Fin d, xn ^ (i : ℕ) * hpu i
  let sumW := ∑ i : Fin d, xn ^ (i : ℕ) * hpw i
  have hcollision :
      commitGen urs.g a + cu • urs.u + cw • urs.w =
        commitGen urs.g sumCoeffs + sumU • urs.u + sumW • urs.w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen]
    exact hopen.trans hsum.symm
  exact match separateOrRelationWitness urs.g urs.u urs.w a sumCoeffs
      cu sumU cw sumW hcollision with
    | PSum.inr relation => PSum.inr relation
    | PSum.inl heq => PSum.inl (by
        rw [heq.1]
        exact coeffsToPoly_scaledSum xn hp)

omit [AddCommGroup G] [Module Fp G] in
/-- The reassembly fold as a `foldr`: `List.foldl` over the reversed pieces is `List.foldr` over
the pieces (`List.foldl_reverse`), which inducts forward without reverse-index bookkeeping. -/
private theorem vanishingHCommitment_foldr (urs : URS G) (xn : Fp) (hPieces : List G) :
    vanishingHCommitment urs.k xn hPieces
      = hPieces.foldr (fun c acc => (acc.scale xn).appendTerm 1 c) (Msm.zero urs.k Fp G) := by
  rw [vanishingHCommitment, List.foldl_reverse]

/-- **The reassembled vanishing commitment evaluates to `Σᵢ (xⁿ)ⁱ·Hᵢ`.** halo2's
`vanishingHCommitment` folds the quotient pieces `Σᵢ hᵢ·(xⁿ)ⁱ`; evaluated against the URS it is
that power-weighted sum, `Hᵢ` the `i`-th piece. -/
theorem vanishingHCommitment_eval (urs : URS G) (xn : Fp) :
    ∀ hPieces : List G,
      (vanishingHCommitment urs.k xn hPieces).eval urs
        = ∑ j ∈ Finset.range hPieces.length, xn ^ j • hPieces.getD j 0
  | [] => by simp [vanishingHCommitment_foldr, Msm.eval_zero]
  | a :: l => by
      rw [vanishingHCommitment_foldr, List.foldr_cons, Msm.eval_appendTerm, Msm.eval_scale,
        ← vanishingHCommitment_foldr urs xn l, vanishingHCommitment_eval urs xn l,
        List.length_cons, Finset.sum_range_succ', Finset.smul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, _root_.one_smul, pow_succ, _root_.smul_smul]
      rw [show (∑ j ∈ Finset.range l.length, (xn * xn ^ j) • l.getD j 0)
            = ∑ j ∈ Finset.range l.length, (xn ^ j * xn) • l.getD j 0 from
          Finset.sum_congr rfl (fun j _ => by rw [_root_.mul_comm]), _root_.add_comm]

end Zcash.Snark
