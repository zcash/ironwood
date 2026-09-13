import Zcash.Common.Probability.LinearForm
import Zcash.Snark.ZeroKnowledge.IpaFold
import Zcash.Common.CPolynomial
import Mathlib.Data.Fin.Rev

/-!
# The power-of-two IPA mask from Common #225

<https://github.com/zakura-core/common/pull/225>, merged at
`b811257a0cedad053cedb6b3bf531107f8561b2a`, replaces a coefficient prefix by
the support `{0} ∪ {2^t | t < k}`. The pinned Ironwood description uses `k = 11`.

The polynomial below uses the repository's coefficient representation. The coefficient-vector
mask is folded using the same low/high update as the prover. Proving a scalar marginal does
not establish the joint IPA view, which includes commitments and the final aggregate blind `f`.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp)
open CompPoly

/-- The sparse polynomial is a random linear combination of powers of two vanishing at `q`. -/
def sparseIpaPolynomial {k : ℕ} (q : Fp) (alphas : Fin k → Fp) : CPoly :=
  ∑ t, CPolynomial.C (alphas t) *
    (CPolynomial.X ^ (2 ^ t.val) - CPolynomial.C (q ^ (2 ^ t.val)))

/-- The imposed root is an identity for every choice of coefficients. -/
theorem sparseIpaPolynomial_eval_root {k : ℕ} (q : Fp) (alphas : Fin k → Fp) :
    (sparseIpaPolynomial q alphas).eval q = 0 := by
  rw [CPolynomial.eval_toPoly]
  simp [sparseIpaPolynomial, CPolynomial.toPoly_sum, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_sub, CPolynomial.toPoly_pow, CPolynomial.C_toPoly, CPolynomial.X_toPoly,
    Polynomial.eval_finsetSum]

section ScalarResponse

variable {F : Type*} [Field F] {k : ℕ}

/-- The sparse mask as a coefficient vector, including its root-enforcing constant term. -/
def sparseIpaCoefficients (q : F) (alphas : Fin k → F) : Fin (2 ^ k) → F :=
  ∑ t, alphas t •
    (Pi.single (powerIndex t) 1 - q ^ (2 ^ t.val) • Pi.single 0 1)

/-- Weight of each mask coordinate in the closed final-scalar formula; `rev` gives `k-1-t`. -/
def ipaMaskWeights (q xi : F) (rounds : Fin k → F) : Fin k → F :=
  fun t => xi * ((rounds t.rev)⁻¹ - q ^ (2 ^ t.val))

/-- The sparse mask's stated contribution to the final IPA scalar. -/
def sparseIpaContribution (q xi : F) (rounds alphas : Fin k → F) : F :=
  xi * ∑ t, alphas t * ((rounds t.rev)⁻¹ - q ^ (2 ^ t.val))

/-- The contribution is a field-linear form in the independently sampled masks. -/
theorem sparseIpaContribution_eq_linearForm (q xi : F) (rounds alphas : Fin k → F) :
    sparseIpaContribution q xi rounds alphas = linearForm (ipaMaskWeights q xi rounds) alphas := by
  unfold sparseIpaContribution linearForm ipaMaskWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Derive the mask formula from the recursive low/high coefficient fold. -/
theorem coefficientFold_sparseIpaCoefficients (q : F) (rounds alphas : Fin k → F) :
    coefficientFold k rounds (sparseIpaCoefficients q alphas) =
      ∑ t, alphas t * ((rounds t.rev)⁻¹ - q ^ (2 ^ t.val)) := by
  change coefficientFoldLinear k rounds (sparseIpaCoefficients q alphas) = _
  simp only [sparseIpaCoefficients, map_sum, map_smul, map_sub]
  change (∑ t, alphas t *
    (coefficientFold k rounds (Pi.single (powerIndex t) 1) -
      q ^ (2 ^ t.val) * coefficientFold k rounds (Pi.single 0 1))) = _
  simp only [coefficientFold_powerIndex, coefficientFold_single_zero, mul_one]

/-- The coefficient-vector construction has the same imposed root as the polynomial formula. -/
theorem coefficientEvaluation_sparseIpaCoefficients (q : F) (alphas : Fin k → F) :
    coefficientEvaluation k q (sparseIpaCoefficients q alphas) = 0 := by
  let evaluationRounds : Fin k → F := fun j => (q ^ (2 ^ j.rev.val))⁻¹
  have heval : ∀ t : Fin k, (evaluationRounds t.rev)⁻¹ = q ^ (2 ^ t.val) := by
    intro t
    simp only [evaluationRounds, Fin.rev_rev, inv_inv]
  rw [← coefficientFold_eq_evaluation k evaluationRounds q _ heval,
    coefficientFold_sparseIpaCoefficients]
  simp [heval]

/-- The scalar emitted after the actual coefficient folds, for a claimed value `v = P(q)`. -/
def maskedIpaScalar (q xi v : F) (rounds : Fin k → F)
    (coefficients : Fin (2 ^ k) → F) (alphas : Fin k → F) : F :=
  foldByRounds k rounds
    (coefficients + xi • sparseIpaCoefficients q alphas - Pi.single 0 v)

/-- The final scalar is its unmasked offset plus the derived sparse-mask contribution. -/
theorem maskedIpaScalar_eq (q xi v : F) (rounds : Fin k → F)
    (coefficients : Fin (2 ^ k) → F) (alphas : Fin k → F) :
    maskedIpaScalar q xi v rounds coefficients alphas =
      coefficientFold k rounds coefficients - v + sparseIpaContribution q xi rounds alphas := by
  rw [maskedIpaScalar, foldByRounds_eq_coefficientFold]
  change coefficientFoldLinear k rounds
    (coefficients + xi • sparseIpaCoefficients q alphas - Pi.single 0 v) = _
  rw [map_sub, map_add, map_smul]
  change coefficientFold k rounds coefficients +
    xi * coefficientFold k rounds (sparseIpaCoefficients q alphas) -
      coefficientFold k rounds (Pi.single 0 v) = _
  rw [coefficientFold_sparseIpaCoefficients, coefficientFold_single_zero]
  unfold sparseIpaContribution
  ring

/-- The multiplier `xi` and one non-evaluation folding direction give rank one. -/
theorem ipaMaskWeights_ne_zero (q xi : F) (rounds : Fin k → F) (t : Fin k)
    (hxi : xi ≠ 0) (ht : (rounds t.rev)⁻¹ ≠ q ^ (2 ^ t.val)) :
    ipaMaskWeights q xi rounds t ≠ 0 :=
  mul_ne_zero hxi (sub_ne_zero.mpr ht)

/-- Exact uniformity of the ideal masked scalar under the explicit nonzero-rank conditions. -/
theorem sparseIpaScalar_uniform [Fintype F] (q xi offset : F) (rounds : Fin k → F)
    (hxi : xi ≠ 0) (t : Fin k) (ht : (rounds t.rev)⁻¹ ≠ q ^ (2 ^ t.val)) :
    (PMF.uniformOfFintype (Fin k → F)).map
        (fun alphas => offset + sparseIpaContribution q xi rounds alphas) =
      PMF.uniformOfFintype F := by
  simp_rw [sparseIpaContribution_eq_linearForm]
  exact affineLinearForm_uniform (ipaMaskWeights q xi rounds) t
    (ipaMaskWeights_ne_zero q xi rounds t hxi ht) offset

/-- When every direction agrees with evaluation, this mask contributes zero. -/
theorem sparseIpaContribution_eq_zero_of_evaluation (q xi : F) (rounds alphas : Fin k → F)
    (h : ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val)) :
    sparseIpaContribution q xi rounds alphas = 0 := by
  simp [sparseIpaContribution, h]

/-- In the evaluation case the complete scalar is zero, not merely the mask contribution. -/
theorem maskedIpaScalar_eq_zero_of_evaluation (q xi v : F) (rounds : Fin k → F)
    (coefficients : Fin (2 ^ k) → F) (alphas : Fin k → F)
    (hv : coefficientEvaluation k q coefficients = v)
    (h : ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val)) :
    maskedIpaScalar q xi v rounds coefficients alphas = 0 := by
  rw [maskedIpaScalar_eq, coefficientFold_eq_evaluation k rounds q coefficients h,
    sparseIpaContribution_eq_zero_of_evaluation q xi rounds alphas h, hv]
  ring

open Classical in
/-- The ideal scalar simulator only needs the public evaluation point and round challenges. -/
noncomputable def idealSparseIpaScalar [Fintype F] (q : F) (rounds : Fin k → F) : PMF F :=
  if ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val) then PMF.pure 0
  else PMF.uniformOfFintype F

/-- Common #225's uniform-or-publicly-zero dichotomy, for the complete folded scalar.

This proves exact equality of a scalar distribution under ideal uniform field masks and
fixed public challenges, with `xi ≠ 0`. It does not yet simulate the joint commitment/scalar
view or condition an actual execution on successful encodings and nonzero challenges. -/
theorem maskedIpaScalar_simulates [Fintype F] (q xi v : F) (rounds : Fin k → F)
    (coefficients : Fin (2 ^ k) → F) (hxi : xi ≠ 0)
    (hv : coefficientEvaluation k q coefficients = v) :
    (PMF.uniformOfFintype (Fin k → F)).map
        (maskedIpaScalar q xi v rounds coefficients) = idealSparseIpaScalar q rounds := by
  classical
  unfold idealSparseIpaScalar
  split_ifs with h
  · have hzero : maskedIpaScalar q xi v rounds coefficients = fun _ => 0 := by
      funext alphas
      exact maskedIpaScalar_eq_zero_of_evaluation q xi v rounds coefficients alphas hv h
    rw [hzero]
    exact PMF.map_const (PMF.uniformOfFintype (Fin k → F)) 0
  · push Not at h
    obtain ⟨t, ht⟩ := h
    have hform : maskedIpaScalar q xi v rounds coefficients = fun alphas =>
        coefficientFold k rounds coefficients - v + sparseIpaContribution q xi rounds alphas :=
      funext (maskedIpaScalar_eq q xi v rounds coefficients)
    rw [hform]
    exact sparseIpaScalar_uniform q xi (coefficientFold k rounds coefficients - v)
      rounds hxi t ht

end ScalarResponse

end Zcash.Snark.ZeroKnowledge
