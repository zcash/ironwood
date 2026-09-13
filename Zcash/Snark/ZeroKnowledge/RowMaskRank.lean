import Zcash.Snark.ZeroKnowledge.Domain
import Zcash.Common.Probability.LinearImage

/-!
# Joint evaluation rank of the replacement-row masks

At `d` distinct points, disjoint from the unmasked rows, `d` replacement rows suffice
to make the evaluation map surjective. The proof interpolates a polynomial that is zero
on every unmasked row and has any prescribed values at the observation points. Its
degree is below `n`, so the existing row interpolation recovers it exactly.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp)

/-- The observation points and unmasked domain rows form distinct interpolation nodes. -/
theorem rowMask_interpolationNodes_injective {n firstMasked d : ℕ}
    (omega : Fp) (points : Fin d → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    Function.Injective (Sum.elim (fun j : Fin firstMasked => omega ^ j.val) points) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have hi : i.val < n := lt_of_lt_of_le i.isLt (by omega)
      have hj : j.val < n := lt_of_lt_of_le j.isLt (by omega)
      have heq := hrows (a₁ := ⟨i.val, hi⟩) (a₂ := ⟨j.val, hj⟩) hab
      exact congrArg Sum.inl (Fin.ext (congrArg (fun x : Fin n => x.val) heq))
    | inr j => exact (haway j i hab.symm).elim
  | inr i =>
    cases b with
    | inl j => exact (haway i j hab).elim
    | inr j => exact congrArg Sum.inr (hpoints hab)

/-- Any joint observation vector is realized by some values of the replacement rows. -/
theorem rowMask_evaluations_surjective {n firstMasked d : ℕ}
    (omega : Fp) (points : Fin d → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    Function.Surjective (fun mask : RowMask n firstMasked => fun i : Fin d =>
      (maskedRowPolynomial firstMasked omega (fun _ => 0) mask).eval (points i)) := by
  intro values
  let nodes := Sum.elim (fun j : Fin firstMasked => omega ^ j.val) points
  let targets := Sum.elim (fun _ : Fin firstMasked => (0 : Fp)) values
  let poly := Lagrange.interpolate Finset.univ nodes targets
  have hnodes : Function.Injective nodes :=
    rowMask_interpolationNodes_injective omega points hrows hpoints haway hsize
  have hdegree : poly.degree < n := by
    have h := Lagrange.degree_interpolate_lt (s := Finset.univ) targets hnodes.injOn
    have hcount : (Finset.univ : Finset (Fin firstMasked ⊕ Fin d)).card = firstMasked + d := by
      simp
    rw [hcount] at h
    exact lt_of_lt_of_le h (by exact_mod_cast hsize)
  let mask : RowMask n firstMasked := fun row => poly.eval (omega ^ row.val.val)
  have hrow (i : Fin n) :
      poly.eval (omega ^ i.val) = maskedRows firstMasked (fun _ : Fin n => 0) mask i := by
    by_cases hi : firstMasked ≤ i.val
    · simp [maskedRows, hi, mask]
    · have hib : i.val < firstMasked := Nat.lt_of_not_ge hi
      have h := Lagrange.eval_interpolate_at_node targets hnodes.injOn
        (Finset.mem_univ (Sum.inl (⟨i.val, hib⟩ : Fin firstMasked)))
      simpa [poly, nodes, targets, maskedRows, hi] using h
  have heq : (maskedRowPolynomial firstMasked omega (fun _ : Fin n => 0) mask).toPoly =
      poly := by
    rw [maskedRowPolynomial, toPoly_rowPolynomial]
    symm
    apply Lagrange.eq_interpolate_of_eval_eq _ hrows.injOn
    · simpa using hdegree
    · intro i _
      exact hrow i
  refine ⟨mask, ?_⟩
  funext i
  change (maskedRowPolynomial firstMasked omega (fun _ : Fin n => 0) mask).eval (points i) = _
  rw [CompPoly.CPolynomial.eval_toPoly, heq]
  exact Lagrange.eval_interpolate_at_node targets hnodes.injOn
    (Finset.mem_univ (Sum.inr i))

/-- The replacement-row embedding, with all unmasked rows set to zero. -/
def maskRowsLinearMap (n firstMasked : ℕ) : RowMask n firstMasked →ₗ[Fp] (Fin n → Fp) where
  toFun := maskedRows firstMasked (fun _ => 0)
  map_add' := by
    intro a b
    funext i
    by_cases hi : firstMasked ≤ i.val <;> simp [maskedRows, hi]
  map_smul' := by
    intro c a
    funext i
    by_cases hi : firstMasked ≤ i.val <;> simp [maskedRows, hi]

/-- The ordinary linear evaluation map for the existing row interpolation. -/
noncomputable def rowEvaluationLinearMap {n d : ℕ} (omega : Fp) (points : Fin d → Fp) :
    (Fin n → Fp) →ₗ[Fp] (Fin d → Fp) where
  toFun values := fun i =>
    (Lagrange.interpolate Finset.univ (fun j : Fin n => omega ^ j.val) values).eval (points i)
  map_add' := by intro a b; funext i; simp only [map_add, Polynomial.eval_add, Pi.add_apply]
  map_smul' := by
    intro c a
    funext i
    simp only [map_smul, Polynomial.eval_smul, Pi.smul_apply, RingHom.id_apply]

/-- The linear map computes precisely the evaluations of the computable row polynomial. -/
theorem rowEvaluationLinearMap_apply {n d : ℕ} (omega : Fp) (points : Fin d → Fp)
    (values : Fin n → Fp) (i : Fin d) :
    rowEvaluationLinearMap omega points values i = (rowPolynomial omega values).eval (points i) := by
  rw [CompPoly.CPolynomial.eval_toPoly, toPoly_rowPolynomial]
  rfl

/-- The part of the joint evaluation vector contributed by the replacement rows. -/
noncomputable def maskEvaluationLinearMap {n firstMasked d : ℕ} (omega : Fp)
    (points : Fin d → Fp) : RowMask n firstMasked →ₗ[Fp] (Fin d → Fp) :=
  (rowEvaluationLinearMap omega points).comp (maskRowsLinearMap n firstMasked)

/-- Splitting a masked row vector into its fixed prefix and random suffix is exact. -/
theorem maskedRows_decompose {n firstMasked : ℕ} (witness : Fin n → Fp)
    (mask : RowMask n firstMasked) :
    maskedRows firstMasked witness mask =
      maskedRows firstMasked witness 0 + maskRowsLinearMap n firstMasked mask := by
  funext i
  by_cases hi : firstMasked ≤ i.val <;> simp [maskedRows, maskRowsLinearMap, hi]

/-- Ideal replacement rows jointly hide every evaluation in the stated observation family.

The rank and point-separation premises are derived from interpolation. No independence of
the separate evaluation marginals is assumed. Challenges are supplied here. -/
theorem maskedRowPolynomial_joint_uniform {n firstMasked d : ℕ}
    (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    (PMF.uniformOfFintype (RowMask n firstMasked)).map (fun mask => fun i : Fin d =>
        (maskedRowPolynomial firstMasked omega witness mask).eval (points i)) =
      PMF.uniformOfFintype (Fin d → Fp) := by
  have hsurj : Function.Surjective
      (maskEvaluationLinearMap (n := n) (firstMasked := firstMasked) omega points) := by
    have heq : (maskEvaluationLinearMap (n := n) (firstMasked := firstMasked) omega points :
        RowMask n firstMasked → (Fin d → Fp)) = fun mask => fun i =>
          (maskedRowPolynomial firstMasked omega (fun _ => 0) mask).eval (points i) := by
      funext mask i
      exact rowEvaluationLinearMap_apply omega points _ i
    rw [heq]
    exact rowMask_evaluations_surjective omega points hrows hpoints haway hsize
  have heq : (fun mask : RowMask n firstMasked => fun i : Fin d =>
      (maskedRowPolynomial firstMasked omega witness mask).eval (points i)) =
        fun mask => rowEvaluationLinearMap omega points (maskedRows firstMasked witness 0) +
          maskEvaluationLinearMap omega points mask := by
    funext mask i
    rw [maskedRowPolynomial, ← rowEvaluationLinearMap_apply, maskedRows_decompose, map_add]
    rfl
  rw [heq]
  exact surjectiveAffineMap_uniform (maskEvaluationLinearMap omega points).toAddMonoidHom
    hsurj (rowEvaluationLinearMap omega points (maskedRows firstMasked witness 0))

end Zcash.Snark.ZeroKnowledge
