import Zcash.Common.UniformMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Sampling an affine scalar from independent uniform masks

A nonzero coefficient is enough to make an affine form of independent uniform field
elements uniform. The proof replaces that coordinate by the affine output through an
explicit bijection. This exposes the rank premise used by the sparse IPA mask.
-/

namespace Zcash.Common.Probability

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- The field-linear observation of a vector of masks. -/
def linearForm (weights values : I → F) : F := ∑ i, weights i * values i

private def linearRest (weights : I → F) (j : I) (values : I → F) : F :=
  ∑ i ∈ Finset.univ.erase j, weights i * values i

/-- A linear form separates one chosen coordinate from the rest, exposing the coordinate used to
couple masks. -/
private theorem linearForm_split (weights values : I → F) (j : I) :
    linearForm weights values = linearRest weights j values + weights j * values j := by
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm

/-- Changing the chosen coordinate leaves the remaining linear form unchanged, enabling the
mask-coupling update. -/
private theorem linearRest_update (weights values : I → F) (j : I) (value : F) :
    linearRest weights j (Function.update values j value) = linearRest weights j values := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- Replace coordinate `j` by an affine form whose coefficient at `j` is nonzero. -/
def linearCoordinateEquiv (weights : I → F) (j : I) (hj : weights j ≠ 0)
    (offset : F) : (I → F) ≃ (I → F) where
  toFun := fun values => Function.update values j (offset + linearForm weights values)
  invFun := fun values => Function.update values j
    ((values j - offset - linearRest weights j values) / weights j)
  left_inv := by
    intro values
    funext i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, linearRest_update, linearForm_split weights values j]
      field_simp [hj]
      ring
    · simp only [Function.update_of_ne hi]
  right_inv := by
    intro values
    funext i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, linearForm_split weights _ j, linearRest_update]
      field_simp [hj]
      ring
    · simp only [Function.update_of_ne hi]

/-- Jointly uniform mask coordinates induce a uniform affine observation at nonzero rank. -/
theorem affineLinearForm_uniform [Fintype F] (weights : I → F) (j : I)
    (hj : weights j ≠ 0) (offset : F) :
    (PMF.uniformOfFintype (I → F)).map (fun values => offset + linearForm weights values) =
      PMF.uniformOfFintype F := by
  have hmap : (fun values => offset + linearForm weights values) =
      (fun values : I → F => values j) ∘ linearCoordinateEquiv weights j hj offset := by
    funext values
    simp only [Function.comp_apply, linearCoordinateEquiv, Equiv.coe_fn_mk,
      Function.update_self]
  rw [hmap, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    Zcash.map_eval_uniformOfFintype]

end Zcash.Common.Probability
