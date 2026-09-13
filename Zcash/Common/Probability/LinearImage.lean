import Zcash.Common.UniformMeasure
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Uniformity of a surjective linear observation

A homomorphism has equally sized fibers: each fiber is a translate of its kernel.
The explicit fiber equivalence proves joint uniformity when a masking map is surjective,
rather than inferring it from the uniformity of individual coordinates.
-/

namespace Zcash.Common.Probability

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private noncomputable def addMapFiberEquiv (f : A →+ B) (hf : Function.Surjective f) :
    A ≃ (B × {a : A // f a = 0}) where
  toFun a := (f a, ⟨a - (hf (f a)).choose, by
    rw [map_sub, (hf (f a)).choose_spec, sub_self]⟩)
  invFun pair := pair.2.val + (hf pair.1).choose
  left_inv := by
    intro a
    exact sub_add_cancel _ _
  right_inv := by
    rintro ⟨b, a, ha⟩
    have hsum : f (a + (hf b).choose) = b := by
      rw [map_add, ha, (hf b).choose_spec, zero_add]
    apply Prod.ext
    · exact hsum
    · apply Subtype.ext
      change a + (hf b).choose - (hf (f (a + (hf b).choose))).choose = a
      rw [hsum, add_sub_cancel_right]

/-- A surjective additive map sends a uniform finite input to a uniform joint output. -/
theorem surjectiveAddMap_uniform [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype B := by
  classical
  letI : Nonempty {a : A // f a = 0} := ⟨⟨0, map_zero f⟩⟩
  have hfactor : (f : A → B) = Prod.fst ∘ addMapFiberEquiv f hf := rfl
  rw [hfactor, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    Zcash.map_fst_uniformOfFintype]

/-- Adding a witness-dependent offset preserves uniformity of the whole output vector. -/
theorem surjectiveAffineMap_uniform [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) (offset : B) :
    (PMF.uniformOfFintype A).map (fun a => offset + f a) = PMF.uniformOfFintype B := by
  change (PMF.uniformOfFintype A).map ((fun b => offset + b) ∘ f) = _
  rw [← PMF.map_comp, surjectiveAddMap_uniform f hf]
  exact Zcash.map_uniformOfFintype_equiv (Equiv.addLeft offset)

end Zcash.Common.Probability
