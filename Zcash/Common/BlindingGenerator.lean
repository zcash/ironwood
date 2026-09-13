import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The blinding-generator condition in a prime-order group

Scalar multiplication by a nonzero point is injective in every field module.
When the group and scalar field have the same finite cardinality, it is also
surjective. This supplies the bijection used by the statistical simulation from
the concrete group order and a nonidentity check on the blinding generator.
-/

namespace Zcash.Common

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Distinct scalars act differently on every nonzero group element. -/
theorem scalarBlinding_injective (point : G) (hpoint : point ≠ 0) :
    Function.Injective (fun scalar : F => scalar • point) := by
  intro left right heq
  change left • point = right • point at heq
  by_contra hne
  have hdiff : left - right ≠ 0 := sub_ne_zero.mpr hne
  have hzero : (left - right) • point = 0 := by
    rw [sub_smul, heq, sub_self]
  apply hpoint
  calc
    point = (left - right)⁻¹ • ((left - right) • point) := by
      rw [inv_smul_smul₀ hdiff]
    _ = 0 := by rw [hzero, smul_zero]

/-- Equal finite field and group cardinalities turn a nonzero blinding point into the required bijection. -/
theorem scalarBlinding_bijective [Fintype F] [Fintype G]
    (hcard : Fintype.card F = Fintype.card G) (point : G) (hpoint : point ≠ 0) :
    Function.Bijective (fun scalar : F => scalar • point) :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨scalarBlinding_injective point hpoint, hcard⟩

/-- For a group of the scalar field's order, the hiding condition is exactly nonidentity of the blinding point. -/
theorem scalarBlinding_bijective_iff [Fintype F] [Fintype G]
    (hcard : Fintype.card F = Fintype.card G) (point : G) :
    Function.Bijective (fun scalar : F => scalar • point) ↔ point ≠ 0 := by
  constructor
  · intro hbij hzero
    have heq : (0 : F) = 1 := hbij.1 (by simp [hzero])
    exact zero_ne_one heq
  · exact scalarBlinding_bijective hcard point

end Zcash.Common
