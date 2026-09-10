import Zcash.Snark.Verifier.Key
import Zcash.Arithmetic.FieldDomainParams

/-! # Field support for verifying keys

These laws connect a key to the field's chosen domain convention. They concern
neither its commitments nor a particular URS. All root and coset properties are
consequences of the certified field parameters, not independent assumptions.
-/

namespace Zcash.Snark.VerifyingKey

open Zcash.Arithmetic

variable {shape : CircuitShape} {F G : Type*} [Field F]
    [params : FieldDomainParams F]

/-- The key uses a supported domain and permutation separator from the chosen
field parameters, with enough distinct cosets for its columns. -/
class FieldSupport (vk : VerifyingKey shape F G) : Prop where
  n_eq : vk.n = 2 ^ shape.k
  omega_eq : vk.omega = FieldDomainParams.omega shape.k
  delta_eq : vk.delta = FieldDomainParams.delta
  domainExponent_le : shape.k ≤ params.twoAdicity
  permutationColumnCount_le : shape.numPermutationColumns ≤ params.oddPart

/-- Proof invocation parameters do not change a key's field support. -/
instance fieldSupportWithProofParams (vk : VerifyingKey shape F G) [FieldSupport vk]
    (pp : ProofParams) : FieldSupport (shape := shape.withProofParams pp) vk := by
  simpa only [Halo2.CircuitShape.withProofParams_toCircuitShape] using
    (inferInstance : FieldSupport vk)

variable (vk : VerifyingKey shape F G) [FieldSupport vk]

theorem n_pos : 0 < vk.n := by
  rw [FieldSupport.n_eq (vk := vk)]
  positivity

/-- A supported key's root has exactly the order of its evaluation domain. -/
theorem omega_isPrimitiveRoot : IsPrimitiveRoot vk.omega vk.n := by
  rw [FieldSupport.n_eq (vk := vk), FieldSupport.omega_eq (vk := vk)]
  exact FieldDomainParams.omega_isPrimitiveRoot
    (FieldSupport.domainExponent_le (vk := vk))

theorem omega_pow_n : vk.omega ^ vk.n = 1 :=
  vk.omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_zero : vk.omega ≠ 0 :=
  (vk.omega_isPrimitiveRoot.isUnit vk.n_pos.ne').ne_zero

/-- Different domain rows have different evaluation points. -/
theorem domainRowsInjective :
    Function.Injective (fun row : Fin vk.n => vk.omega ^ (row : ℕ)) := by
  intro i j h
  exact Fin.ext (vk.omega_isPrimitiveRoot.pow_inj i.isLt j.isLt h)

theorem n_cast_ne_zero : (vk.n : F) ≠ 0 := by
  letI : NeZero vk.n := ⟨vk.n_pos.ne'⟩
  exact vk.omega_isPrimitiveRoot.neZero'.out

theorem delta_ne_zero : vk.delta ≠ 0 := by
  rw [FieldSupport.delta_eq (vk := vk)]
  exact FieldDomainParams.delta_ne_zero

/-- Supported column names occupy distinct cosets of the row subgroup. -/
theorem eq_of_delta_pow_eq_omega_pow_mul
    (j j' : Fin shape.numPermutationColumns) (row : ℕ)
    (h : vk.delta ^ (j : ℕ) = vk.omega ^ row * vk.delta ^ (j' : ℕ)) : j = j' := by
  rw [FieldSupport.delta_eq (vk := vk), FieldSupport.omega_eq (vk := vk)] at h
  exact FieldDomainParams.eq_of_delta_pow_eq_omega_pow_mul
    (FieldSupport.domainExponent_le (vk := vk))
    (FieldSupport.permutationColumnCount_le (vk := vk)) j j' row h

end Zcash.Snark.VerifyingKey
