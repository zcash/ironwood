import Zcash.Circuits.Halo2.FieldSupport
import Zcash.Arithmetic.PermutationDomain
import Zcash.Snark.Keygen.Pipeline

/-! # Pasta instances of circuit/field compatibility -/

namespace Halo2.TopLevelCircuit

open Zcash.Arithmetic Zcash.Snark.Keygen

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Numerical shape bounds establish the three field-compatibility conditions
for the canonical Pasta domain and permutation names. -/
theorem fieldSupport_of_pastaBounds
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (hDomain : top.domainExponent ≤ 32)
    (hDegree : top.constraintDegree < scalarFieldOrder)
    (hColumns : top.permutationColumnCount ≤ deltaFpOrder) :
    CircuitFieldSupport top top.omega deltaFp where
  omega_isPrimitiveRoot := by
    simpa only [omega, n] using omegaOf_isPrimitiveRoot top.domainExponent hDomain
  constraintDegree_lt_ringChar := by
    simpa only [ZMod.ringChar_zmod_n] using hDegree
  delta_ne_zero := by
    rw [deltaFp, powFast_eq_pow]
    exact pow_ne_zero _ (by decide : (5 : Fp) ≠ 0)
  eq_of_delta_pow_eq_omega_pow_mul := deltaFp_domainCosets hDomain hColumns

/-- A supported canonical Pasta domain cannot exceed the field's two-adicity. -/
theorem domainExponent_le
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    [CircuitFieldSupport top top.omega deltaFp] : top.domainExponent ≤ 32 := by
  by_contra hLarge
  have hLe : 32 ≤ top.domainExponent := by omega
  have hOmega : top.omega = omegaOf 32 := by
    simp only [omega, omegaOf, Nat.sub_eq_zero_of_le hLe, Nat.sub_self]
  have hRoot := CircuitFieldSupport.omega_isPrimitiveRoot
    (top := top) (omega := top.omega) (delta := deltaFp)
  rw [hOmega] at hRoot
  have hSize := hRoot.unique (omegaOf_isPrimitiveRoot 32 (by omega))
  rw [n] at hSize
  have : top.domainExponent = 32 := Nat.pow_right_injective (by decide : 2 ≤ 2) hSize
  omega

/-- The current Pasta bridge spells its supported exponents with a strict bound. -/
theorem domainExponent_lt
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    [CircuitFieldSupport top top.omega deltaFp] : top.domainExponent < 33 := by
  have := top.domainExponent_le
  omega

/-- Selector compression uses the same degree exposed by the circuit interface. -/
theorem csDegree_lt_scalarFieldOrder
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    [CircuitFieldSupport top top.omega deltaFp] :
    csDegree top.constraintSystem < scalarFieldOrder := by
  rw [top.constraintSystem_csDegree]
  simpa only [ZMod.ringChar_zmod_n] using
    (CircuitFieldSupport.constraintDegree_lt_ringChar
      (top := top) (omega := top.omega) (delta := deltaFp))

end Halo2.TopLevelCircuit
