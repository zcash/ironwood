import Clean.Halo2.TopLevel
import Zcash.Arithmetic.FieldDomainParams

/-!
# Field support for a compiled circuit

These are numerical compatibility conditions between a circuit and certified field
parameters, not additional circuit lawfulness.
-/

namespace Halo2

open Zcash.Arithmetic

/-- The circuit fits the evaluation domains, characteristic, and permutation cosets
provided by the field. All algebraic consequences follow from `FieldDomainParams`. -/
class CircuitFieldSupport
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    (params : FieldDomainParams F) : Prop where
  domainExponent_le : top.domainExponent ≤ params.twoAdicity
  constraintDegree_lt_ringChar : top.constraintDegree < ringChar F
  permutationColumnCount_le : top.permutationColumnCount ≤ params.oddPart

namespace CircuitFieldSupport

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    (params : FieldDomainParams F)

/-- The circuit's root is derived from its exponent and the field parameters. -/
def omega : F := params.omega top.domainExponent

variable [CircuitFieldSupport top params]

/-- Strict-bound form of the supported domain exponent. -/
theorem domainExponent_lt : top.domainExponent < params.twoAdicity + 1 :=
  Nat.lt_succ_of_le (domainExponent_le (top := top) (params := params))

/-- Numerical domain support gives the circuit root its exact order. -/
theorem omega_isPrimitiveRoot : IsPrimitiveRoot (omega top params) top.n := by
  simpa only [omega, TopLevelCircuit.n] using
    params.omega_isPrimitiveRoot (domainExponent_le (top := top) (params := params))

theorem omega_ne_zero : omega top params ≠ 0 :=
  (omega_isPrimitiveRoot top params).isUnit (by
    simp only [TopLevelCircuit.n]; positivity) |>.ne_zero

/-- Circuit columns occupy distinct cosets of the evaluation subgroup. -/
theorem eq_of_delta_pow_eq_omega_pow_mul
    (j j' : Fin top.permutationColumnCount) (row : ℕ)
    (h : params.delta ^ (j : ℕ) = omega top params ^ row * params.delta ^ (j' : ℕ)) :
    j = j' :=
  params.eq_of_delta_pow_eq_omega_pow_mul
    (domainExponent_le (top := top) (params := params))
    (permutationColumnCount_le (top := top) (params := params)) j j' row h

include params in
/-- Clean's constraint-system degree is the same bounded circuit degree. -/
theorem csDegree_lt_ringChar : csDegree top.constraintSystem < ringChar F := by
  rw [top.constraintSystem_csDegree]
  exact constraintDegree_lt_ringChar (top := top) (params := params)

end CircuitFieldSupport

end Halo2
