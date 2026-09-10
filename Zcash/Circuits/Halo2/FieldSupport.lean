import Clean.Halo2.TopLevel
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Field support for a compiled circuit

These are compatibility conditions between a circuit's finite shape and its chosen
evaluation root and permutation-column scalar, not additional circuit lawfulness.
-/

namespace Halo2

/-- The evaluation domain, selector roots, and permutation column names fit the
chosen field. Instances can establish these conditions from numerical shape bounds. -/
class CircuitFieldSupport
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    (omega delta : F) : Prop where
  omega_isPrimitiveRoot : IsPrimitiveRoot omega top.n
  constraintDegree_lt_ringChar : top.constraintDegree < ringChar F
  delta_ne_zero : delta ≠ 0
  eq_of_delta_pow_eq_omega_pow_mul :
    ∀ (j j' : Fin top.permutationColumnCount) (row : ℕ),
      delta ^ (j : ℕ) = omega ^ row * delta ^ (j' : ℕ) → j = j'

end Halo2
