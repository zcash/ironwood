import Zcash.Circuits.Action.Shape
import Zcash.Circuits.Integration.TopLevelGates

/-!
# Action polynomial bounds

This module supplies the two Action-specific numerical facts in the generic
constraint-bound boundary. Selector allocation follows for every top-level circuit
from its intrinsic configure and gate lawfulness guarantees.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Keygen
open Zcash.Circuits.Action (actionCircuit)

namespace ActionConstraintBounds

/-- The derived Action constraint-system degree is below the Pasta field order. -/
theorem selectorDegree :
    csDegree actionCircuit.constraintSystem < scalarFieldOrder := by
  rw [actionCircuit.constraintSystem_csDegree,
    Zcash.Circuits.Action.actionCircuit_constraintDegree_eq]
  norm_num [scalarFieldOrder]

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 := by
  simp only [TopLevelCircuit.domainExponent,
    Zcash.Circuits.Action.actionCircuit_shape_eq,
    Zcash.Circuits.Action.actionShape]
  norm_num

/-- The deployed Orchard Action circuit satisfies the polynomial bridge's numerical
bounds. -/
theorem constraintBounds :
    TopLevelConstraintBounds actionCircuit where
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

end ActionConstraintBounds

end Zcash.Snark
