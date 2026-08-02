import Zcash.Circuits.Action.SelectorCoherence
import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Circuits.Integration.TopLevelGates
import Mathlib.Util.AssertNoSorry

/-!
# Closed computations for Action configure coherence

This small module isolates the native computation certificates needed to lift the
Action configure proofs to the synthesis-closed top-level constraint system.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

/--
Closing the Action configure result under its own synthesis does not add gates or
change the selector allocation bound.
-/
theorem gateData_eq :
    actionCircuit.constraintSystem.gates =
        (Action.Circuit.configure Specs.Sinsemilla.orchardGenerators {}).2.gates ∧
      actionCircuit.selectorCount =
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).2.numSelectors := by
  native_decide

/--
Closing the Action configure result under its own synthesis does not add lookups.
-/
theorem lookupData_eq :
    actionCircuit.constraintSystem.lookups =
      (Action.Circuit.configure
        Specs.Sinsemilla.orchardGenerators {}).2.lookups := by
  native_decide

/-- The derived Action constraint-system degree is below the Pasta field order. -/
theorem selectorDegree :
    csDegree actionCircuit.constraintSystem < scalarFieldOrder := by
  native_decide

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 := by
  native_decide

assert_no_sorry gateData_eq
assert_no_sorry lookupData_eq
assert_no_sorry selectorDegree
assert_no_sorry domainExponent_lt

end ActionGateCoherence

end Zcash.Snark
