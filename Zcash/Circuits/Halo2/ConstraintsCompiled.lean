import Zcash.Circuits.Halo2.CompiledGates
import Zcash.Circuits.Halo2.CompiledCopies
import Zcash.Circuits.Halo2.CompiledLookups
import Zcash.Circuits.Halo2.Witness

/-! # Semantic soundness of the Halo2 compiler

The public boundary consists of compiled gate evaluations, resolved copy equality,
and tuple membership at compiled lookup activations. Selector compression, query
indexing, placement, and constant allocation are discharged internally. Fixed
assignments are already true in the circuit-owned environment.
-/

namespace Halo2.TopLevelCircuit

open Zcash Zcash.Snark

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

/-- Row-level satisfaction of the circuit's compiled constraints. -/
structure ConstraintsCompiled (assignment : ProofAssignment Fp) : Prop where
  gates : top.GatesCompiled assignment
  copies : top.CopiesCompiled assignment
  lookups : top.LookupsCompiled assignment

/-- Compiler semantics imply source constraints, including circuit-owned fixed data. -/
theorem constraints_of_compiled [CircuitFieldSupport top]
    (assignment : ProofAssignment Fp) (h : top.ConstraintsCompiled assignment) :
    Constraints top.placement (top.environment assignment) top.operations 0 := by
  rw [CircuitConstraintFamily.operations_constraints_iff]
  exact ⟨top.gate_constraints_of_compiled assignment h.gates,
    top.copy_constraints_of_compiled assignment h.copies,
    top.lookup_constraints_of_compiled assignment h.lookups,
    top.fixed_constraints assignment⟩

/-- Compiled satisfaction proves the circuit specification for its extracted witness
and public input, without exposing source operations or compiler transformations. -/
theorem soundness_compiled [CircuitFieldSupport top]
    (assignment : ProofAssignment Fp) (h : top.ConstraintsCompiled assignment) :
    top.Spec (top.extractPublicInput (top.environment assignment))
      (top.extractWitness assignment) :=
  top.soundness assignment (top.constraints_of_compiled assignment h)

end Halo2.TopLevelCircuit
