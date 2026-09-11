import Clean.Halo2.TopLevel

/-! # Witness extraction from a circuit assignment -/

namespace Halo2.TopLevelCircuit

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)

/-- Extract the witness used by the circuit specification. No secrecy is assumed. -/
def extractWitness (assignment : ProofAssignment F) : top.PrivateWitness :=
  top.extractPrivate top.config (top.placedEnvironment assignment)

/-- Source constraints establish the specification for the extracted witness. -/
theorem spec_of_constraints (assignment : ProofAssignment F)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0) :
    top.Spec (top.extractPublicInput (top.environment assignment))
      (top.extractWitness assignment) :=
  top.soundness assignment hconstraints

end Halo2.TopLevelCircuit
