import Clean.Halo2.TopLevel

/-! # Witness extraction from a circuit assignment -/

namespace Halo2.TopLevelCircuit

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)

/-- Extract the witness used by the circuit specification. No secrecy is assumed. -/
def extractWitness (assignment : ProofAssignment F) : top.PrivateWitness :=
  top.extractPrivate top.config (top.placedEnvironment assignment)

end Halo2.TopLevelCircuit
