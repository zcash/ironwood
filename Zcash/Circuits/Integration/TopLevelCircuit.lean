import Clean.Halo2.TopLevel
import Zcash.Circuits.Integration.CircuitIntegration
import Zcash.Common.RelationWitness
import Zcash.Common.Satisfying

/-!
# Generic SNARK-to-top-level-circuit endpoint

`FullCircuitBridge` reconstructs Clean's authoritative operation constraints from the
separated gate, copy, lookup, and fixed arguments.  A fitting `TopLevelCircuit`
closes its own environment contract.  This module composes those two generic
boundaries; no Action-specific circuit, placement, or statement appears here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace FullCircuitSatisfaction

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- Exact full operation satisfaction implies the circuit-owned semantic statement. -/
theorem topLevelSoundness
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp)
    (hsatisfied :
      FullCircuitSatisfaction top.placement
        (top.environment assignment) top.operations 0) :
    top.Statement (top.extractPublicInput (top.environment assignment)) := by
  apply top.statement_soundness assignment
  exact FullCircuitSatisfaction.constraints hsatisfied

end FullCircuitSatisfaction

/-- Type-valued semantic evidence for a top-level circuit: the private witness as
executable data, together with its specification proof — `Zcash.Common.Satisfying`
at the circuit's own specification. Unlike `TopLevelCircuit.Statement`, nothing is
truncated. -/
abbrev TopLevelSemanticWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (publicInput : PublicInput Fp) : Type :=
  Zcash.Common.Satisfying top.Spec publicInput

namespace TopLevelSemanticWitness

/-- Forget the retained data and recover the ordinary existential statement. -/
theorem statement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {publicInput : PublicInput Fp}
    (witness : TopLevelSemanticWitness top publicInput) :
    top.Statement publicInput :=
  ⟨witness.w, witness.satisfied⟩

end TopLevelSemanticWitness

namespace FullCircuitBridge

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
Reconstructed full constraints imply the top-level circuit's own statement.
-/
theorem topLevelSoundness
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp)
    (bridge : FullCircuitBridge top.placement (top.environment assignment)
      top.operations 0) :
    top.Statement (top.extractPublicInput (top.environment assignment)) :=
  bridge.satisfaction.topLevelSoundness top assignment

end FullCircuitBridge

/-!
`TopLevelBridgeWitness` hides the exact environment and operation stream at the
dependent-type boundary. Their equalities to the circuit-derived values are
retained as properties, so downstream soundness composition never needs to
unfold circuit synthesis.
-/
variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

structure TopLevelBridgeWitness
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp) where
  environment : Environment Fp
  operations : Operations Fp
  environment_eq : environment = top.environment assignment
  operations_eq : top.operations = operations
  bridge : FullCircuitBridge top.placement environment
    operations 0

namespace TopLevelBridgeWitness

theorem statement
    {top : TopLevelCircuit Fp Config PublicInput}
    {assignment : ProofAssignment Fp}
    (witness : TopLevelBridgeWitness top assignment) :
    top.Statement (top.extractPublicInput (top.environment assignment)) :=
    FullCircuitSatisfaction.topLevelSoundness top assignment
      (by
        rw [witness.operations_eq]
        exact witness.environment_eq ▸ witness.bridge.satisfaction)

/-- Preserve the circuit's extracted private witness on the successful bridge branch. -/
def semanticWitness
    {top : TopLevelCircuit Fp Config PublicInput}
    {assignment : ProofAssignment Fp}
    (witness : TopLevelBridgeWitness top assignment) :
    TopLevelSemanticWitness top
      (top.extractPublicInput (top.environment assignment)) :=
    { w := top.extractPrivateWitness (top.placedEnvironment assignment)
      satisfied := top.soundness assignment
        (by
          rw [witness.operations_eq]
          exact FullCircuitSatisfaction.constraints
            (witness.environment_eq ▸ witness.bridge.satisfaction)) }

end TopLevelBridgeWitness

end Zcash.Snark
