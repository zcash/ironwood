import Zcash.Snark.ZeroKnowledge.VariableBaseSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace

/-!
# Complete variable-base multiplication selector trace

This joins the main region to the three overflow-check regions, keeping the empty
scalar-loading region and the running-sum lookup activations in their source order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The scalar-overflow gate retains its configured activation, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem overflowGate_regionActivations (K : ℕ) (config : Ecc.MulOverflow.Config K)
    (input : Var Ecc.MulOverflow.Inputs Fp) (scalar low : AssignedCell Fp) (region : RegionIndex) :
    regionActivations ((Ecc.MulOverflow.gateRegion K config input scalar low).operations region) =
      [.enableGate (Ecc.MulOverflow.overflowGate K config) 1] := rfl

/-- Scalar-overflow checks retain their complete region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem overflow_activationTrace (K : ℕ) (hKW : K * Ecc.MulOverflow.numWords K = 130)
    (config : Ecc.MulOverflow.Config K) (input : Var Ecc.MulOverflow.Inputs Fp) (region : RegionIndex) :
    activationTrace (((Ecc.MulOverflow.circuit K hKW).call config input).operations region) =
      [[], runningActivations config.lookupConfig 0 (Ecc.MulOverflow.numWords K),
        [.enableGate (Ecc.MulOverflow.overflowGate K config) 1]] := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Ecc.MulOverflow.synthesize K config input).operations region) = _
  simp only [Ecc.MulOverflow.synthesize, activation_trace_norm, List.cons_append]

/-- All four regions of the actual variable-base multiplication gadget. -/
def variableBaseActivations (config : Ecc.Mul.Config) : List (List (RegionOperation Fp)) :=
  [variableBaseMainActivations config, [],
    runningActivations config.overflowConfig.lookupConfig 0 13,
    [.enableGate (Ecc.MulOverflow.overflowGate 10 config.overflowConfig) 1]]

/-- Variable-base multiplication retains its main and overflow region traces, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem variableBase_activationTrace (config : Ecc.Mul.Config)
    (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    activationTrace ((Ecc.Mul.mul.call config input).operations region) =
      variableBaseActivations config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Ecc.Mul.synthesize config input).operations region) = _
  simp only [Ecc.Mul.synthesize, activation_trace_norm, variableBaseActivations,
    Ecc.MulOverflow.numWords, List.cons_append]

end Zcash.Snark.ZeroKnowledge
