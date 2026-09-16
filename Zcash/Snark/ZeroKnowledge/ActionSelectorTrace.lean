import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace
import Zcash.Snark.ZeroKnowledge.VariableBaseOverflowTrace
import Zcash.Snark.ZeroKnowledge.ActionConfiguration

/-!
# Connecting compact selector traces to Action

The compiler's activation list is exactly the placed compact trace.
`ActionSourceSelectorTrace` composes every Action region; the concrete packing
certificate remains a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action Zcash.Circuits.Trace

/-- The actual Action compiler consumes exactly the placed source selector trace. -/
theorem actionCircuit_selectorActivations_eq_trace :
    actionCircuit.selectorActivations =
      placeSelectorTrace actionCircuit.regionStarts (trace selectorOf actionCircuit.operations) :=
  activations_eq_placeSelectorTrace actionCircuit.regionStarts actionCircuit.operations 0

end Zcash.Snark.ZeroKnowledge
