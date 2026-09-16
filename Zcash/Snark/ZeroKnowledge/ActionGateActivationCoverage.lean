import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActionSourceGateTrace
import Zcash.Snark.ZeroKnowledge.GateIndexedCoverage
import Zcash.Meta.ActivationCoverage

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.activationCoverage true

/-- The gate coverage result is indexed by the original complete Action operations: every
configured gate has its original source entry at every active row.

Both of the check's list arguments are read from compact source traces, placed. The labels
come from `actionCircuit_gateLabels_eq_sourceTrace` and the activations from
`actionCircuit_selectorActivations_eq_sourceTrace`, so the opaque circuit is opened only
through its recorded implementation equation, never reduced through. -/
theorem actionCircuit_gateActivationCoverage :
    gateActivationCoverageCheck (actionCircuit.constraintSystem.gates.map sourceGateLabel)
      actionCircuit.selectorActivations
      (sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0) = true := by
  rw [actionCircuit_gateLabels_eq_sourceTrace, actionCircuit_selectorActivations_eq_sourceTrace,
    actionCircuit_regionStarts_eq_certificate, Internal.actionCircuit_eq_impl]
  rw [← gateActivationCoverageScan_eq, ← gateIndexedCoverageScan_original]
  check_activation_coverage

end Zcash.Snark.ZeroKnowledge
