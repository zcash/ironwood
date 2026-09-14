import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActionSourceLookupTrace
import Zcash.Snark.ZeroKnowledge.ActivationCoverageScan
import Zcash.Meta.ActivationCoverage

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.activationCoverage true

/-- The lookup coverage result is indexed by the original complete Action operations: every
configured lookup has its original source entry at every active master row.

Both of the check's list arguments are read from compact source traces, placed. The labels
come from `actionCircuit_lookupLabels_eq_sourceTrace` and the activations from
`actionCircuit_selectorActivations_eq_sourceTrace`, so the opaque circuit is opened only
through its recorded implementation equation, never reduced through. -/
theorem actionCircuit_lookupActivationCoverage :
    lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations
      (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) = true := by
  rw [actionCircuit_lookupLabels_eq_sourceTrace, actionCircuit_selectorActivations_eq_sourceTrace,
    actionCircuit_regionStarts_eq_certificate, Internal.actionCircuit_eq_impl]
  rw [← lookupActivationCoverageScan_eq]
  check_activation_coverage

end Zcash.Snark.ZeroKnowledge
