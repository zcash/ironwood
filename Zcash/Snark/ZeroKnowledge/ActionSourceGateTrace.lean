import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.GateActivationTrace

/-!
# The complete Action source gate trace

The gate labels of the Action circuit are its activation trace projected to gates, so the tower
of per-gadget lemmas that composes the activation trace serves here without a gate tower of its
own. The final equality opens the opaque top-level circuit only through its recorded
implementation equation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action Zcash.Circuits.Trace

/-- All source regions of the specified post-NU6.3 Action circuit, projected to their gate
labels: each gate's selector index and name at its local row. -/
def actionSourceGateTrace (config : Circuit.Config) : List (List ((ℕ × String) × ℕ)) :=
  (actionSourceActivations Specs.Sinsemilla.orchardGenerators config).map fun body =>
    body.flatMap gateOf

/-- The actual opaque Action circuit has precisely the source-derived compact gate trace. Its gate
labels are the activation trace projected, so this follows from the activation equation and the
generic projection rather than from a gate tower of its own. -/
theorem actionCircuit_gateTrace_eq :
    trace gateOf actionCircuit.operations = actionSourceGateTrace actionConfig := by
  rw [trace_eq_project _ gateOf_vanishes, actionCircuit_activationTrace_eq]
  rfl

/-- The source labels the coverage check is stated over are exactly the placed compositional
trace. The coverage proof rests on this substitution: the statement it proves is over the
compiler's own labels, and only its derivation goes through the trace. Placement enters
definitionally, since a circuit's `placement` is `regionStarts.getD · 0`. -/
theorem actionCircuit_gateLabels_eq_sourceTrace :
    sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0 =
      (placeLabels actionCircuit.regionStarts (actionSourceGateTrace actionConfig) 0).map
        flatGateLabel := by
  rw [show actionCircuit.placement = fun region => actionCircuit.regionStarts.getD region 0
    from rfl]
  rw [sourceGateActivationLabels_eq_placeTrace, actionCircuit_gateTrace_eq]

end Zcash.Snark.ZeroKnowledge
