import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupActivationTrace

/-!
# The complete Action source lookup trace

The lookup labels of the Action circuit are its activation trace projected to lookups, so the
tower of per-gadget lemmas that composes the activation trace serves here without a lookup
tower of its own. The final equality opens the opaque top-level circuit only through its
recorded implementation equation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action Zcash.Circuits.Trace

/-- All source regions of the specified post-NU6.3 Action circuit, projected to their lookup
labels: each lookup's master selector at its local row. -/
def actionSourceLookupTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  (actionSourceActivations Specs.Sinsemilla.orchardGenerators config).map fun body =>
    body.flatMap lookupOf

/-- The actual opaque Action circuit has precisely the source-derived compact lookup trace. Its
lookup labels are the activation trace projected, so this follows from the activation equation
and the generic projection rather than from a lookup tower of its own. -/
theorem actionCircuit_lookupTrace_eq :
    trace lookupOf actionCircuit.operations = actionSourceLookupTrace actionConfig := by
  rw [trace_eq_project _ lookupOf_vanishes, actionCircuit_activationTrace_eq]
  rfl

/-- The source labels the coverage check is stated over are exactly the placed compositional
trace. The coverage proof rests on this substitution: the statement it proves is over the
compiler's own labels, and only its derivation goes through the trace. Placement enters
definitionally, since a circuit's `placement` is `regionStarts.getD · 0`. -/
theorem actionCircuit_lookupLabels_eq_sourceTrace :
    sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0 =
      placeSelectorTrace actionCircuit.regionStarts (actionSourceLookupTrace actionConfig) 0 := by
  rw [← operationSourceLookupLabels_eq]
  rw [show actionCircuit.placement = fun region => actionCircuit.regionStarts.getD region 0
    from rfl]
  rw [operationSourceLookupLabels_eq_placeTrace, actionCircuit_lookupTrace_eq]

end Zcash.Snark.ZeroKnowledge
