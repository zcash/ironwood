import Zcash.Snark.ZeroKnowledge.GateActivationCoverage
import Zcash.Circuits.Trace.Activations

/-!
# Placing compact gate traces

A compact gate trace, `trace gateOf` of `Zcash/Circuits/Trace/Activations.lean`, keeps each gate's
selector index and name at its local row. A region with no gates still occupies one slot.
Placement is `placeLabels`, which adds a region's start to the row of a label of any payload.
`sourceGateActivationLabels_eq_placeTrace` connects the placed trace to the coverage check's own
label list over the operation stream, for any supplied placement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- The coverage check's label triple, read from a payload-and-row label: the selector index, the
gate name, and the placed row. -/
def flatGateLabel (label : (ℕ × String) × ℕ) : ℕ × String × ℕ :=
  (label.1.1, label.1.2, label.2)

/-- The placed compact trace and the coverage check's own label list agree on every operation
stream, so either may be used to state a circuit's gate labels. -/
theorem sourceGateActivationLabels_eq_placeTrace (starts : List ℕ) (operations : Operations F)
    (initial : ℕ) :
    sourceGateActivationLabels (fun region => starts.getD region 0) operations initial =
      (placeLabels starts (trace gateOf operations) initial).map flatGateLabel := by
  unfold sourceGateActivationLabels
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationEnabledGates, List.map_append, trace, List.filterMap_cons,
            placeLabels, List.zipIdx_cons, List.flatMap_cons]
          rw [ih]
          congr 1
          induction body with
          | nil => rfl
          | cons op rest2 ih2 =>
              cases op <;> simp_all [regionEnabledGates, gateOf, flatGateLabel]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
