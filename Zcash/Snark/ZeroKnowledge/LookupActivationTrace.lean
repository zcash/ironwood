import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace

/-!
# Placing compact lookup traces

A compact lookup trace, `trace lookupOf` of `Zcash/Circuits/Trace/Activations.lean`, keeps each
lookup argument's own master selector at its local row, so lookup membership is never inferred
from a selector index alone. A region with no lookups still occupies one slot. Placement reuses
`placeSelectorTrace`, since a compact lookup trace has the shape of a compact selector trace.
`operationSourceLookupLabels_eq_placeTrace` connects the placed trace to the direct label
projection over the operation stream, for any supplied placement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- The placed compact trace and the direct label projection agree on every operation
stream, so either may be used to state a circuit's lookup labels. -/
theorem operationSourceLookupLabels_eq_placeTrace (starts : List ℕ)
    (operations : Operations F) (initial : ℕ) :
    operationSourceLookupLabels (fun region => starts.getD region 0) operations initial =
      placeSelectorTrace starts (trace lookupOf operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationSourceLookupLabels, trace, List.filterMap_cons,
            placeSelectorTrace, List.zipIdx_cons, List.flatMap_cons]
          rw [ih]
          congr 1
          induction body with
          | nil => rfl
          | cons op rest2 ih2 =>
              cases op <;> simp_all [regionSourceLookupLabels, lookupOf]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
