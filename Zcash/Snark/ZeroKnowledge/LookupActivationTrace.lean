import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace

/-!
# Placing compact lookup traces

A compact lookup trace, `trace lookupOf` of `Zcash/Circuits/Trace/Activations.lean`, keeps each
lookup argument's own master selector at its local row, so lookup membership is never inferred
from a selector index alone. A region with no lookups still occupies one slot. Placement is
`placeLabels`, which is generic in the label payload.
`sourceLookupActivationLabels_eq_placeTrace` connects the placed trace to the coverage check's
own label list over the operation stream, for any supplied placement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- The placed compact trace and the coverage check's own label list agree on every operation
stream, so either may be used to state a circuit's lookup labels. -/
theorem sourceLookupActivationLabels_eq_placeTrace (starts : List ℕ)
    (operations : Operations F) (initial : ℕ) :
    sourceLookupActivationLabels (fun region => starts.getD region 0) operations initial =
      placeLabels starts (trace lookupOf operations) initial := by
  unfold sourceLookupActivationLabels
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationEnabledLookups, List.map_append, trace, List.filterMap_cons,
            placeLabels, List.zipIdx_cons, List.flatMap_cons]
          rw [ih]
          congr 1
          induction body with
          | nil => rfl
          | cons op rest2 ih2 =>
              cases op <;> simp_all [regionEnabledLookups, lookupOf]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
