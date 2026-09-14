import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace

/-!
# Compact lookup-activation traces

The lookup counterpart of `SelectorActivationTrace`. A region's lookup activations
are recorded before floor-planner placement, so a circuit's lookup labels follow
from its synthesis stages one at a time, each stage's trace proved separately.

The trace keeps each lookup argument's own master selector rather than the selectors
the activation enables, so lookup membership is never inferred from a selector index
alone. Placement reuses `placeSelectorTrace`: a compact lookup trace has the same
shape as a compact selector trace.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

variable {F : Type}

/-- A region's ordered lookup-master activations, before floor-planner placement. -/
def regionLookupTrace (body : RegionOperations F) : List (ℕ × ℕ) :=
  body.flatMap fun operation => match operation with
    | .enableLookup argument _ row => [(argument.masterSelector.index, row)]
    | _ => []

/-- The ordered region lookup traces; a region with no lookups still occupies one slot. -/
def lookupTrace (operations : Operations F) : List (List (ℕ × ℕ)) :=
  operations.filterMap fun operation => match operation with
    | .region _ body => some (regionLookupTrace body)
    | _ => none

/-- The placed compact trace and the direct label projection agree on every operation
stream, so either may be used to state a circuit's lookup labels. -/
theorem operationSourceLookupLabels_eq_placeTrace (starts : List ℕ)
    (operations : Operations F) (initial : ℕ) :
    operationSourceLookupLabels (fun region => starts.getD region 0) operations initial =
      placeSelectorTrace starts (lookupTrace operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationSourceLookupLabels, lookupTrace, List.filterMap_cons,
            placeSelectorTrace, List.zipIdx_cons, List.flatMap_cons]
          rw [ih]
          congr 1
          induction body with
          | nil => rfl
          | cons op rest2 ih2 =>
              cases op <;> simp_all [regionSourceLookupLabels, regionLookupTrace]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
