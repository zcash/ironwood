import Clean.Halo2.Formal.Call
import Clean.Halo2.FormalRegion.Call
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Zcash.Circuits.Trace.Activations

/-!
# Placing compact selector traces

A compact selector trace, `trace selectorOf` of `Zcash/Circuits/Trace/Activations.lean`, keeps
every selector activation, its local row, and its region's position in the synthesis stream.
Empty regions remain in it because they still advance the floor planner's region index.
Placement is `placeLabels` of that module, and `activations_eq_placeLabels` connects the placed
trace to the compiler's actual activation walk, for any supplied placement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- Compact trace placement is exactly the compiler's activation walk, including
region-index advancement through empty traces and ignored non-region operations. -/
theorem activations_eq_placeLabels (starts : List ℕ) (operations : Operations F) (initial : ℕ) :
    activations starts (indexedRegions operations initial).1 =
      placeLabels starts (trace selectorOf operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, activations, List.flatMap_cons,
            trace, List.filterMap_cons, placeLabels, List.zipIdx_cons,
            List.map_flatMap] at ih ⊢
          rw [ih]
          congr 1
          apply List.flatMap_congr
          intro operation hoperation
          cases operation <;> simp [selectorOf]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
