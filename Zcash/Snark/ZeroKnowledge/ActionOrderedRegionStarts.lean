import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes
import Zcash.Snark.ZeroKnowledge.ActionTracePlacement

/-!
# V1 placement of the ordered Action source shapes

The ordered shape table alone determines the actual Action compiler's region starts. This is
placement data: it does not depend on any activation trace, and the modules that consume it,
the advice certificates among them, should not depend on one either.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Zcash.Circuits.Action

/-- V1 placement of the exact certified source shapes. -/
def actionOrderedRegionStarts : List ℕ :=
  regionStartsFromSummary { regionShapes := actionOrderedRegionShapes }

/-- Expose the finite planner calculation only when explicitly requested. -/
theorem actionOrderedRegionStarts_def :
    actionOrderedRegionStarts = (V1.planCandidate (indexRegionSummaries 0 actionOrderedRegionShapes)).1 :=
  regionStartsFromSummary_def _

/-- The actual Action compiler uses exactly the placement of the certified ordered shapes. -/
theorem actionCircuit_regionStarts_eq_ordered :
    actionCircuit.regionStarts = actionOrderedRegionStarts := by
  rw [actionCircuit_regionStarts_eq_source, actionSourceRegionStarts_def, actionOrderedRegionShapes_eq_source]
  exact actionOrderedRegionStarts_def.symm

end Zcash.Snark.ZeroKnowledge
