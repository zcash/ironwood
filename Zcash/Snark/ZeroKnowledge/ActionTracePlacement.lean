import Zcash.Snark.ZeroKnowledge.SelectorTracePlacement
import Zcash.Circuits.Action.Planner

/-!
# Action activation placement from the reduced source data

The exact V1 input order comes from the Action bundle's compositional summary, and
it is the actual opaque circuit's placement. No numerical packing certificate is
assumed or established by this refinement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Zcash.Circuits.Action

/-- V1 placement of the source-derived Action region shapes, in synthesis order. -/
def actionSourceRegionStarts : List ℕ :=
  regionStartsFromSummary (Circuit.mainPostSynthesisSummary actionConfig)

/-- The controlled computation equation for the concrete source-summary placement. -/
theorem actionSourceRegionStarts_def :
    actionSourceRegionStarts = (V1.planCandidate (indexRegionSummaries 0
      (Circuit.mainPostSynthesisSummary actionConfig).regionShapes)).1 :=
  regionStartsFromSummary_def _

/-- The source-summary calculation gives the actual opaque Action circuit's starts. -/
theorem actionCircuit_regionStarts_eq_source :
    actionCircuit.regionStarts = actionSourceRegionStarts :=
  (topLevel_regionStarts_eq_planSummary actionCircuit).trans
    (congrArg regionStartsFromSummary actionCircuit_synthesisSummary_eq)

end Zcash.Snark.ZeroKnowledge
