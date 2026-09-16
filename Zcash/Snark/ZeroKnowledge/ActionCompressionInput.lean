import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActionTracePlacement
import Zcash.Snark.ZeroKnowledge.ActionExpressionDegree
import Zcash.Snark.ZeroKnowledge.SelectorCompressionCount

/-!
# Action compression from certified finite source data

The ordered shape table, source activation trace, and degree vector determine the
actual Action compiler's compression count. This interface removes the full
witness computation from the numerical certificate. It proves the input
correspondence used by the closed count in `ActionCompressionCertificate`.
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

/-- Place the complete source selector trace at those certified source-shape starts. -/
def actionOrderedSelectorActivations : List (ℕ × ℕ) :=
  placeSelectorTrace actionOrderedRegionStarts (actionSourceSelectorTrace actionConfig)

/-- Every actual activation is reproduced by the reduced ordered source calculation. -/
theorem actionCircuit_selectorActivations_eq_ordered :
    actionCircuit.selectorActivations = actionOrderedSelectorActivations :=
  actionCircuit_selectorActivations_eq_sourceTrace.trans
    (congrArg (fun starts => placeSelectorTrace starts (actionSourceSelectorTrace actionConfig))
      actionCircuit_regionStarts_eq_ordered)

/-- The remaining compression calculation on the certified Action inputs. -/
def actionOrderedSelectorCount : ℕ :=
  selectorPackingCount 2048 56 9 actionSelectorDegrees actionOrderedSelectorActivations

/-- Actual Action key generation has exactly the count computed from the finite source data. -/
theorem actionCircuit_newFixedCols_eq_orderedCount :
    actionCircuit.selectorMap.newFixedCols = actionOrderedSelectorCount := by
  have hrows : actionCircuit.n = 2048 := by
    rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
    decide
  have hselectors : actionCircuit.constraintSystem.numSelectors = 56 := actionCircuit_selectorCount_eq
  have hbudget : csDegree actionCircuit.constraintSystem = 9 :=
    actionCircuit.constraintSystem_csDegree.trans actionCircuit_constraintDegree_eq
  unfold actionOrderedSelectorCount
  rw [actionCircuit.selectorMap_eq_derive, deriveSelCompressMap_newFixedCols_eq_count,
    hrows, hselectors, hbudget, actionCircuit_selectorMaxDegrees, actionCircuit_selectorActivations_eq_ordered]

end Zcash.Snark.ZeroKnowledge
