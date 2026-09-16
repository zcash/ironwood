import Zcash.Snark.ZeroKnowledge.VariableBaseOverflowTrace
import Zcash.Snark.ZeroKnowledge.ActionConfiguration

/-!
# Connecting compact selector traces to Action

The compiler's activation list is exactly the placed compact trace. The source
equation for Action's variable-base multiplication main region also identifies
its only row-zero selector. `ActionSourceSelectorTrace` composes every Action
region; the concrete packing certificate remains a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action

/-- The actual Action compiler consumes exactly the placed source selector trace. -/
theorem actionCircuit_selectorActivations_eq_trace :
    actionCircuit.selectorActivations =
      placeSelectorTrace actionCircuit.regionStarts (selectorTrace actionCircuit.operations) :=
  activations_eq_placeSelectorTrace actionCircuit.regionStarts actionCircuit.operations 0

/-- Incomplete multiplication rounds never activate row zero, discharging their contribution to the
initial-selector check. -/
private theorem incompleteRounds_initial (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    (incompleteRoundsSelectorTrace config offset count).filter (fun activation => activation.2 = 0) = [] := by
  simp [incompleteRoundsSelectorTrace]

/-- Complete multiplication rounds starting above zero do not activate row zero, discharging the
corresponding boundary check. -/
private theorem completeRounds_initial (config : Ecc.MulComplete.Config) (offset count : ℕ)
    (hoffset : 0 < offset) :
    (completeRoundsSelectorTrace config offset count).filter (fun activation => activation.2 = 0) = [] := by
  simp [completeRoundsSelectorTrace, List.filter_eq_nil_iff]
  omega

/-- The main multiplication region's sole row-zero activation, for every configuration. -/
theorem variableBaseMainSelectorTrace_initial (config : Ecc.Mul.Config) :
    (variableBaseMainSelectorTrace config).filter (fun activation => activation.2 = 0) =
      [(config.addConfig.qAdd.index, 0)] := by
  simp [variableBaseMainSelectorTrace, incompleteSelectorTrace,
    incompleteRounds_initial, completeRounds_initial]

/-- The configured main multiplication region enables only selector eight at its
local row zero. This is a source theorem, without a captured-key assumption. -/
theorem actionVariableBaseMain_initial_selector (offset : ℕ)
    (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    (regionSelectorTrace
      ((Ecc.Mul.mainCircuit.call actionConfig.eccConfig.mul offset input).operations region)).filter
        (fun activation => activation.2 = 0) = [(8, 0)] := by
  rw [regionSelectorTrace_eq_project, variableBaseMain_regionActivations,
    variableBaseMainActivations_selectorOf, variableBaseMainSelectorTrace_initial]
  rfl

end Zcash.Snark.ZeroKnowledge
