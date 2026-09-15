import Zcash.Snark.ZeroKnowledge.ActionWitnessSelectorTrace

/-!
# Activation traces of variable-base scalar multiplication

The incomplete and complete rounds expose their exact activation offsets without
expanding the scalar witness or the intermediate elliptic-curve points.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- Interior incomplete-addition gates occur one row after their round starts. -/
def incompleteRoundsActivations (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin count =>
    [RegionOperation.enableGate (Ecc.MulIncomplete.qMul2Gate config) (offset + i.val + 1)]).flatten

/-- Interior incomplete-addition gates occur one row after their round starts. -/
def incompleteRoundsSelectorTrace (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count => [(config.qMul2.index, offset + i.val + 1)]).flatten

/-- The interior rounds' activations project to their selector labels. -/
theorem incompleteRoundsActivations_selectorOf (config : Ecc.MulIncomplete.Config)
    (offset count : ℕ) :
    (incompleteRoundsActivations config offset count).flatMap selectorOf =
      incompleteRoundsSelectorTrace config offset count := by
  simp only [incompleteRoundsActivations, incompleteRoundsSelectorTrace, flatten_flatMap,
    List.map_ofFn, Function.comp_def, selectorOf, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Ecc.MulIncomplete.qMul2Gate_selector]

/-- Initial, interior, and final incomplete-addition gates in source order. -/
def incompleteActivations (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (RegionOperation Fp) :=
  [.enableGate (Ecc.MulIncomplete.qMul1Gate config) offset] ++
    incompleteRoundsActivations config offset count ++
    [.enableGate (Ecc.MulIncomplete.qMul3Gate config) (offset + count + 1)]

/-- Initial, interior, and final incomplete-addition selectors in source order. -/
def incompleteSelectorTrace (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  [(config.qMul1.index, offset)] ++ incompleteRoundsSelectorTrace config offset count ++
    [(config.qMul3.index, offset + count + 1)]

/-- The incomplete stage's activations project to its selector labels. -/
theorem incompleteActivations_selectorOf (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    (incompleteActivations config offset count).flatMap selectorOf =
      incompleteSelectorTrace config offset count := by
  simp only [incompleteActivations, incompleteSelectorTrace, List.flatMap_append,
    incompleteRoundsActivations_selectorOf, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, selectorOf, Ecc.MulIncomplete.qMul1Gate_selector,
    Ecc.MulIncomplete.qMul3Gate_selector]

/-- One incomplete multiplication round records its configured gate, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem incompleteRound_regionActivations (bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionActivations (((Ecc.MulIncomplete.round bit).call config offset input).operations region) =
      [.enableGate (Ecc.MulIncomplete.qMul2Gate config) (offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem incompleteRound_regionSelectorTrace (bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.round bit).call config offset input).operations region) =
      [(config.qMul2.index, offset + 1)] := by
  rw [regionSelectorTrace_eq_project, incompleteRound_regionActivations]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, selectorOf,
    Ecc.MulIncomplete.qMul2Gate_selector]

/-- Incomplete multiplication rounds retain their successive activation rows, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem incompleteLoop_regionActivations (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionActivations (((Ecc.MulIncomplete.loop count bit).call config offset input).operations region) =
      incompleteRoundsActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Ecc.MulIncomplete.loopProgram count bit config offset input).operations region) = _
  rw [Ecc.MulIncomplete.loopProgram_operations]
  simp only [activation_trace_norm, Nat.mul_one, incompleteRoundsActivations]

@[selector_trace_norm]
theorem incompleteLoop_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.loop count bit).call config offset input).operations region) =
      incompleteRoundsSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, incompleteLoop_regionActivations,
    incompleteRoundsActivations_selectorOf]

/-- The incomplete multiplication stage retains its complete activation trace, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem incomplete_regionActivations (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var Ecc.MulIncomplete.Inputs Fp) (region : RegionIndex) :
    regionActivations (((Ecc.MulIncomplete.double_and_add count bit).call config offset input).operations region) =
      incompleteActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Ecc.MulIncomplete.double_and_add, activation_trace_norm,
    Ecc.MulIncomplete.operations_readState, incompleteActivations, List.append_assoc]

@[selector_trace_norm]
theorem incomplete_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var Ecc.MulIncomplete.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.double_and_add count bit).call config offset input).operations region) =
      incompleteSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, incomplete_regionActivations,
    incompleteActivations_selectorOf]

/-- The decomposition gate and the two complete additions in each bit round. -/
def completeRoundsActivations (config : Ecc.MulComplete.Config) (offset count : ℕ) :
    List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin count =>
    [RegionOperation.enableGate (Ecc.MulComplete.decomposeGate config) (offset + i.val * 2 + 1),
      RegionOperation.enableGate (completeAddGate config.addConfig) (offset + i.val * 2),
      RegionOperation.enableGate (completeAddGate config.addConfig)
        (offset + i.val * 2 + 1)]).flatten

/-- The decomposition selector and the two complete-addition selectors in each bit round. -/
def completeRoundsSelectorTrace (config : Ecc.MulComplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qDecompose.index, offset + i.val * 2 + 1),
      (config.addConfig.qAdd.index, offset + i.val * 2),
      (config.addConfig.qAdd.index, offset + i.val * 2 + 1)]).flatten

/-- The complete rounds' activations project to their selector labels. -/
theorem completeRoundsActivations_selectorOf (config : Ecc.MulComplete.Config)
    (offset count : ℕ) :
    (completeRoundsActivations config offset count).flatMap selectorOf =
      completeRoundsSelectorTrace config offset count := by
  simp [completeRoundsActivations, completeRoundsSelectorTrace, flatten_flatMap,
    Function.comp_def, selectorOf, Ecc.MulComplete.decomposeGate_selector, completeAddGate]

/-- One complete multiplication round records its configured gates, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem completeRound_regionActivations (bit iteration : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.RoundInputs Fp) (region : RegionIndex) :
    regionActivations (((Ecc.MulComplete.round bit iteration).call config offset input).operations region) =
      [.enableGate (Ecc.MulComplete.decomposeGate config) (offset + 1),
        .enableGate (completeAddGate config.addConfig) offset,
        .enableGate (completeAddGate config.addConfig) (offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Ecc.MulComplete.roundSynthesize bit iteration config offset input).operations region) = _
  simp only [Ecc.MulComplete.roundSynthesize, activation_trace_norm, List.cons_append]

@[selector_trace_norm]
theorem completeRound_regionSelectorTrace (bit iteration : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.RoundInputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulComplete.round bit iteration).call config offset input).operations region) =
      [(config.qDecompose.index, offset + 1), (config.addConfig.qAdd.index, offset),
        (config.addConfig.qAdd.index, offset + 1)] := by
  rw [regionSelectorTrace_eq_project, completeRound_regionActivations]
  simp [selectorOf, Ecc.MulComplete.decomposeGate_selector, completeAddGate]

/-- Copying the complete-round initial state adds no activation, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem completeStartCopy_regionActivations (config : Ecc.MulComplete.Config)
    (input : Var Ecc.MulComplete.Inputs Fp) (offset : ℕ) (region : RegionIndex) :
    regionActivations ((Ecc.MulComplete.startCopy config input offset).operations region) = [] := rfl

@[selector_trace_norm]
theorem completeStartCopy_regionSelectorTrace (config : Ecc.MulComplete.Config)
    (input : Var Ecc.MulComplete.Inputs Fp) (offset : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulComplete.startCopy config input offset).operations region) = [] := rfl

/-- The complete multiplication stage retains its complete activation trace, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem complete_regionActivations (count bit : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.Inputs Fp) (region : RegionIndex) :
    regionActivations (((Ecc.MulComplete.assign_region count bit).call config offset input).operations region) =
      completeRoundsActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Ecc.MulComplete.assignRegionSynthesize count bit config offset input).operations region) = _
  simp only [Ecc.MulComplete.assignRegionSynthesize, activation_trace_norm,
    Ecc.MulComplete.operations_zsCells, completeRoundsActivations]

@[selector_trace_norm]
theorem complete_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulComplete.assign_region count bit).call config offset input).operations region) =
      completeRoundsSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, complete_regionActivations,
    completeRoundsActivations_selectorOf]

/-- Every activation in the actual variable-base multiplication main region. -/
def variableBaseMainActivations (config : Ecc.Mul.Config) : List (RegionOperation Fp) :=
  [.enableGate (completeAddGate config.addConfig) 0] ++
    incompleteActivations config.hiConfig 1 124 ++
    incompleteActivations config.loConfig 1 125 ++
    completeRoundsActivations config.completeConfig 129 3 ++
    [.enableGate (Ecc.Mul.lsbGate config) 135,
      .enableGate (completeAddGate config.addConfig) 135]

/-- Every selector activation in the actual variable-base multiplication main region. -/
def variableBaseMainSelectorTrace (config : Ecc.Mul.Config) : List (ℕ × ℕ) :=
  [(config.addConfig.qAdd.index, 0)] ++
    incompleteSelectorTrace config.hiConfig 1 124 ++
    incompleteSelectorTrace config.loConfig 1 125 ++
    completeRoundsSelectorTrace config.completeConfig 129 3 ++
    [(config.qMulLsb.index, 135), (config.addConfig.qAdd.index, 135)]

/-- The main region's activations project to its selector labels. -/
theorem variableBaseMainActivations_selectorOf (config : Ecc.Mul.Config) :
    (variableBaseMainActivations config).flatMap selectorOf =
      variableBaseMainSelectorTrace config := by
  simp [variableBaseMainActivations, variableBaseMainSelectorTrace, selectorOf,
    incompleteActivations_selectorOf, completeRoundsActivations_selectorOf, completeAddGate,
    Ecc.Mul.lsbGate_selector]

/-- The main variable-base multiplication region retains both round schedules, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem variableBaseMain_regionActivations (config : Ecc.Mul.Config)
    (offset : ℕ) (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    regionActivations ((Ecc.Mul.mainCircuit.call config offset input).operations region) =
      variableBaseMainActivations config := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Ecc.Mul.mainSynthesize config input).operations region) = _
  simp only [Ecc.Mul.mainSynthesize, activation_trace_norm,
    Ecc.Mul.offInit, Ecc.Mul.offHi, Ecc.Mul.offLo, Ecc.Mul.offComp, Ecc.Mul.offLsb,
    Ecc.Mul.loSpan, Ecc.Mul.compSpan, variableBaseMainActivations,
    List.cons_append, List.append_assoc]

@[selector_trace_norm]
theorem variableBaseMain_regionSelectorTrace (config : Ecc.Mul.Config)
    (offset : ℕ) (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.Mul.mainCircuit.call config offset input).operations region) =
      variableBaseMainSelectorTrace config := by
  rw [regionSelectorTrace_eq_project, variableBaseMain_regionActivations,
    variableBaseMainActivations_selectorOf]

end Zcash.Snark.ZeroKnowledge
