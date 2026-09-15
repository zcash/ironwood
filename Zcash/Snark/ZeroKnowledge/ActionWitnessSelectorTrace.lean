import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Snark.ZeroKnowledge.ActivationTrace
import Zcash.Circuits.Action.Circuit

/-!
# Source-derived activation traces for Action witness loading

These equations retain the source circuit's activations and their local rows, for
arbitrary witness programs, input cells, and ambient region indices.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The complete-addition gate of a configuration, spelled as the circuit's own synthesis spells
it. A gate reached through a configuration this wide is worth naming once. -/
def completeAddGate (config : Ecc.Add.Config) : Gate Fp :=
  Ecc.Add.gate config.qAdd config.lambda config.xP config.yP config.xQR config.yQR
    config.alpha config.beta config.gamma config.delta

/-- Point witnessing enables the point gate at its requested row, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem witnessPoint_regionActivations (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionActivations ((Ecc.WitnessPoint.point.call config offset input).operations region) =
      [.enableGate (Ecc.WitnessPoint.pointGate config.qPoint config.x config.y) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem witnessPoint_regionSelectorTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.WitnessPoint.point.call config offset input).operations region) =
      [(config.qPoint.index, offset)] := by
  rw [regionSelectorTrace_eq_project, witnessPoint_regionActivations]
  rfl

/-- Nonidentity point witnessing enables its distinct point gate, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem witnessNonIdPoint_regionActivations (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionActivations ((Ecc.WitnessPoint.pointNonId.call config offset input).operations region) =
      [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.qPointNonId config.x config.y)
        offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem witnessNonIdPoint_regionSelectorTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.WitnessPoint.pointNonId.call config offset input).operations region) =
      [(config.qPointNonId.index, offset)] := by
  rw [regionSelectorTrace_eq_project, witnessNonIdPoint_regionActivations]
  rfl

/-- Complete addition enables the addition gate at its requested row, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem completeAdd_regionActivations (config : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (region : RegionIndex) :
    regionActivations ((Ecc.Add.add.call config offset input).operations region) =
      [.enableGate (completeAddGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem completeAdd_regionSelectorTrace (config : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.Add.add.call config offset input).operations region) =
      [(config.qAdd.index, offset)] := by
  rw [regionSelectorTrace_eq_project, completeAdd_regionActivations]
  rfl

/-- Loading Sinsemilla tables creates no region trace, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaLoad_activationTrace (generators : Specs.Sinsemilla.Generators)
    (table : Sinsemilla.GeneratorTableConfig) (region : RegionIndex) :
    activationTrace ((Sinsemilla.load generators table).operations region) = [] := rfl

@[selector_trace_norm]
theorem sinsemillaLoad_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (table : Sinsemilla.GeneratorTableConfig) (region : RegionIndex) :
    selectorTrace ((Sinsemilla.load generators table).operations region) = [] := rfl

/-- Loading private data retains one empty region trace, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem loadPrivate_activationTrace (column : Column .advice) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    activationTrace ((Action.Circuit.loadPrivate column witness).operations region) = [[]] := rfl

@[selector_trace_norm]
theorem loadPrivate_selectorTrace (column : Column .advice) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    selectorTrace ((Action.Circuit.loadPrivate column witness).operations region) = [[]] := rfl

/-- All eight witness-loading regions, including the five regions with no activations. -/
@[activation_trace_norm]
theorem actionSynthWitness_activationTrace (generators : Specs.Sinsemilla.Generators)
    (witness : Action.Circuit.Witnesses Fp) (config : Action.Circuit.Config) (region : RegionIndex) :
    activationTrace ((Action.Circuit.synthWitness generators witness config).operations region) =
      [[], [],
        [.enableGate (Ecc.WitnessPoint.pointGate config.eccConfig.witnessPoint.qPoint
          config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0],
        [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId
          config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0],
        [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId
          config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0], [], [], []] := by
  simp only [Action.Circuit.synthWitness, Ecc.WitnessPoint.pointFormal,
    Ecc.WitnessPoint.pointNonIdFormal, activation_trace_norm, List.cons_append]

@[selector_trace_norm]
theorem actionSynthWitness_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (witness : Action.Circuit.Witnesses Fp) (config : Action.Circuit.Config) (region : RegionIndex) :
    selectorTrace ((Action.Circuit.synthWitness generators witness config).operations region) =
      [[], [], [(config.eccConfig.witnessPoint.qPoint.index, 0)],
        [(config.eccConfig.witnessPoint.qPointNonId.index, 0)],
        [(config.eccConfig.witnessPoint.qPointNonId.index, 0)], [], [], []] := by
  simp only [Action.Circuit.synthWitness, Ecc.WitnessPoint.pointFormal,
    Ecc.WitnessPoint.pointNonIdFormal, selector_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
