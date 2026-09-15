import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Snark.ZeroKnowledge.ActivationTrace
import Zcash.Circuits.Sinsemilla.HashToPoint

/-!
# Exact activation traces of Sinsemilla hashing

Lookup and gate activations are both retained, including repeated activation of
the same selector at a row. The formulas preserve piece order and boundary rows
without evaluating generator points, message pieces, or witness programs.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
Sinsemilla is where keeping the activations earns the most: a round enables its lookup and its
gate at the same row, and both carry `qS1`, so a selector label cannot tell them apart.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- Each interior Sinsemilla row enables the lookup and then the gate. -/
def sinsemillaRoundsActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) : List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin count =>
    [RegionOperation.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config)
        [config.qS1] (offset + i.val),
      RegionOperation.enableGate (Sinsemilla.HashPiece.sinsemillaGate config)
        (offset + i.val)]).flatten

/-- Each interior Sinsemilla row enables the lookup and then the gate. -/
def sinsemillaRoundsSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qS1.index, offset + i.val), (config.qS1.index, offset + i.val)]).flatten

/-- A run of Sinsemilla round activations projects to its selector labels. -/
theorem sinsemillaRoundsActivations_selectorOf (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    (sinsemillaRoundsActivations generators config offset count).flatMap selectorOf =
      sinsemillaRoundsSelectorTrace config offset count := by
  simp only [sinsemillaRoundsActivations, sinsemillaRoundsSelectorTrace, flatten_flatMap,
    List.map_ofFn, Function.comp_def, selectorOf, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, Sinsemilla.HashPiece.sinsemillaGate_selector,
    ComplexSelector.toSelector_index, List.singleton_append]

/-- A piece ends with the boundary lookup; its linking gate belongs to the chain. -/
def sinsemillaPieceActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) : List (RegionOperation Fp) :=
  sinsemillaRoundsActivations generators config offset count ++
    [.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config) [config.qS1]
      (offset + count)]

/-- A piece ends with the boundary lookup; its linking gate belongs to the chain. -/
def sinsemillaPieceSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  sinsemillaRoundsSelectorTrace config offset count ++ [(config.qS1.index, offset + count)]

/-- One Sinsemilla round records its lookup and its gate, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaRound_regionActivations (generators : Specs.Sinsemilla.Generators) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.HashPiece.round generators index).call config offset input).operations region) =
      [.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config) [config.qS1] offset,
        .enableGate (Sinsemilla.HashPiece.sinsemillaGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem sinsemillaRound_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.round generators index).call config offset input).operations region) =
      [(config.qS1.index, offset), (config.qS1.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Successive Sinsemilla rounds retain their ordered activation rows, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaLoop_regionActivations (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.HashPiece.loop generators count).call config offset input).operations region) =
      sinsemillaRoundsActivations generators config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellVec,
    sinsemillaRoundsActivations, Nat.mul_one]

@[selector_trace_norm]
theorem sinsemillaLoop_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.loop generators count).call config offset input).operations region) =
      sinsemillaRoundsSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, sinsemillaLoop_regionActivations,
    sinsemillaRoundsActivations_selectorOf]

/-- A Sinsemilla message piece retains its complete activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaPiece_regionActivations (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (final : Bool) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.HashPiece.circuit generators count final initialY).call
      config offset input).operations region) =
      sinsemillaPieceActivations generators config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Sinsemilla.HashPiece.circuitBody generators count final initialY
    config offset input).operations region) = _
  simp only [Sinsemilla.HashPiece.circuitBody, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    Sinsemilla.HashPiece.operations_cellVec, sinsemillaPieceActivations]
  rfl

/-- A piece's activations project to its selector labels. -/
theorem sinsemillaPieceActivations_selectorOf (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    (sinsemillaPieceActivations generators config offset count).flatMap selectorOf =
      sinsemillaPieceSelectorTrace config offset count := by
  simp only [sinsemillaPieceActivations, sinsemillaPieceSelectorTrace, List.flatMap_append,
    sinsemillaRoundsActivations_selectorOf, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, selectorOf, List.map_cons, List.map_nil,
    ComplexSelector.toSelector_index]

@[selector_trace_norm]
theorem sinsemillaPiece_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (final : Bool) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.circuit generators count final initialY).call
      config offset input).operations region) = sinsemillaPieceSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, sinsemillaPiece_regionActivations,
    sinsemillaPieceActivations_selectorOf]

/-- A Sinsemilla slot retains the trace of its message piece, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaSlot_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.Chain.slot generators widths initialY index).call
      config offset input).operations region) =
      sinsemillaPieceActivations generators config offset (widths.getD index 0) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.slot, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt]

@[selector_trace_norm]
theorem sinsemillaSlot_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.Chain.slot generators widths initialY index).call
      config offset input).operations region) = sinsemillaPieceSelectorTrace config offset (widths.getD index 0) := by
  rw [regionSelectorTrace_eq_project, sinsemillaSlot_regionActivations,
    sinsemillaPieceActivations_selectorOf]

/-- Every piece and its boundary linking gate, in the chain's exact loop order. -/
def sinsemillaChainActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin widths.length =>
    let base := offset + Sinsemilla.Chain.prefixRows widths i.val
    sinsemillaPieceActivations generators config base (widths.getD i.val 0) ++
      [.enableGate (Sinsemilla.HashPiece.sinsemillaGate config)
        (base + widths.getD i.val 0)]).flatten

/-- Every piece and its boundary linking gate, in the chain's exact loop order. -/
def sinsemillaChainSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin widths.length =>
    let base := offset + Sinsemilla.Chain.prefixRows widths i.val
    sinsemillaPieceSelectorTrace config base (widths.getD i.val 0) ++
      [(config.qS1.index, base + widths.getD i.val 0)]).flatten

/-- A chain's activations project to its selector labels. -/
theorem sinsemillaChainActivations_selectorOf (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    (sinsemillaChainActivations generators config offset widths).flatMap selectorOf =
      sinsemillaChainSelectorTrace config offset widths := by
  simp only [sinsemillaChainActivations, sinsemillaChainSelectorTrace, flatten_flatMap,
    List.map_ofFn, Function.comp_def, List.flatMap_append, sinsemillaPieceActivations_selectorOf,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, selectorOf,
    Sinsemilla.HashPiece.sinsemillaGate_selector, ComplexSelector.toSelector_index]

/-- A chain of Sinsemilla pieces retains their activation order, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaChain_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.Chain.circuit generators widths initialY).call
      config offset input).operations region) =
      sinsemillaChainActivations generators config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    sinsemillaChainActivations]

@[selector_trace_norm]
theorem sinsemillaChain_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.Chain.circuit generators widths initialY).call
      config offset input).operations region) = sinsemillaChainSelectorTrace config offset widths := by
  rw [regionSelectorTrace_eq_project, sinsemillaChain_regionActivations,
    sinsemillaChainActivations_selectorOf]

/-- The domain-point initialization gate followed by all message-piece activations. -/
def sinsemillaHashActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (RegionOperation Fp) :=
  [.enableGate (Sinsemilla.HashPiece.initialYQGate config) offset] ++
    sinsemillaChainActivations generators config offset widths

/-- The domain-point initialization gate followed by all message-piece activations. -/
def sinsemillaHashSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (ℕ × ℕ) :=
  [(config.qS4.index, offset)] ++ sinsemillaChainSelectorTrace config offset widths

/-- A hash's activations project to its selector labels. -/
theorem sinsemillaHashActivations_selectorOf (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    (sinsemillaHashActivations generators config offset widths).flatMap selectorOf =
      sinsemillaHashSelectorTrace config offset widths := by
  simp only [sinsemillaHashActivations, sinsemillaHashSelectorTrace, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, selectorOf,
    sinsemillaChainActivations_selectorOf, Sinsemilla.HashPiece.initialYQGate_selector]

/-- The Sinsemilla hash retains its complete source activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaHash_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.HashToPoint.hashRegion generators widths point honCurve hwidths).call
      config offset input).operations region) =
      sinsemillaHashActivations generators config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Sinsemilla.HashToPoint.hashRegionSynthesize generators widths point
    config offset input).operations region) = _
  simp only [Sinsemilla.HashToPoint.hashRegionSynthesize, activation_trace_norm,
    Sinsemilla.HashToPoint.z1Cells_operations, sinsemillaHashActivations]

@[selector_trace_norm]
theorem sinsemillaHash_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashToPoint.hashRegion generators widths point honCurve hwidths).call
      config offset input).operations region) = sinsemillaHashSelectorTrace config offset widths := by
  rw [regionSelectorTrace_eq_project, sinsemillaHash_regionActivations,
    sinsemillaHashActivations_selectorOf]

/-- The Sinsemilla hash retains its complete source activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaHash_activationTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    activationTrace (((Sinsemilla.HashToPoint.hashCircuit generators widths point honCurve hwidths).call
      config input).operations region) = [sinsemillaHashActivations generators config 0 widths] := by
  simp only [Sinsemilla.HashToPoint.hashCircuit, activation_trace_norm]

@[selector_trace_norm]
theorem sinsemillaHash_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    selectorTrace (((Sinsemilla.HashToPoint.hashCircuit generators widths point honCurve hwidths).call
      config input).operations region) = [sinsemillaHashSelectorTrace config 0 widths] := by
  simp only [Sinsemilla.HashToPoint.hashCircuit, selector_trace_norm]

/-- Witnessing a Sinsemilla message piece preserves its region slot, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem witnessMessagePiece_activationTrace (config : Sinsemilla.HashPiece.Config)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    activationTrace ((Sinsemilla.HashToPoint.witnessMessagePiece config witness).operations region) = [[]] := rfl

@[selector_trace_norm]
theorem witnessMessagePiece_selectorTrace (config : Sinsemilla.HashPiece.Config) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    selectorTrace ((Sinsemilla.HashToPoint.witnessMessagePiece config witness).operations region) = [[]] := rfl

end Zcash.Snark.ZeroKnowledge
