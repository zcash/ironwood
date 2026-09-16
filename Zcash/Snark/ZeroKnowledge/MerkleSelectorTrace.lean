import Zcash.Snark.ZeroKnowledge.SinsemillaSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace
import Zcash.Snark.ZeroKnowledge.SelectorTraceFold
import Zcash.Circuits.Sinsemilla.Merkle

/-!
# Exact selector traces of the Merkle-path circuit

The per-layer trace has eight regions: the conditional swap followed by seven
hash-layer regions. A serial path is proved to concatenate this trace at each
layer, independently of the node, sibling, and direction witnesses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- Conditional swap enables its configured gate at the requested row, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem condSwap_regionActivations (sibling : WitgenIR Fp 1)
    (swap : Placed ProverEnvironment Fp → Bool) (config : CondSwap.Config)
    (offset : ℕ) (input : Var CondSwap.Input Fp) (region : RegionIndex) :
    regionActivations (((CondSwap.swap sibling swap).call config offset input).operations region) =
      [.enableGate (CondSwap.swapGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Merkle input decomposition retains its configured activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem merkleDecomposition_regionActivations (level : Fp) (config : Sinsemilla.Merkle.Gate.Config)
    (offset : ℕ) (input : Var Sinsemilla.Merkle.Gate.Inputs Fp) (region : RegionIndex) :
    regionActivations (((Sinsemilla.Merkle.Gate.circuit level).call config offset input).operations region) =
      [.enableGate (Sinsemilla.Merkle.Gate.decomposeGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The seven source regions of a Merkle hash layer, including three activation-free loads. -/
def merkleHashActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.Merkle.Config) (lookup : LookupRangeCheck.Config 10) :
    List (List (RegionOperation Fp)) :=
  [[], shortCheckActivations lookup, shortCheckActivations lookup, [], [],
    sinsemillaHashActivations generators config.sinsemilla 0
      Sinsemilla.Merkle.HashLayer.merkleNs,
    [.enableGate (Sinsemilla.Merkle.Gate.decomposeGate config.gate) 0]]

/-- A Merkle hash retains its complete Sinsemilla region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem merkleHash_activationTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (config : Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.HashLayer.Input Fp) (region : RegionIndex) :
    activationTrace (((Sinsemilla.Merkle.HashLayer.circuit generators point honCurve level hlevel).call
      config input).operations region) = merkleHashActivations generators config.1 config.2 := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Sinsemilla.Merkle.HashLayer.synthesize generators config.1 config.2
    point honCurve level input).operations region) = _
  simp only [Sinsemilla.Merkle.HashLayer.synthesize, Sinsemilla.HashToPoint.hashMessage,
    activation_trace_norm, merkleHashActivations, shortCheckActivations, List.cons_append]

/-- A layer's conditional-swap region precedes its hash-layer regions. -/
def merkleLayerActivations (generators : Specs.Sinsemilla.Generators)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10) :
    List (List (RegionOperation Fp)) :=
  [.enableGate (CondSwap.swapGate config.1) 0] ::
    merkleHashActivations generators config.2.1 config.2.2

/-- A Merkle layer retains the swap, decomposition, and hash region traces, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem merkleLayer_activationTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (sibling : WitgenIR Fp 1) (swap : Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    activationTrace (((Sinsemilla.Merkle.Layer.circuit generators point honCurve level hlevel sibling swap).call
      config input).operations region) = merkleLayerActivations generators config := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.Layer.circuit, activation_trace_norm,
    merkleLayerActivations, List.cons_append]

/-- Every source region in a serial Merkle path, with no witness-dependent trace data. -/
@[activation_trace_norm]
theorem merkleRoot_activationTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level depth : ℕ) (hdepth : level + depth ≤ 2 ^ 10)
    (siblings : ℕ → WitgenIR Fp 1) (swaps : ℕ → Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    activationTrace (((Sinsemilla.Merkle.CalculateRoot.circuit generators point honCurve level depth hdepth
      siblings swaps).call config input).operations region) =
      (List.replicate depth (merkleLayerActivations generators config)).flatten := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((do
    let output ← FormalCircuit.foldCall
      (Sinsemilla.Merkle.CalculateRoot.layerAt generators point honCurve level siblings swaps)
      Sinsemilla.Merkle.CalculateRoot.toInput config input depth
    pure output.node : Circuit Fp (AssignedCell Fp)).operations region) = _
  simp only [activation_trace_norm]
  trans (List.ofFn fun _ : Fin depth => merkleLayerActivations generators config).flatten
  · apply activationTrace_foldCall (traces := fun _ => merkleLayerActivations generators config)
    intro index input current
    simp only [Sinsemilla.Merkle.CalculateRoot.layerAt, activation_trace_norm]
  · simp

end Zcash.Snark.ZeroKnowledge
