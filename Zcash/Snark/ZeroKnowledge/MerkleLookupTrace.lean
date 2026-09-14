import Zcash.Snark.ZeroKnowledge.LookupRangeCheckTrace
import Zcash.Snark.ZeroKnowledge.LookupTraceFold
import Zcash.Snark.ZeroKnowledge.SinsemillaLookupTrace
import Zcash.Circuits.Sinsemilla.Merkle

/-!
# Exact lookup traces of the Merkle-path circuit

A hash layer's lookups come from two sources: the two short range checks on its
decomposed input, and the Sinsemilla chain that hashes it. The conditional swap
and the decomposition gate enable no lookup, so their regions contribute empty
entries and the trace keeps one entry per region.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The seven source regions of a Merkle hash layer: the two short range checks and
the Sinsemilla hash each contribute their own lookups. -/
def merkleHashLookupTrace (config : Sinsemilla.Merkle.Config) (lookup : LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [[], shortLookupTrace lookup, shortLookupTrace lookup, [], [],
    sinsemillaChainLookupTrace config.sinsemilla 0 Sinsemilla.Merkle.HashLayer.merkleNs, []]

/-- A Merkle hash contributes its two short-check lookups. -/
@[lookup_trace_norm]
theorem merkleHash_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (config : Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.HashLayer.Input Fp) (region : RegionIndex) :
    lookupTrace (((Sinsemilla.Merkle.HashLayer.circuit generators point honCurve level hlevel).call
      config input).operations region) = merkleHashLookupTrace config.1 config.2 := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Sinsemilla.Merkle.HashLayer.synthesize generators config.1 config.2
    point honCurve level input).operations region) = _
  simp only [Sinsemilla.Merkle.HashLayer.synthesize, Sinsemilla.HashToPoint.hashMessage,
    lookup_trace_norm, synthesis_summary_norm, merkleHashLookupTrace, shortLookupTrace,
    List.cons_append]

/-- A layer's conditional-swap region precedes its hash-layer regions. -/
def merkleLayerLookupTrace (config : Sinsemilla.Merkle.Config) (lookup : LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [] :: merkleHashLookupTrace config lookup

/-- A Merkle layer contributes only its hash layer's lookups. -/
@[lookup_trace_norm]
theorem merkleLayer_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (sibling : WitgenIR Fp 1) (swap : Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    lookupTrace (((Sinsemilla.Merkle.Layer.circuit generators point honCurve level hlevel sibling swap).call
      config input).operations region) = merkleLayerLookupTrace config.2.1 config.2.2 := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.Layer.circuit, lookup_trace_norm, synthesis_summary_norm,
    merkleLayerLookupTrace, List.cons_append]

/-- Every lookup in a serial Merkle path, with no witness-dependent trace data. -/
@[lookup_trace_norm]
theorem merkleRoot_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level depth : ℕ) (hdepth : level + depth ≤ 2 ^ 10)
    (siblings : ℕ → WitgenIR Fp 1) (swaps : ℕ → Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    lookupTrace (((Sinsemilla.Merkle.CalculateRoot.circuit generators point honCurve level depth hdepth
      siblings swaps).call config input).operations region) =
      (List.replicate depth (merkleLayerLookupTrace config.2.1 config.2.2)).flatten := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((do
    let output ← FormalCircuit.foldCall
      (Sinsemilla.Merkle.CalculateRoot.layerAt generators point honCurve level siblings swaps)
      Sinsemilla.Merkle.CalculateRoot.toInput config input depth
    pure output.node : Circuit Fp (AssignedCell Fp)).operations region) = _
  simp only [lookup_trace_norm]
  trans (List.ofFn fun _ : Fin depth => merkleLayerLookupTrace config.2.1 config.2.2).flatten
  · apply lookupTrace_foldCall (traces := fun _ => merkleLayerLookupTrace config.2.1 config.2.2)
    intro index input current
    simp only [Sinsemilla.Merkle.CalculateRoot.layerAt, lookup_trace_norm]
  · simp

end Zcash.Snark.ZeroKnowledge
