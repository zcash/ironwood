import Zcash.Snark.ZeroKnowledge.CommitDomainLookupTrace
import Zcash.Snark.ZeroKnowledge.LookupRangeCheckTrace
import Zcash.Circuits.CommitIvk.Main
import Zcash.Circuits.CommitIvk.MainBundle

/-!
# Lookup trace of the incoming viewing-key commitment

The lookups come from two places: the three short range checks interleaved with the
message pieces, and the two running checks in the canonicity stage. The commitment's
own Sinsemilla hash contributes its chain; the final gate region enables none.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Incoming-viewing-key canonicity contributes both running range-check traces; its
closing gate region enables no lookup. -/
@[lookup_trace_norm]
theorem commitIvkCanonicity_lookupTrace (first second : WitgenIR Fp 1)
    (config : CommitIvk.Config × LookupRangeCheck.Config 10)
    (input : Var CommitIvk.Canonicity.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((CommitIvk.Canonicity.circuit first second).call config
      input).operations region) =
      [runningLookupTrace config.2 0 13, runningLookupTrace config.2 0 14, []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((CommitIvk.Canonicity.synth first second config.1 config.2
    input).operations region) = _
  simp only [CommitIvk.Canonicity.synth, CommitIvk.Canonicity.gateChild,
    lookup_trace_norm, synthesis_summary_norm, List.cons_append]

/-- The seven message-piece regions: three carry a short check, the rest none. -/
def commitIvkPiecesLookupTrace (config : CommitIvk.Main.Config) : List (List (ℕ × ℕ)) :=
  let short := shortLookupTrace config.lookupConfig
  [[], short, short, [], [], short, []]

/-- Incoming-viewing-key message preparation contributes its three short checks. -/
@[lookup_trace_norm]
theorem commitIvkPieces_lookupTrace (config : CommitIvk.Main.Config)
    (ak nk : AssignedCell Fp) (region : RegionIndex) :
    lookupTrace ((CommitIvk.Main.synthPieces config ak nk).operations region) =
      commitIvkPiecesLookupTrace config := by
  simp only [CommitIvk.Main.synthPieces, lookup_trace_norm, synthesis_summary_norm,
    commitIvkPiecesLookupTrace, shortLookupTrace, List.cons_append]

/-- All source regions of the incoming viewing-key commitment. -/
def commitIvkLookupTrace (config : CommitIvk.Main.Config) : List (List (ℕ × ℕ)) :=
  commitIvkPiecesLookupTrace config ++
    sinsemillaCommitLookupTrace CommitIvk.Main.ns config.hashConfig ++
    [runningLookupTrace config.lookupConfig 0 13, runningLookupTrace config.lookupConfig 0 14, []]

/-- The trace holds exactly as many activations as the circuit's own summary counts, tying
the two derivations together so neither can drift. -/
theorem commitIvkLookupTrace_length (config : CommitIvk.Main.Config) :
    (commitIvkLookupTrace config).flatten.length =
      (CommitIvk.Main.synthesisSummary config).lookupActivationCount := by
  rw [CommitIvk.Main.synthesisSummary_lookupActivationCount]
  simp only [commitIvkLookupTrace, commitIvkPiecesLookupTrace, sinsemillaCommitLookupTrace,
    shortLookupTrace, runningLookupTrace, sinsemillaChainLookupTrace,
    sinsemillaPieceLookupTrace, sinsemillaRoundsLookupTrace, CommitIvk.Main.ns,
    List.length_flatten, List.map_ofFn, List.map_cons, List.map_nil, List.map_append,
    List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  rfl

/-- The complete incoming-viewing-key commitment produces its configured lookup trace. -/
@[lookup_trace_norm]
theorem commitIvk_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (base : Ecc.MulFixed.FixedBase) (point : Point Fp) (honCurve : point.OnCurve)
    (config : CommitIvk.Main.Config)
    (input : Var CommitIvk.Main.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((CommitIvk.Main.circuit generators base point honCurve).call
      config input).operations region) = commitIvkLookupTrace config := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((CommitIvk.Main.synth generators base point honCurve
    config input).operations region) = _
  simp only [CommitIvk.Main.synth, lookup_trace_norm, synthesis_summary_norm,
    NoteCommit.Main.currentRegion_operations, commitIvkLookupTrace, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
