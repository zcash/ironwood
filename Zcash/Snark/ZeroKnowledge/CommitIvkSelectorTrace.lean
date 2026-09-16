import Zcash.Snark.ZeroKnowledge.CommitDomainSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace

/-!
# Selector trace of the incoming viewing-key commitment

All fourteen regions are derived from the source stages: seven message-piece
regions, the four-region Sinsemilla commitment, and three canonicity regions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The incoming-viewing-key check enables its gate at the requested row, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem commitIvkGate_regionActivations (first second : WitgenIR Fp 1) (config : CommitIvk.Config)
    (offset : ℕ) (input : Var CommitIvk.Inputs Fp) (region : RegionIndex) :
    (((CommitIvk.bundle first second).call config offset input).operations region).flatMap activationOf =
      [.enableGate (CommitIvk.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Incoming-viewing-key canonicity retains both range-check traces and its final gate, supplying
the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem commitIvkCanonicity_activationTrace (first second : WitgenIR Fp 1)
    (config : CommitIvk.Config × LookupRangeCheck.Config 10)
    (input : Var CommitIvk.Canonicity.Inputs Fp) (region : RegionIndex) :
    trace activationOf (((CommitIvk.Canonicity.circuit first second).call config input).operations region) =
      [runningActivations config.2 0 13, runningActivations config.2 0 14,
        [.enableGate (CommitIvk.gate config.1) 0]] := by
  rw [FormalCircuit.call_operations]
  change trace activationOf ((CommitIvk.Canonicity.synth first second config.1 config.2 input).operations region) = _
  simp only [CommitIvk.Canonicity.synth, CommitIvk.Canonicity.gateChild,
    activation_trace_norm, List.cons_append]

/-- The seven interleaved message loads and short checks. -/
def commitIvkPiecesActivations (config : CommitIvk.Main.Config) :
    List (List (RegionOperation Fp)) :=
  let short := shortCheckActivations config.lookupConfig
  [[], short, short, [], [], short, []]

/-- Incoming-viewing-key message preparation retains its complete configured trace, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem commitIvkPieces_activationTrace (config : CommitIvk.Main.Config)
    (ak nk : AssignedCell Fp) (region : RegionIndex) :
    trace activationOf ((CommitIvk.Main.synthPieces config ak nk).operations region) =
      commitIvkPiecesActivations config := by
  simp only [CommitIvk.Main.synthPieces, activation_trace_norm,
    commitIvkPiecesActivations, shortCheckActivations, List.cons_append]

/-- All source regions of the incoming viewing-key commitment. -/
def commitIvkActivations (generators : Specs.Sinsemilla.Generators) (config : CommitIvk.Main.Config) :
    List (List (RegionOperation Fp)) :=
  commitIvkPiecesActivations config ++
    sinsemillaCommitActivations generators CommitIvk.Main.ns
      (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningActivations config.lookupConfig 0 13, runningActivations config.lookupConfig 0 14,
      [.enableGate (CommitIvk.gate config.gate) 0]]

/-- The complete incoming-viewing-key commitment produces its configured source trace, supplying
the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem commitIvk_activationTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : CommitIvk.Main.Config)
    (input : Var CommitIvk.Main.Inputs Fp) (region : RegionIndex) :
    trace activationOf (((CommitIvk.Main.circuit generators base point honCurve).call config input).operations region) =
      commitIvkActivations generators config := by
  rw [FormalCircuit.call_operations]
  change trace activationOf ((CommitIvk.Main.synth generators base point honCurve config input).operations region) = _
  simp only [CommitIvk.Main.synth, activation_trace_norm, NoteCommit.Main.currentRegion_operations,
    commitIvkActivations, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
