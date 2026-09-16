import Zcash.Snark.ZeroKnowledge.NoteGateSelectorTrace
import Zcash.Snark.ZeroKnowledge.CommitDomainSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace
import Zcash.Circuits.NoteCommit.MainBundle

/-!
# Complete source selector trace of note commitment

All forty-three regions are retained in source order: fifteen piece-loading
regions, eighteen hash and canonicity-check regions, and ten final gate regions.
The trace is independent of note data and commitment blinding witnesses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The five-region y-coordinate canonicity flow. -/
def noteYActivations (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10) :
    List (List (RegionOperation Fp)) :=
  [shortCheckActivations config.2, shortCheckActivations config.2,
    runningActivations config.2 0 25, runningActivations config.2 0 13,
    [.enableGate (NoteCommit.YCanonicity.gate config.1) 0]]

/-- Note-coordinate witnessing retains its configured region trace, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem noteY_activationTrace (witness : WitgenIR Fp 1)
    (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (region : RegionIndex) :
    activationTrace (((NoteCommit.YCanonicityCheck.circuit witness).call config input).operations region) =
      noteYActivations config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((NoteCommit.YCanonicityCheck.synth witness config.1 config.2 input).operations region) = _
  simp only [NoteCommit.YCanonicityCheck.synth, NoteCommit.YCanonicityCheck.gateChild,
    activation_trace_norm, noteYActivations, shortCheckActivations, List.cons_append]

/-- The fifteen interleaved message-piece loads and short checks. -/
def notePiecesActivations (config : NoteCommit.Main.Config) : List (List (RegionOperation Fp)) :=
  let short := shortCheckActivations config.lookupConfig
  [[], short, short, [], [], short, [], short, short, [], [], short, [], short, []]

/-- Note message preparation retains its configured region traces, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem notePieces_activationTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    activationTrace ((NoteCommit.Main.synthPieces config input).operations region) =
      notePiecesActivations config := by
  simp only [NoteCommit.Main.synthPieces, activation_trace_norm,
    notePiecesActivations, shortCheckActivations, List.cons_append]

/-- The eighteen regions between piece loading and the final gate stages. -/
def noteChecksActivations (generators : Specs.Sinsemilla.Generators) (config : NoteCommit.Main.Config) :
    List (List (RegionOperation Fp)) :=
  noteYActivations (config.gates.y, config.lookupConfig) ++
    noteYActivations (config.gates.y, config.lookupConfig) ++
    sinsemillaCommitActivations generators NoteCommit.Main.ns
      (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningActivations config.lookupConfig 0 13, runningActivations config.lookupConfig 0 14,
      runningActivations config.lookupConfig 0 14, runningActivations config.lookupConfig 0 13]

/-- Note canonicity checks retain their configured region traces, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem noteChecks_activationTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (hashRegion region : RegionIndex) :
    activationTrace ((NoteCommit.Main.synthChecks generators base point honCurve config input pieces hashRegion).operations region) =
      noteChecksActivations generators config := by
  simp only [NoteCommit.Main.synthChecks, activation_trace_norm,
    noteChecksActivations, List.cons_append, List.append_assoc]

/-- Five decomposition gates followed by five canonicity gates. -/
def noteGatesActivations (config : NoteCommit.Main.Config) : List (List (RegionOperation Fp)) :=
  [[.enableGate (NoteCommit.DecomposeB.gate config.gates.b) 0],
    [.enableGate (NoteCommit.DecomposeD.gate config.gates.d) 0],
    [.enableGate (NoteCommit.DecomposeE.gate config.gates.e) 0],
    [.enableGate (NoteCommit.DecomposeG.gate config.gates.g) 0],
    [.enableGate (NoteCommit.DecomposeH.gate config.gates.h) 0],
    [.enableGate (NoteCommit.GdCanonicity.gate config.gates.gd) 0],
    [.enableGate (NoteCommit.PkdCanonicity.gate config.gates.pkd) 0],
    [.enableGate (NoteCommit.ValueCanonicity.gate config.gates.value) 0],
    [.enableGate (NoteCommit.RhoCanonicity.gate config.gates.rho) 0],
    [.enableGate (NoteCommit.PsiCanonicity.gate config.gates.psi) 0]]

/-- The note gate stage retains its configured region traces, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem noteGates_activationTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (checks : NoteCommit.Main.CheckCells) (hashRegion region : RegionIndex) :
    activationTrace ((NoteCommit.Main.synthGates config input pieces checks hashRegion).operations region) =
      noteGatesActivations config := by
  simp only [NoteCommit.Main.synthGates, NoteCommit.Main.synthDecompositions,
    NoteCommit.Main.synthCanonicity, NoteCommit.Main.synthGdPkdValueCanonicity,
    NoteCommit.Main.synthRhoPsiCanonicity, activation_trace_norm,
    noteGatesActivations, List.cons_append]

/-- The complete note-commitment source trace, before global region placement. -/
def noteCommitActivations (generators : Specs.Sinsemilla.Generators) (config : NoteCommit.Main.Config) :
    List (List (RegionOperation Fp)) :=
  notePiecesActivations config ++ noteChecksActivations generators config ++
    noteGatesActivations config

/-- The complete note commitment retains its composed source trace, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem noteCommit_activationTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    activationTrace (((NoteCommit.Main.circuit generators base point honCurve).call config input).operations region) =
      noteCommitActivations generators config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((NoteCommit.Main.synth generators base point honCurve config input).operations region) = _
  simp only [NoteCommit.Main.synth, activation_trace_norm, NoteCommit.Main.currentRegion_operations,
    noteCommitActivations, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
