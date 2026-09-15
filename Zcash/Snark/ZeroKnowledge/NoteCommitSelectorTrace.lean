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

/-- The five-region y-coordinate canonicity flow. -/
def noteYSelectorTrace (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [shortSelectorTrace config.2, shortSelectorTrace config.2,
    runningSelectorTrace config.2 0 25, runningSelectorTrace config.2 0 13,
    [(config.1.qYCanon.index, 0)]]

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

/-- Note-coordinate witnessing retains its configured region trace, supplying the source metadata
for Action selector coverage. -/
@[selector_trace_norm]
theorem noteY_selectorTrace (witness : WitgenIR Fp 1)
    (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((NoteCommit.YCanonicityCheck.circuit witness).call config input).operations region) =
      noteYSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((NoteCommit.YCanonicityCheck.synth witness config.1 config.2 input).operations region) = _
  simp only [NoteCommit.YCanonicityCheck.synth, NoteCommit.YCanonicityCheck.gateChild,
    selector_trace_norm, noteYSelectorTrace, shortSelectorTrace, List.cons_append]

/-- The fifteen interleaved message-piece loads and short checks. -/
def notePiecesActivations (config : NoteCommit.Main.Config) : List (List (RegionOperation Fp)) :=
  let short := shortCheckActivations config.lookupConfig
  [[], short, short, [], [], short, [], short, short, [], [], short, [], short, []]

/-- The fifteen interleaved message-piece loads and short checks. -/
def notePiecesSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  let short := shortSelectorTrace config.lookupConfig
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

/-- Note message preparation retains its configured region traces, supplying the source metadata for
Action selector coverage. -/
@[selector_trace_norm]
theorem notePieces_selectorTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthPieces config input).operations region) =
      notePiecesSelectorTrace config := by
  simp only [NoteCommit.Main.synthPieces, selector_trace_norm,
    notePiecesSelectorTrace, shortSelectorTrace, List.cons_append]

/-- The eighteen regions between piece loading and the final gate stages. -/
def noteChecksActivations (generators : Specs.Sinsemilla.Generators) (config : NoteCommit.Main.Config) :
    List (List (RegionOperation Fp)) :=
  noteYActivations (config.gates.y, config.lookupConfig) ++
    noteYActivations (config.gates.y, config.lookupConfig) ++
    sinsemillaCommitActivations generators NoteCommit.Main.ns
      (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningActivations config.lookupConfig 0 13, runningActivations config.lookupConfig 0 14,
      runningActivations config.lookupConfig 0 14, runningActivations config.lookupConfig 0 13]

/-- The eighteen regions between piece loading and the final gate stages. -/
def noteChecksSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  noteYSelectorTrace (config.gates.y, config.lookupConfig) ++
    noteYSelectorTrace (config.gates.y, config.lookupConfig) ++
    sinsemillaCommitSelectorTrace NoteCommit.Main.ns (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningSelectorTrace config.lookupConfig 0 13, runningSelectorTrace config.lookupConfig 0 14,
      runningSelectorTrace config.lookupConfig 0 14, runningSelectorTrace config.lookupConfig 0 13]

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

/-- Note canonicity checks retain their configured region traces, supplying the source metadata for
Action selector coverage. -/
@[selector_trace_norm]
theorem noteChecks_selectorTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (hashRegion region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthChecks generators base point honCurve config input pieces hashRegion).operations region) =
      noteChecksSelectorTrace config := by
  simp only [NoteCommit.Main.synthChecks, selector_trace_norm,
    noteChecksSelectorTrace, List.cons_append, List.append_assoc]

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

/-- Five decomposition gates followed by five canonicity gates. -/
def noteGatesSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  [[(config.gates.b.qNotecommitB.index, 0)], [(config.gates.d.qNotecommitD.index, 0)],
    [(config.gates.e.qNotecommitE.index, 0)], [(config.gates.g.qNotecommitG.index, 0)],
    [(config.gates.h.qNotecommitH.index, 0)], [(config.gates.gd.qNotecommitGd.index, 0)],
    [(config.gates.pkd.qNotecommitPkd.index, 0)], [(config.gates.value.qNotecommitValue.index, 0)],
    [(config.gates.rho.qNotecommitRho.index, 0)], [(config.gates.psi.qNotecommitPsi.index, 0)]]

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

/-- The note gate stage retains its configured region traces, supplying the source metadata for
Action selector coverage. -/
@[selector_trace_norm]
theorem noteGates_selectorTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (checks : NoteCommit.Main.CheckCells) (hashRegion region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthGates config input pieces checks hashRegion).operations region) =
      noteGatesSelectorTrace config := by
  simp only [NoteCommit.Main.synthGates, NoteCommit.Main.synthDecompositions,
    NoteCommit.Main.synthCanonicity, NoteCommit.Main.synthGdPkdValueCanonicity,
    NoteCommit.Main.synthRhoPsiCanonicity, selector_trace_norm,
    noteGatesSelectorTrace, List.cons_append]

/-- The complete note-commitment source trace, before global region placement. -/
def noteCommitActivations (generators : Specs.Sinsemilla.Generators) (config : NoteCommit.Main.Config) :
    List (List (RegionOperation Fp)) :=
  notePiecesActivations config ++ noteChecksActivations generators config ++
    noteGatesActivations config

/-- The complete note-commitment source trace, before global region placement. -/
def noteCommitSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  notePiecesSelectorTrace config ++ noteChecksSelectorTrace config ++ noteGatesSelectorTrace config

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

/-- The complete note commitment retains its composed source trace, supplying the source metadata
for Action selector coverage. -/
@[selector_trace_norm]
theorem noteCommit_selectorTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((NoteCommit.Main.circuit generators base point honCurve).call config input).operations region) =
      noteCommitSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((NoteCommit.Main.synth generators base point honCurve config input).operations region) = _
  simp only [NoteCommit.Main.synth, selector_trace_norm, NoteCommit.Main.currentRegion_operations,
    noteCommitSelectorTrace, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
