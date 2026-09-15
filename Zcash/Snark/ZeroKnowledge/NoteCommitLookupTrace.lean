import Zcash.Snark.ZeroKnowledge.CommitDomainLookupTrace
import Zcash.Snark.ZeroKnowledge.LookupRangeCheckTrace
import Zcash.Circuits.NoteCommit.MainBundle

/-!
# Complete source lookup trace of note commitment

All forty-three regions are retained in source order. The lookups come from the
range checks — seven short checks interleaved with the message pieces, and the
running checks in the canonicity stages — together with the Sinsemilla chain of
the commitment itself. The ten closing gate regions do not enable any.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The five-region y-coordinate canonicity flow; its closing gate does not enable any lookup. -/
def noteYLookupTrace (config : LookupRangeCheck.Config 10) : List (List (ℕ × ℕ)) :=
  [shortLookupTrace config, shortLookupTrace config,
    runningLookupTrace config 0 25, runningLookupTrace config 0 13, []]

/-- Note-coordinate witnessing contributes its two short and two running checks. -/
@[lookup_trace_norm]
theorem noteY_lookupTrace (witness : WitgenIR Fp 1)
    (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((NoteCommit.YCanonicityCheck.circuit witness).call config
      input).operations region) = noteYLookupTrace config.2 := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((NoteCommit.YCanonicityCheck.synth witness config.1 config.2
    input).operations region) = _
  simp only [NoteCommit.YCanonicityCheck.synth, NoteCommit.YCanonicityCheck.gateChild,
    lookup_trace_norm, synthesis_summary_norm, noteYLookupTrace, shortLookupTrace,
    List.cons_append]

/-- The fifteen message-piece regions: seven carry a short check, the rest none. -/
def notePiecesLookupTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  let short := shortLookupTrace config.lookupConfig
  [[], short, short, [], [], short, [], short, short, [], [], short, [], short, []]

/-- Note message preparation contributes its seven short checks. -/
@[lookup_trace_norm]
theorem notePieces_lookupTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    lookupTrace ((NoteCommit.Main.synthPieces config input).operations region) =
      notePiecesLookupTrace config := by
  simp only [NoteCommit.Main.synthPieces, lookup_trace_norm, synthesis_summary_norm,
    notePiecesLookupTrace, shortLookupTrace, List.cons_append]

/-- The eighteen regions between piece loading and the final gate stages. -/
def noteChecksLookupTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  noteYLookupTrace config.lookupConfig ++ noteYLookupTrace config.lookupConfig ++
    sinsemillaCommitLookupTrace NoteCommit.Main.ns config.hashConfig ++
    [runningLookupTrace config.lookupConfig 0 13, runningLookupTrace config.lookupConfig 0 14,
      runningLookupTrace config.lookupConfig 0 14, runningLookupTrace config.lookupConfig 0 13]

/-- Note canonicity checks contribute both y-coordinate flows, the commitment's hash, and
four further running checks. -/
@[lookup_trace_norm]
theorem noteChecks_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (base : Ecc.MulFixed.FixedBase) (point : Point Fp) (honCurve : point.OnCurve)
    (config : NoteCommit.Main.Config) (input : Var NoteCommit.Main.Inputs Fp)
    (pieces : NoteCommit.Main.PieceCells) (hashRegion region : RegionIndex) :
    lookupTrace ((NoteCommit.Main.synthChecks generators base point honCurve config input pieces
      hashRegion).operations region) = noteChecksLookupTrace config := by
  simp only [NoteCommit.Main.synthChecks, lookup_trace_norm, synthesis_summary_norm,
    noteChecksLookupTrace, List.cons_append, List.append_assoc]

/-- Five decomposition gates followed by five canonicity gates, of which none enables a lookup. -/
def noteGatesLookupTrace : List (List (ℕ × ℕ)) := List.replicate 10 []

/-- The note gate stage does not enable any lookup, in any of its ten regions. -/
@[lookup_trace_norm]
theorem noteGates_lookupTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (checks : NoteCommit.Main.CheckCells) (hashRegion region : RegionIndex) :
    lookupTrace ((NoteCommit.Main.synthGates config input pieces checks
      hashRegion).operations region) = noteGatesLookupTrace := by
  simp only [NoteCommit.Main.synthGates, NoteCommit.Main.synthDecompositions,
    NoteCommit.Main.synthCanonicity, NoteCommit.Main.synthGdPkdValueCanonicity,
    NoteCommit.Main.synthRhoPsiCanonicity, lookup_trace_norm, synthesis_summary_norm,
    noteGatesLookupTrace, List.cons_append]
  rfl

/-- The complete note-commitment source lookup trace, before global region placement. -/
def noteCommitLookupTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  notePiecesLookupTrace config ++ noteChecksLookupTrace config ++ noteGatesLookupTrace

/-- The trace holds exactly as many activations as the circuit's own summary counts, tying
the two derivations together so neither can drift. -/
theorem noteCommitLookupTrace_length (config : NoteCommit.Main.Config) :
    (noteCommitLookupTrace config).flatten.length =
      (NoteCommit.Main.synthesisSummary config).lookupActivationCount := by
  rw [NoteCommit.Main.synthesisSummary_lookupActivationCount]
  simp only [noteCommitLookupTrace, notePiecesLookupTrace, noteChecksLookupTrace,
    noteGatesLookupTrace, noteYLookupTrace, sinsemillaCommitLookupTrace,
    shortLookupTrace, runningLookupTrace, sinsemillaChainLookupTrace,
    sinsemillaPieceLookupTrace, sinsemillaRoundsLookupTrace, NoteCommit.Main.ns,
    List.length_flatten, List.map_ofFn, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate, Function.comp_def]
  rfl

/-- The complete note commitment produces its composed source lookup trace. -/
@[lookup_trace_norm]
theorem noteCommit_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (base : Ecc.MulFixed.FixedBase) (point : Point Fp) (honCurve : point.OnCurve)
    (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((NoteCommit.Main.circuit generators base point honCurve).call
      config input).operations region) = noteCommitLookupTrace config := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((NoteCommit.Main.synth generators base point honCurve
    config input).operations region) = _
  simp only [NoteCommit.Main.synth, lookup_trace_norm, synthesis_summary_norm,
    NoteCommit.Main.currentRegion_operations, noteCommitLookupTrace, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
