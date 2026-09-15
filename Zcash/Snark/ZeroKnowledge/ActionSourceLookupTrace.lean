import Zcash.Snark.ZeroKnowledge.ActionAuxiliaryLookupTrace
import Zcash.Snark.ZeroKnowledge.MerkleLookupTrace
import Zcash.Snark.ZeroKnowledge.CommitIvkLookupTrace
import Zcash.Snark.ZeroKnowledge.NoteCommitLookupTrace
import Zcash.Snark.ZeroKnowledge.ActionSelectorTrace

/-!
# The complete Action source lookup trace

The three synthesis stages and the post-NU6.3 cross-address region are connected
compositionally to their compact lookup traces. The final equality opens the
opaque top-level circuit only through its recorded implementation equation. It
retains every region, every activation, and each activation's master selector and
local row.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action

/-- Witness loading does not enable any lookup, in any of its eight regions. -/
def actionWitnessLookupTrace : List (List (ℕ × ℕ)) := List.replicate 8 []

/-- Loading the Sinsemilla generator table does not open a region, so it does not contribute an
entry. -/
@[lookup_trace_norm]
theorem sinsemillaLoad_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (table : Sinsemilla.GeneratorTableConfig) (region : RegionIndex) :
    lookupTrace ((Sinsemilla.load generators table).operations region) = [] := rfl

/-- Witnessing a point does not enable any lookup. -/
@[lookup_trace_norm]
theorem witnessPoint_regionLookupTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Zcash.Circuits.Point) Fp) (region : RegionIndex) :
    regionLookupTrace ((Ecc.WitnessPoint.point.call config offset input).operations region)
      = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- All eight witness-loading regions are lookup-free. -/
@[lookup_trace_norm]
theorem actionSynthWitness_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (witness : Circuit.Witnesses Fp) (config : Circuit.Config) (region : RegionIndex) :
    lookupTrace ((Circuit.synthWitness generators witness config).operations region) =
      actionWitnessLookupTrace := by
  simp only [Circuit.synthWitness, Circuit.loadPrivate, Ecc.WitnessPoint.pointFormal,
    Ecc.WitnessPoint.pointNonIdFormal, lookup_trace_norm, synthesis_summary_norm,
    actionWitnessLookupTrace, List.cons_append]
  rfl

/-- The lookups of all 295 integrity-check regions. -/
def actionChecksLookupTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  (List.replicate 16 (merkleLayerLookupTrace config.merkle1 config.lookupConfig)).flatten ++
    (List.replicate 16 (merkleLayerLookupTrace config.merkle2 config.lookupConfig)).flatten ++
    [[], []] ++
    valueCommitLookupTrace ++
    nullifierLookupTrace config.eccConfig.mulFixedBaseField.lookupConfig ++
    spendAuthorityLookupTrace ++
    commitIvkLookupTrace
      { gate := config.commitIvkConfig, hashConfig := config.sinsemilla1,
        lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    addressIntegrityLookupTrace (config.eccConfig.mul, config.eccConfig.witnessPoint)

/-- Action checks produce their configured lookup trace independently of witness values. -/
@[lookup_trace_norm]
theorem actionSynthChecks_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (bases : Circuit.Bases) (witness : Circuit.Witnesses Fp) (config : Circuit.Config)
    (cells : Circuit.WitnessCells) (region : RegionIndex) :
    lookupTrace ((Circuit.synthChecks generators bases witness config cells).operations region) =
      actionChecksLookupTrace config := by
  rw [Circuit.synthChecks_eq]
  simp only [Circuit.synthChecksProgram, Circuit.loadPrivate, lookup_trace_norm,
    synthesis_summary_norm, actionChecksLookupTrace, List.cons_append, List.append_assoc]

/-- The Orchard checks region does not enable any lookup. -/
@[lookup_trace_norm]
theorem actionOrchardChecks_regionLookupTrace (config : Circuit.Config)
    (cells : Circuit.WitnessCells) (checks : Circuit.CheckCells) (region : RegionIndex) :
    regionLookupTrace ((Circuit.synthOrchardChecks config cells checks).operations region)
      = [] := rfl

/-- Old and new note commitments, with their intervening lookup-free witness and copy
regions. -/
def actionNotesLookupTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  noteCommitLookupTrace
      { gates := config.noteCommitOld, hashConfig := config.sinsemilla1,
        lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    [[], [], [], []] ++
    noteCommitLookupTrace
      { gates := config.noteCommitNew, hashConfig := config.sinsemilla2,
        lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    [[]]

/-- The note stages produce their configured lookup traces independently of witness values. -/
@[lookup_trace_norm]
theorem actionSynthNotes_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (bases : Circuit.Bases) (witness : Circuit.Witnesses Fp) (config : Circuit.Config)
    (cells : Circuit.WitnessCells) (checks : Circuit.CheckCells) (region : RegionIndex) :
    lookupTrace ((Circuit.synthNotes generators bases witness config cells
      checks).operations region) = actionNotesLookupTrace config := by
  rw [Circuit.synthNotes_eq]
  simp only [Circuit.synthNotesProgram, Circuit.loadPrivate,
    Ecc.WitnessPoint.pointNonIdFormal, lookup_trace_norm, synthesis_summary_norm,
    actionNotesLookupTrace, List.cons_append, List.append_assoc]

/-- The base Action's complete source lookup trace, independent of witness programs. -/
def actionBaseLookupTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  actionWitnessLookupTrace ++ actionChecksLookupTrace config ++ actionNotesLookupTrace config

/-- Base Action synthesis produces the composed checks-and-notes lookup trace. -/
@[lookup_trace_norm]
theorem actionSynthesizeBase_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (bases : Circuit.Bases) (witness : Circuit.Witnesses Fp) (config : Circuit.Config)
    (region : RegionIndex) :
    lookupTrace ((Circuit.synthesizeBase generators bases witness config).operations region) =
      actionBaseLookupTrace config := by
  simp only [Circuit.synthesizeBase, lookup_trace_norm, synthesis_summary_norm,
    actionBaseLookupTrace, actionWitnessLookupTrace, List.append_assoc]

/-- Calling the base Action circuit preserves its complete source lookup trace. -/
@[lookup_trace_norm]
theorem actionBaseCall_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (bases : Circuit.Bases) (config : Circuit.Config) (input : Var unit Fp)
    (region : RegionIndex) :
    lookupTrace (((Circuit.baseCircuit generators bases).call config input).operations region) =
      actionBaseLookupTrace config := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Circuit.synthesizeBase generators bases Circuit.hintWitnesses
    config).operations region) = _
  exact actionSynthesizeBase_lookupTrace _ _ _ _ _

/-- A cross-address check region does not enable any lookup. -/
@[lookup_trace_norm]
theorem actionCrossAddressRow_regionLookupTrace (config : Circuit.Config)
    (oldCell newCell : AssignedCell Fp) (row : ℕ) (region : RegionIndex) :
    regionLookupTrace ((Circuit.synthCrossAddressRow config oldCell newCell
      row).operations region) = [] := rfl

/-- Cross-address checks occupy one lookup-free region. -/
@[lookup_trace_norm]
theorem actionCrossAddress_lookupTrace (config : Circuit.Config)
    (points : Var Circuit.AddressPoints Fp) (region : RegionIndex) :
    lookupTrace ((Circuit.synthCrossAddressChecks config points).operations region) = [[]] := by
  simp only [Circuit.synthCrossAddressChecks, lookup_trace_norm, List.ofFn_const,
    List.flatten_replicate_nil]

/-- All source regions of the specified post-NU6.3 Action circuit. -/
def actionSourceLookupTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  actionBaseLookupTrace config ++ [[]]

/-- The complete Action source produces the composed base and cross-address lookup traces. -/
@[lookup_trace_norm]
theorem actionMainPost_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (bases : Circuit.Bases) (config : Circuit.Config) (input : Var unit Fp)
    (region : RegionIndex) :
    lookupTrace ((Circuit.mainPost generators bases config input).operations region) =
      actionSourceLookupTrace config := by
  simp only [Circuit.mainPost, lookup_trace_norm, actionSourceLookupTrace]

/-- The source trace holds exactly as many activations as the circuit's own summary counts:
2,424, the number the certified walk materializes. Stating it against the circuit's lemma
rather than the literal keeps the two derivations from drifting apart. -/
theorem actionSourceLookupTrace_length :
    (actionSourceLookupTrace actionConfig).flatten.length =
      actionCircuit.synthesisSummary.lookupActivationCount := by
  rw [actionCircuit_lookupActivationCount_eq]
  simp only [actionSourceLookupTrace, actionBaseLookupTrace, actionWitnessLookupTrace,
    actionChecksLookupTrace, actionNotesLookupTrace, merkleLayerLookupTrace,
    merkleHashLookupTrace, noteCommitLookupTrace, notePiecesLookupTrace,
    noteChecksLookupTrace, noteGatesLookupTrace, noteYLookupTrace,
    commitIvkLookupTrace, commitIvkPiecesLookupTrace, sinsemillaCommitLookupTrace,
    valueCommitLookupTrace, spendAuthorityLookupTrace, nullifierLookupTrace,
    addressIntegrityLookupTrace, variableBaseLookupTrace, mulOverflowLookupTrace,
    shortLookupTrace, runningLookupTrace, sinsemillaChainLookupTrace,
    sinsemillaPieceLookupTrace, sinsemillaRoundsLookupTrace,
    Ecc.MulOverflow.numWords, CommitIvk.Main.ns, NoteCommit.Main.ns,
    Sinsemilla.Merkle.HashLayer.merkleNs,
    List.length_flatten, List.map_ofFn, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate, List.map_flatten, List.length_append, List.length_cons,
    List.length_nil, List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate,
    List.sum_flatten, Function.comp_def]
  rfl

/-- The actual opaque Action circuit has precisely the source-derived compact lookup trace.
This is the only place the opaque top-level circuit is opened, and it is opened through its
recorded implementation equation rather than by reduction. -/
theorem actionCircuit_lookupTrace_eq :
    lookupTrace actionCircuit.operations = actionSourceLookupTrace actionConfig := by
  rw [Internal.actionCircuit_eq_impl]
  change lookupTrace ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases
    actionConfig ()).operations 0) = _
  exact actionMainPost_lookupTrace _ _ _ _ _

/-- The source labels the coverage check is stated over are exactly the placed compositional
trace. This is the substitution that lets the coverage proof drop the certified walk: the
statement it proves is unchanged, only its derivation is. Placement enters definitionally,
since a circuit's `placement` is `regionStarts.getD · 0`. -/
theorem actionCircuit_lookupLabels_eq_sourceTrace :
    sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0 =
      placeSelectorTrace actionCircuit.regionStarts (actionSourceLookupTrace actionConfig) 0 := by
  rw [← operationSourceLookupLabels_eq]
  rw [show actionCircuit.placement = fun region => actionCircuit.regionStarts.getD region 0
    from rfl]
  rw [operationSourceLookupLabels_eq_placeTrace, actionCircuit_lookupTrace_eq]

end Zcash.Snark.ZeroKnowledge
