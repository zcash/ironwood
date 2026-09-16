import Zcash.Snark.ZeroKnowledge.ActionAuxiliaryTrace
import Zcash.Snark.ZeroKnowledge.MerkleSelectorTrace
import Zcash.Snark.ZeroKnowledge.CommitIvkSelectorTrace
import Zcash.Snark.ZeroKnowledge.NoteCommitSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActionSelectorTrace

/-!
# The complete Action source selector trace

The three synthesis stages and the post-NU6.3 cross-address region are connected
compositionally to their compact traces. The final equality opens the opaque
top-level circuit only through its recorded implementation equation. It retains
all regions, activation multiplicities, selector indices, and local rows.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action Zcash.Circuits.Trace

/-- Witness loading keeps all eight regions, including the five activation-free loads. -/
def actionWitnessActivations (config : Circuit.Config) : List (List (RegionOperation Fp)) :=
  [[], [],
    [.enableGate (Ecc.WitnessPoint.pointGate config.eccConfig.witnessPoint.qPoint
      config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0],
    [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0],
    [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0], [], [], []]

/-- The exact sequence of all 295 integrity-check regions. -/
def actionChecksActivations (generators : Specs.Sinsemilla.Generators) (config : Circuit.Config) :
    List (List (RegionOperation Fp)) :=
  (List.replicate 16 (merkleLayerActivations generators
      (config.merkle1.condSwap, config.merkle1, config.lookupConfig))).flatten ++
    (List.replicate 16 (merkleLayerActivations generators
      (config.merkle2.condSwap, config.merkle2, config.lookupConfig))).flatten ++
    [[], []] ++
    valueCommitActivations (config.eccConfig.mulFixedShort, config.eccConfig.mulFixedFull, config.eccConfig.add) ++
    nullifierActivations (config.poseidonConfig, config.addChipConfig, config.eccConfig.mulFixedBaseField, config.eccConfig.add) ++
    spendAuthorityActivations (config.eccConfig.mulFixedFull, config.eccConfig.add) ++
    commitIvkActivations generators
      { gate := config.commitIvkConfig, hashConfig := config.sinsemilla1, lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    addressIntegrityActivations (config.eccConfig.mul, config.eccConfig.witnessPoint)

/-- Action checks produce their configured trace independently of witness values, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionSynthChecks_activationTrace (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (witness : Circuit.Witnesses Fp) (config : Circuit.Config) (cells : Circuit.WitnessCells) (region : RegionIndex) :
    activationTrace ((Circuit.synthChecks generators bases witness config cells).operations region) =
      actionChecksActivations generators config := by
  rw [Circuit.synthChecks_eq]
  simp only [Circuit.synthChecksProgram, activation_trace_norm,
    actionChecksActivations, List.cons_append, List.append_assoc]

/-- The Orchard checks enable the Orchard gate at row zero, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem actionOrchardChecks_regionActivations (config : Circuit.Config)
    (cells : Circuit.WitnessCells) (checks : Circuit.CheckCells) (region : RegionIndex) :
    regionActivations ((Circuit.synthOrchardChecks config cells checks).operations region) =
      [.enableGate (Circuit.orchardGate config.qOrchard config.advices) 0] := rfl

/-- Old and new note commitments with their intervening witness and copy regions. -/
def actionNotesActivations (generators : Specs.Sinsemilla.Generators) (config : Circuit.Config) :
    List (List (RegionOperation Fp)) :=
  noteCommitActivations generators
      { gates := config.noteCommitOld, hashConfig := config.sinsemilla1, lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    [[], [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0],
      [.enableGate (Ecc.WitnessPoint.pointNonIdGate config.eccConfig.witnessPoint.qPointNonId config.eccConfig.witnessPoint.x config.eccConfig.witnessPoint.y) 0], []] ++
    noteCommitActivations generators
      { gates := config.noteCommitNew, hashConfig := config.sinsemilla2, lookupConfig := config.lookupConfig,
        mulConfig := config.eccConfig.mulFixedFull, addConfig := config.eccConfig.add } ++
    [[.enableGate (Circuit.orchardGate config.qOrchard config.advices) 0]]

/-- The note stages produce their configured traces independently of witness values, supplying
the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionSynthNotes_activationTrace (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (witness : Circuit.Witnesses Fp) (config : Circuit.Config) (cells : Circuit.WitnessCells)
    (checks : Circuit.CheckCells) (region : RegionIndex) :
    activationTrace ((Circuit.synthNotes generators bases witness config cells checks).operations region) =
      actionNotesActivations generators config := by
  rw [Circuit.synthNotes_eq]
  simp only [Circuit.synthNotesProgram, Ecc.WitnessPoint.pointNonIdFormal, activation_trace_norm,
    actionNotesActivations, List.cons_append, List.append_assoc]

/-- The base Action's complete source trace, independent of witness programs. -/
def actionBaseActivations (generators : Specs.Sinsemilla.Generators) (config : Circuit.Config) :
    List (List (RegionOperation Fp)) :=
  actionWitnessActivations config ++ actionChecksActivations generators config ++
    actionNotesActivations generators config

/-- Base Action synthesis produces the composed checks-and-notes trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionSynthesizeBase_activationTrace (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (witness : Circuit.Witnesses Fp) (config : Circuit.Config) (region : RegionIndex) :
    activationTrace ((Circuit.synthesizeBase generators bases witness config).operations region) =
      actionBaseActivations generators config := by
  simp only [Circuit.synthesizeBase, activation_trace_norm, actionBaseActivations,
    actionWitnessActivations, List.append_assoc]

/-- Calling the base Action circuit preserves its complete source trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionBaseCall_activationTrace (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (config : Circuit.Config) (input : Var unit Fp) (region : RegionIndex) :
    activationTrace (((Circuit.baseCircuit generators bases).call config input).operations region) =
      actionBaseActivations generators config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Circuit.synthesizeBase generators bases Circuit.hintWitnesses config).operations region) = _
  exact actionSynthesizeBase_activationTrace _ _ _ _ _

/-- A cross-address check enables the Orchard gate at its requested row, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionCrossAddressRow_regionActivations (config : Circuit.Config)
    (oldCell newCell : AssignedCell Fp) (row : ℕ) (region : RegionIndex) :
    regionActivations ((Circuit.synthCrossAddressRow config oldCell newCell row).operations region) =
      [.enableGate (Circuit.orchardGate config.qOrchard config.advices) row] := rfl

/-- Cross-address checks retain the four successive Orchard activations, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionCrossAddress_activationTrace (config : Circuit.Config)
    (points : Var Circuit.AddressPoints Fp) (region : RegionIndex) :
    activationTrace ((Circuit.synthCrossAddressChecks config points).operations region) =
      [gateRowRun (Circuit.orchardGate config.qOrchard config.advices) 0 4] := by
  simp only [Circuit.synthCrossAddressChecks, activation_trace_norm, gateRowRun, Nat.mul_one]

/-- All source regions of the specified post-NU6.3 Action circuit. -/
def actionSourceActivations (generators : Specs.Sinsemilla.Generators) (config : Circuit.Config) :
    List (List (RegionOperation Fp)) :=
  actionBaseActivations generators config ++ [gateRowRun (Circuit.orchardGate config.qOrchard config.advices) 0 4]

/-- All source selector labels of the specified post-NU6.3 Action circuit: the selectors read off
each region of the source activation trace. Defining it this way rather than assembling it from
per-gadget selector traces is what removes the parallel selector tower — the equation relating
the two forms is true by definition, so nothing has to prove it. -/
def actionSourceSelectorTrace (config : Circuit.Config) : List (List (ℕ × ℕ)) :=
  (actionSourceActivations Specs.Sinsemilla.orchardGenerators config).map
    fun body => body.flatMap selectorOf

/-- The complete Action source produces the composed base and cross-address traces, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem actionMainPost_activationTrace (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (config : Circuit.Config) (input : Var unit Fp) (region : RegionIndex) :
    activationTrace ((Circuit.mainPost generators bases config input).operations region) =
      actionSourceActivations generators config := by
  simp only [Circuit.mainPost, activation_trace_norm, actionSourceActivations]

/-- The actual opaque Action circuit has precisely the source-derived compact activation trace. -/
theorem actionCircuit_activationTrace_eq :
    activationTrace actionCircuit.operations =
      actionSourceActivations Specs.Sinsemilla.orchardGenerators actionConfig := by
  rw [Internal.actionCircuit_eq_impl]
  change activationTrace ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) = _
  exact actionMainPost_activationTrace _ _ _ _ _

/-- The actual opaque Action circuit has precisely the source-derived compact trace. Its selector
labels are the activation trace projected, so this follows from the activation equation and the
generic projection rather than from a selector tower of its own. -/
theorem actionCircuit_selectorTrace_eq :
    selectorTrace actionCircuit.operations = actionSourceSelectorTrace actionConfig := by
  rw [selectorTrace, trace_eq_project _ selectorOf_vanishes, actionCircuit_activationTrace_eq]
  rfl

/-- The compiler's complete activation list follows by placing the source-derived trace. -/
theorem actionCircuit_selectorActivations_eq_sourceTrace :
    actionCircuit.selectorActivations =
      placeSelectorTrace actionCircuit.regionStarts (actionSourceSelectorTrace actionConfig) := by
  rw [actionCircuit_selectorActivations_eq_trace, actionCircuit_selectorTrace_eq]

end Zcash.Snark.ZeroKnowledge
