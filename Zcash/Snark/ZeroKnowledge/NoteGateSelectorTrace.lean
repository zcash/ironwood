import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Snark.ZeroKnowledge.ActivationTrace
import Zcash.Circuits.NoteCommit.Decompose
import Zcash.Circuits.NoteCommit.Canonicity

/-!
# Source selector traces of the note-commitment gates

Every decomposition and canonicity bundle enables its own selector once at the
supplied local row. These equations project the actual synthesis programs for
arbitrary copied cells and witness programs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The source activation of the `DecomposeB` gate bundle. -/
@[activation_trace_norm]
theorem noteDecomposeB_regionActivations (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeB.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeB.Inputs Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.DecomposeB.bundle first).call config offset input).operations region) =
      [.enableGate (NoteCommit.DecomposeB.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteDecomposeB_regionSelectorTrace (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeB.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeB.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.DecomposeB.bundle first).call config offset input).operations region) =
      [(config.qNotecommitB.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteDecomposeB_regionActivations]
  rfl

/-- The source activation of the `DecomposeD` gate bundle. -/
@[activation_trace_norm]
theorem noteDecomposeD_regionActivations (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeD.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeD.Inputs Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.DecomposeD.bundle first).call config offset input).operations region) =
      [.enableGate (NoteCommit.DecomposeD.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteDecomposeD_regionSelectorTrace (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeD.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeD.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.DecomposeD.bundle first).call config offset input).operations region) =
      [(config.qNotecommitD.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteDecomposeD_regionActivations]
  rfl

/-- The source activation of the `DecomposeE` gate bundle. -/
@[activation_trace_norm]
theorem noteDecomposeE_regionActivations (config : NoteCommit.DecomposeE.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeE.Inputs Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.DecomposeE.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.DecomposeE.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteDecomposeE_regionSelectorTrace (config : NoteCommit.DecomposeE.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeE.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.DecomposeE.bundle).call config offset input).operations region) =
      [(config.qNotecommitE.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteDecomposeE_regionActivations]
  rfl

/-- The source activation of the `DecomposeG` gate bundle. -/
@[activation_trace_norm]
theorem noteDecomposeG_regionActivations (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeG.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeG.Inputs Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.DecomposeG.bundle first).call config offset input).operations region) =
      [.enableGate (NoteCommit.DecomposeG.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteDecomposeG_regionSelectorTrace (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeG.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeG.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.DecomposeG.bundle first).call config offset input).operations region) =
      [(config.qNotecommitG.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteDecomposeG_regionActivations]
  rfl

/-- The source activation of the `DecomposeH` gate bundle. -/
@[activation_trace_norm]
theorem noteDecomposeH_regionActivations (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeH.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeH.Inputs Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.DecomposeH.bundle first).call config offset input).operations region) =
      [.enableGate (NoteCommit.DecomposeH.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteDecomposeH_regionSelectorTrace (first : WitgenIR Fp 1) (config : NoteCommit.DecomposeH.Config)
    (offset : ℕ) (input : Var NoteCommit.DecomposeH.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.DecomposeH.bundle first).call config offset input).operations region) =
      [(config.qNotecommitH.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteDecomposeH_regionActivations]
  rfl

/-- The source activation of the `GdCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem noteGdCanonicity_regionActivations (config : NoteCommit.GdCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.GdCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.GdCanonicity.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.GdCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteGdCanonicity_regionSelectorTrace (config : NoteCommit.GdCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.GdCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.GdCanonicity.bundle).call config offset input).operations region) =
      [(config.qNotecommitGd.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteGdCanonicity_regionActivations]
  rfl

/-- The source activation of the `PkdCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem notePkdCanonicity_regionActivations (config : NoteCommit.PkdCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.PkdCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.PkdCanonicity.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.PkdCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem notePkdCanonicity_regionSelectorTrace (config : NoteCommit.PkdCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.PkdCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.PkdCanonicity.bundle).call config offset input).operations region) =
      [(config.qNotecommitPkd.index, offset)] := by
  rw [regionSelectorTrace_eq_project, notePkdCanonicity_regionActivations]
  rfl

/-- The source activation of the `ValueCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem noteValueCanonicity_regionActivations (config : NoteCommit.ValueCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.ValueCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.ValueCanonicity.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.ValueCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteValueCanonicity_regionSelectorTrace (config : NoteCommit.ValueCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.ValueCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.ValueCanonicity.bundle).call config offset input).operations region) =
      [(config.qNotecommitValue.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteValueCanonicity_regionActivations]
  rfl

/-- The source activation of the `RhoCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem noteRhoCanonicity_regionActivations (config : NoteCommit.RhoCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.RhoCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.RhoCanonicity.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.RhoCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteRhoCanonicity_regionSelectorTrace (config : NoteCommit.RhoCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.RhoCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.RhoCanonicity.bundle).call config offset input).operations region) =
      [(config.qNotecommitRho.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteRhoCanonicity_regionActivations]
  rfl

/-- The source activation of the `PsiCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem notePsiCanonicity_regionActivations (config : NoteCommit.PsiCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.PsiCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.PsiCanonicity.bundle).call config offset input).operations region) =
      [.enableGate (NoteCommit.PsiCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem notePsiCanonicity_regionSelectorTrace (config : NoteCommit.PsiCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.PsiCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.PsiCanonicity.bundle).call config offset input).operations region) =
      [(config.qNotecommitPsi.index, offset)] := by
  rw [regionSelectorTrace_eq_project, notePsiCanonicity_regionActivations]
  rfl

/-- The source activation of the `YCanonicity` gate bundle. -/
@[activation_trace_norm]
theorem noteYCanonicity_regionActivations (first second : WitgenIR Fp 1) (config : NoteCommit.YCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.YCanonicity.Row Fp) (region : RegionIndex) :
    regionActivations (((NoteCommit.YCanonicity.bundle first second).call config offset input).operations region) =
      [.enableGate (NoteCommit.YCanonicity.gate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem noteYCanonicity_regionSelectorTrace (first second : WitgenIR Fp 1) (config : NoteCommit.YCanonicity.Config)
    (offset : ℕ) (input : Var NoteCommit.YCanonicity.Row Fp) (region : RegionIndex) :
    regionSelectorTrace (((NoteCommit.YCanonicity.bundle first second).call config offset input).operations region) =
      [(config.qYCanon.index, offset)] := by
  rw [regionSelectorTrace_eq_project, noteYCanonicity_regionActivations]
  rfl

end Zcash.Snark.ZeroKnowledge
