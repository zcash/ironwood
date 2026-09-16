import Zcash.Snark.ZeroKnowledge.ActionWitnessSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActivationTrace

/-!
# Activation traces shared by fixed-base multiplication

The trace separates scalar decomposition, fixed-column loading, and the addition
chain. Field-valued fixed parameters and window witnesses are discarded only by
the proved operation projection; activations are retained in full.

Each gadget has one lemma, stated on activations. Its selector trace follows by projection, and
so would a trace of any other label shape, so neither needs a lemma of its own.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- Incomplete addition enables its gate at the requested row, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem incompleteAdd_regionActivations (config : Ecc.AddIncomplete.Config) (offset : ℕ)
    (input : Var Ecc.AddIncomplete.Inputs Fp) (region : RegionIndex) :
    regionActivations ((Ecc.AddIncomplete.add.call config offset input).operations region) =
      [.enableGate (Ecc.AddIncomplete.gate config.qAddIncomplete config.xP config.yP
        config.xQR config.yQR) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Running-sum decomposition enables its range-check gate on every requested row, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem decomposeEnable_regionActivations (width : ℕ) (config : DecomposeRunningSum.Config)
    (offset count : ℕ) (region : RegionIndex) :
    regionActivations ((DecomposeRunningSum.enableLoop width config offset count).operations region) =
      gateRowRun (DecomposeRunningSum.rangeCheckGate width config) offset count := by
  simp only [DecomposeRunningSum.enableLoop, activation_trace_norm, gateRowRun, Nat.mul_one]

/-- Assigning running-sum witnesses adds no activation, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem decomposeAssign_regionActivations (width : ℕ) (config : DecomposeRunningSum.Config)
    (input : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionActivations ((DecomposeRunningSum.assignLoop width config input offset count).operations region) = [] := by
  simp only [DecomposeRunningSum.assignLoop, activation_trace_norm, List.ofFn_const,
    List.flatten_replicate_nil]

/-- Copy-and-decompose uses the same successive range-check activations, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem copyDecompose_regionActivations (width count : ℕ) (config : DecomposeRunningSum.Config)
    (offset : ℕ) (input : Var DecomposeRunningSum.Inputs Fp) (region : RegionIndex) :
    regionActivations (((DecomposeRunningSum.copyDecompose width count).call config offset input).operations region) =
      gateRowRun (DecomposeRunningSum.rangeCheckGate width config) offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((DecomposeRunningSum.body width count config offset input).operations region) = _
  simp only [DecomposeRunningSum.body, activation_trace_norm]

/-- One fixed-base constant window enables the supplied gate at its row, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem fixedConstantsWindow_regionActivations (toggle : Gate Fp)
    (base : Ecc.MulFixed.FixedBaseData) (config : Ecc.MulFixed.Config) (index row : ℕ)
    (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.fixedConstantsWindow toggle base config index row).operations region) =
      [.enableGate toggle row] := rfl

/-- The fixed-base constant loop enables the supplied gate on successive rows, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem fixedConstantsLoop_regionActivations (toggle : Gate Fp)
    (base : Ecc.MulFixed.FixedBaseData) (config : Ecc.MulFixed.Config) (offset count : ℕ)
    (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.fixedConstantsLoop toggle base config offset count).operations region) =
      gateRowRun toggle offset count := by
  simp only [Ecc.MulFixed.fixedConstantsLoop, activation_trace_norm,
    fixedConstantsWindow_regionActivations, gateRowRun, Nat.mul_one]

/-- Computing a fixed-base witness window adds no activation, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem fixedWindow_regionActivations (base : Ecc.MulFixed.FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (config : Ecc.MulFixed.Config) (input : AssignedCell Fp)
    (index row : ℕ) (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.processWindow base table config input index row).operations region) = [] := rfl

/-- The gate of the incomplete addition that the chain repeats. -/
def fixedChainGate (config : Ecc.MulFixed.Config) : Gate Fp :=
  Ecc.AddIncomplete.gate config.addIncompleteConfig.qAddIncomplete config.addIncompleteConfig.xP
    config.addIncompleteConfig.yP config.addIncompleteConfig.xQR config.addIncompleteConfig.yQR

/-- The first incomplete addition precedes the remaining middle-window additions. -/
def fixedWindowChainActivations (config : Ecc.MulFixed.Config) (offset count : ℕ) :
    List (RegionOperation Fp) :=
  [.enableGate (fixedChainGate config) (offset + 1)] ++
    gateRowRun (fixedChainGate config) (offset + 2) (count - 3)

/-- Any activation-free window witness routine gives the same shared addition trace. -/
theorem fixedWindowChain_regionActivations (config : Ecc.MulFixed.Config)
    (process : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp))) (offset count : ℕ)
    (region : RegionIndex)
    (hprocess : ∀ index row, regionActivations ((process index row).operations region) = []) :
    regionActivations ((Ecc.MulFixed.windowChain config process offset count).operations region) =
      fixedWindowChainActivations config offset count := by
  simp only [Ecc.MulFixed.windowChain, Ecc.MulFixed.windowChainStep, activation_trace_norm,
    hprocess, fixedWindowChainActivations, fixedChainGate, gateRowRun, Nat.mul_one]

/-- Computing a hinted full-width window adds no activation, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem fullWidthWindow_regionActivations (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (index row : ℕ) (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.FullWidth.processWindowH base config windows index row).operations region) = [] := rfl

/-- Full-width scalar witnessing enables its gate across all 85 windows, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem fullWidthScalar_regionActivations (config : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.FullWidth.witnessScalarLoop config windows offset).operations region) =
      gateRowRun (Ecc.MulFixed.FullWidth.fullWidthGate config) offset 85 := by
  simp only [Ecc.MulFixed.FullWidth.witnessScalarLoop, activation_trace_norm, gateRowRun,
    Nat.mul_one, List.ofFn_const, List.flatten_replicate_nil, List.append_nil]

/-- The scalar and fixed-constant passes each enable the full-width gate. -/
def fullWidthInnerActivations (config : Ecc.MulFixed.FullWidth.Config) (offset : ℕ) :
    List (RegionOperation Fp) :=
  gateRowRun (Ecc.MulFixed.FullWidth.fullWidthGate config) offset 85 ++
    gateRowRun (Ecc.MulFixed.FullWidth.fullWidthGate config) offset 85 ++
    fixedWindowChainActivations config.superConfig offset 85

/-- The full-width inner region produces its configured activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem fullWidthInner_regionActivations (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.FullWidth.Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (region : RegionIndex) :
    regionActivations ((Ecc.MulFixed.FullWidth.innerRegion base config offset windows).operations region) =
      fullWidthInnerActivations config offset := by
  rw [Ecc.MulFixed.FullWidth.innerRegion_operations_eq]
  simp only [activation_trace_norm]
  rw [fixedWindowChain_regionActivations _ _ _ _ _ (fun index row =>
    fullWidthWindow_regionActivations base config windows index row region)]
  rfl

/-- Both regions of full-width multiplication, in their synthesis order. -/
@[activation_trace_norm]
theorem fullWidth_activationTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config) (input : Var UnconstrainedNat Fp)
    (region : RegionIndex) :
    activationTrace (((Ecc.MulFixed.FullWidth.circuit base).call config input).operations region) =
      [fullWidthInnerActivations config 0,
        [.enableGate (completeAddGate config.superConfig.addConfig) 0]] := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Ecc.MulFixed.FullWidth.synthesize base.toData config
    (Ecc.MulFixed.FullWidth.scalarWindows input)).operations region) = _
  simp only [Ecc.MulFixed.FullWidth.synthesize, activation_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
