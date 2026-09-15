import Zcash.Snark.ZeroKnowledge.FixedBaseSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace

/-!
# Selector traces of short and base-field fixed-base multiplication

Both variants share the running-sum and coordinate passes. Their final regions
retain the short-sign or base-field canonicity selector at row one.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Running-sum and coordinate passes use the same selector, followed by the addition chain. -/
def runningFixedInnerSelectorTrace (config : Ecc.MulFixed.Config) (offset count : ℕ) : List (ℕ × ℕ) :=
  selectorRowRun config.runningSumConfig.qRangeCheck.index offset count ++
    selectorRowRun config.runningSumConfig.qRangeCheck.index offset count ++
    fixedWindowChainSelectorTrace config offset count

/-- Short fixed-base multiplication retains its 22-window inner trace, supplying the source metadata
for Action selector coverage. -/
@[selector_trace_norm]
theorem shortInner_regionSelectorTrace (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.Short.Config) (offset : ℕ) (magnitude : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.Short.innerRegion base config offset magnitude).operations region) =
      runningFixedInnerSelectorTrace config.superConfig offset 22 := by
  simp only [Ecc.MulFixed.Short.innerRegion, selector_trace_norm, Ecc.MulFixed.coordsGate_selector]
  rw [fixedWindowChain_regionSelectorTrace _ _ _ _ _ (fun index row =>
    fixedWindow_regionActivations base _ config.superConfig magnitude index row region)]
  simp only [runningFixedInnerSelectorTrace, List.append_assoc]

/-- The short-scalar sign stage retains the addition and signed-magnitude selectors, supplying the
source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem shortSign_regionSelectorTrace (config : Ecc.MulFixed.Short.Config)
    (accumulator window : Point (AssignedCell Fp)) (sign high : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.Short.mswRegion config accumulator window sign high).operations region) =
      [(config.superConfig.addConfig.qAdd.index, 0), (config.qMulFixedShort.index, 1)] := by
  simp only [Ecc.MulFixed.Short.mswRegion, selector_trace_norm,
    Ecc.MulFixed.Short.shortGate_selector, List.cons_append]

/-- Short fixed-base multiplication retains both its inner and sign-stage region traces, supplying
the source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem shortFixed_selectorTrace (base : Ecc.MulFixed.Short.FixedBase) (config : Ecc.MulFixed.Short.Config)
    (input : Var Ecc.MulFixed.Short.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((Ecc.MulFixed.Short.circuit base).call config input).operations region) =
      [runningFixedInnerSelectorTrace config.superConfig 0 22,
        [(config.superConfig.addConfig.qAdd.index, 0), (config.qMulFixedShort.index, 1)]] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Ecc.MulFixed.Short.synthesize base.toData config input).operations region) = _
  simp only [Ecc.MulFixed.Short.synthesize, selector_trace_norm, List.cons_append]
  rw [shortSign_regionSelectorTrace]

/-- Base-field fixed multiplication retains its 85-window inner trace, supplying the source metadata
for Action selector coverage. -/
@[selector_trace_norm]
theorem baseFieldInner_regionSelectorTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.BaseFieldElem.Config) (offset : ℕ)
    (input : Var DecomposeRunningSum.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulFixed.BaseFieldElem.inner base).call config offset input).operations region) =
      runningFixedInnerSelectorTrace config.superConfig offset 85 := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Ecc.MulFixed.BaseFieldElem.innerRegion base.toData config offset input.alpha).operations region) = _
  rw [Ecc.MulFixed.BaseFieldElem.innerRegion_operations_eq]
  simp only [selector_trace_norm, Ecc.MulFixed.coordsGate_selector]
  rw [fixedWindowChain_regionSelectorTrace _ _ _ _ _ (fun index row =>
    fixedWindow_regionActivations base.toData _ config.superConfig input.alpha index row region)]
  rfl

/-- The auxiliary thirteen-window range check retains its configured region trace, supplying the
source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem baseFieldCheck13_selectorTrace (config : LookupRangeCheck.Config 10) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    selectorTrace ((Ecc.MulFixed.BaseFieldElem.witnessCheck13 config witness).operations region) =
      [runningSelectorTrace config 0 13] := by
  simp only [Ecc.MulFixed.BaseFieldElem.witnessCheck13, selector_trace_norm]

/-- Base-field scalar canonicity retains its configured activation trace, supplying the source
metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem baseFieldCanonicity_regionSelectorTrace (config : Ecc.MulFixed.BaseFieldElem.Config)
    (alpha high prime tail mid next : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.BaseFieldElem.canonicityRegion config alpha high prime tail mid next).operations region) =
      [(config.qMulFixedBaseField.index, 1)] := rfl

/-- Base-field fixed multiplication retains its inner and canonicity region traces, supplying the
source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem baseFieldFixed_selectorTrace (base : Ecc.MulFixed.FixedBase) (config : Ecc.MulFixed.BaseFieldElem.Config)
    (input : AssignedCell Fp) (region : RegionIndex) :
    selectorTrace (((Ecc.MulFixed.BaseFieldElem.circuit base).call config input).operations region) =
      [runningFixedInnerSelectorTrace config.superConfig 0 85,
        [(config.superConfig.addConfig.qAdd.index, 0)], runningSelectorTrace config.lookupConfig 0 13,
        [(config.qMulFixedBaseField.index, 1)]] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Ecc.MulFixed.BaseFieldElem.synthesize base config input).operations region) = _
  simp only [Ecc.MulFixed.BaseFieldElem.synthesize, selector_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
