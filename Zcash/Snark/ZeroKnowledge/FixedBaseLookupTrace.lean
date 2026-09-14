import Zcash.Snark.ZeroKnowledge.LookupRangeCheckTrace
import Zcash.Circuits.Ecc.MulFixed.BaseFieldElem
import Zcash.Circuits.Ecc.MulFixed.FullWidth
import Zcash.Circuits.Ecc.MulFixed.Short

/-!
# Lookup traces of fixed-base multiplication

No variant's window passes enable a lookup. Full-width and short multiplication
therefore contribute none at all; the base-field variant's only lookups come from
the auxiliary thirteen-window range check on its scalar.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Both regions of full-width blinding multiplication are lookup-free. The region-level
`regionLookupTrace_eq_nil` does not reach this: a circuit's trace has one entry per region, so
crossing a multi-region call boundary needs the region count as well as the activation count.
Stated here, beside its only consumer. -/
@[lookup_trace_norm]
theorem fullWidth_lookupTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config) (input : Var UnconstrainedNat Fp)
    (region : RegionIndex) :
    lookupTrace (((Ecc.MulFixed.FullWidth.circuit base).call config input).operations region)
      = [[], []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.MulFixed.FullWidth.synthesize base.toData config
    (Ecc.MulFixed.FullWidth.scalarWindows input)).operations region) = _
  simp only [Ecc.MulFixed.FullWidth.synthesize, lookup_trace_norm, synthesis_summary_norm,
    List.cons_append]

/-- The short-scalar sign region enables no lookup. -/
@[lookup_trace_norm]
theorem shortSign_regionLookupTrace (config : Ecc.MulFixed.Short.Config)
    (accumulator window : Point (AssignedCell Fp)) (sign high : AssignedCell Fp)
    (region : RegionIndex) :
    regionLookupTrace ((Ecc.MulFixed.Short.mswRegion config accumulator window sign
      high).operations region) = [] := by
  simp only [lookup_trace_norm, synthesis_summary_norm]

/-- Short fixed-base multiplication enables no lookup, in either of its two regions. -/
@[lookup_trace_norm]
theorem shortFixed_lookupTrace (base : Ecc.MulFixed.Short.FixedBase)
    (config : Ecc.MulFixed.Short.Config)
    (input : Var Ecc.MulFixed.Short.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((Ecc.MulFixed.Short.circuit base).call config input).operations region)
      = [[], []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.MulFixed.Short.synthesize base.toData config input).operations
    region) = _
  simp only [Ecc.MulFixed.Short.synthesize, lookup_trace_norm, synthesis_summary_norm,
    List.cons_append]
  rw [shortSign_regionLookupTrace]

/-- The auxiliary thirteen-window range check contributes its running lookups. -/
@[lookup_trace_norm]
theorem baseFieldCheck13_lookupTrace (config : LookupRangeCheck.Config 10)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    lookupTrace ((Ecc.MulFixed.BaseFieldElem.witnessCheck13 config witness).operations region) =
      [runningLookupTrace config 0 13] := by
  simp only [Ecc.MulFixed.BaseFieldElem.witnessCheck13, lookup_trace_norm]

/-- Base-field fixed multiplication's four regions: the window pass, its closing addition,
the thirteen-window range check, and the canonicity region. Only the range check looks up. -/
@[lookup_trace_norm]
theorem baseFieldFixed_lookupTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.BaseFieldElem.Config)
    (input : AssignedCell Fp) (region : RegionIndex) :
    lookupTrace (((Ecc.MulFixed.BaseFieldElem.circuit base).call config input).operations region) =
      [[], [], runningLookupTrace config.lookupConfig 0 13, []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.MulFixed.BaseFieldElem.synthesize base config input).operations
    region) = _
  simp only [Ecc.MulFixed.BaseFieldElem.synthesize, lookup_trace_norm, synthesis_summary_norm,
    List.cons_append]

end Zcash.Snark.ZeroKnowledge
