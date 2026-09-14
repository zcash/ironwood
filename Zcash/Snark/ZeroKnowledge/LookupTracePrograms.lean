import Zcash.Snark.ZeroKnowledge.LookupActivationTrace
import Clean.Halo2.FormalRegion.ToFormal

/-!
# Lookup traces through circuit composition

The normalization rules project operation streams before reducing field values or
witness programs. Child calls remain available as separate proof boundaries, and
loop rules retain their finite iteration structure.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

attribute [lookup_trace_norm]
  regionLookupTrace_nil regionLookupTrace_cons regionLookupTrace_append regionLookupTrace_flatMap
  regionLookupTrace_enableGate regionLookupTrace_enableLookup
  regionLookupTrace_assignAdvice regionLookupTrace_assignFixed
  regionLookupTrace_constrainEqual regionLookupTrace_constrainConstant
  regionLookupTrace_constrainInstance regionLookupTrace_eq_nil
  lookupTrace_nil lookupTrace_cons lookupTrace_append lookupTrace_flatMap
  lookupTrace_region lookupTrace_constrainInstance lookupTrace_loadTable
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  operations_assignRegion operations_assignAdvice operations_assignFixed
  operations_copyAdvice operations_enable operations_enableLookup
  operations_constrainEqual operations_constrainInstance operations_loadTable
  operations_constrainConstant operations_assignAdviceFromInstance
  operations_cellAt operations_cellVec
  List.append_nil List.nil_append

variable {F α β : Type}

/-- Flattening region-program lists preserves their concatenated lookup traces. -/
@[lookup_trace_norm]
theorem regionLookupTrace_flatten (bodies : List (RegionOperations F)) :
    regionLookupTrace bodies.flatten = (bodies.map regionLookupTrace).flatten := by
  simp only [List.flatten_eq_flatMap, regionLookupTrace_flatMap, List.flatMap_map]
  rfl

/-- Flattening synthesis-program lists preserves region order. -/
@[lookup_trace_norm]
theorem lookupTrace_flatten (bodies : List (Operations F)) :
    lookupTrace bodies.flatten = (bodies.map lookupTrace).flatten := by
  simp only [List.flatten_eq_flatMap, lookupTrace_flatMap, List.flatMap_map]
  rfl

variable [FiniteField F]

/-- A fixed-stride loop exposes only its per-iteration lookup traces. -/
@[lookup_trace_norm]
theorem regionLookupTrace_forRange' (offset stride count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    regionLookupTrace ((RegionCircuit.forRange' offset stride count body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionLookupTrace ((body i.val (offset + i.val * stride)).operations region)).flatten := by
  rw [RegionCircuit.forRange'_operations, regionLookupTrace_flatten, List.map_ofFn]
  rfl

/-- Variable row schedules keep the same trace projection. -/
@[lookup_trace_norm]
theorem regionLookupTrace_forRangeVar' (rows : ℕ → ℕ) (count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    regionLookupTrace ((RegionCircuit.forRangeVar' rows count body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionLookupTrace ((body i.val (rows i.val)).operations region)).flatten := by
  rw [RegionCircuit.forRangeVar'_operations, regionLookupTrace_flatten, List.map_ofFn]
  rfl

/-- Accumulator-dependent folds preserve every lookup of each actual iteration. -/
@[lookup_trace_norm]
theorem regionLookupTrace_foldRange (offset stride count : ℕ) (initial : β)
    (body : ℕ → ℕ → β → RegionCircuit F β) (region : RegionIndex) :
    regionLookupTrace ((RegionCircuit.foldRange offset stride count initial body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionLookupTrace ((body i.val (offset + i.val * stride)
          (RegionCircuit.foldAcc (fun j => offset + j * stride) initial body i.val region)).operations region)).flatten := by
  unfold RegionCircuit.foldRange RegionCircuit.foldRangeVar
  rw [RegionCircuit.foldRangeVarAux_operations, regionLookupTrace_flatten, List.map_ofFn]
  rfl

/-- Promoting a region gadget to a layouter gadget contributes exactly one region,
including when that region's lookup trace is empty. -/
@[lookup_trace_norm]
theorem lookupTrace_toFormal_call {ConfigInput Config : Type}
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F) (region : RegionIndex) :
    lookupTrace (((child.toFormal name).call config input).operations region) =
      [regionLookupTrace ((child.call config 0 input).operations region)] := by
  rw [FormalCircuit.call_operations, FormalRegionCircuit.call_operations]
  rfl

end Zcash.Snark.ZeroKnowledge
