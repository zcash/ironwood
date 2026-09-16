import Zcash.Circuits.Trace.Activations

/-!
# Activation traces through circuit composition

The `activation_trace_norm` simp set, which reduces a gadget's operation stream to its compact
activation list. The rules project the stream before reducing field values or witness programs,
child calls stay available as separate proof boundaries, and loop rules keep their finite
iteration structure.

`Activations.lean` registers the attribute and this module applies it, because an attribute
cannot be applied in the module that registers it.

The rules are the ones stated for any extractor, applied at `activationOf`; the base cases are
`List.flatMap`'s own and the equations of `activationOf`.
-/

namespace Zcash.Circuits.Trace

open Halo2

attribute [activation_trace_norm]
  -- What one operation contributes, and the core list laws.
  activationOf
  List.flatMap_nil List.flatMap_cons List.flatMap_append List.flatMap_assoc
  List.append_nil List.nil_append
  -- This module's rules, stated for any extractor.
  flatten_flatMap
  trace_nil trace_cons trace_append trace_flatMap trace_flatten
  trace_region trace_constrainInstance trace_loadTable
  flatMap_forRange' flatMap_forRangeVar' flatMap_foldRange
  trace_toFormal_call
  -- The operation streams of Clean's circuit combinators.
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  operations_assignRegion operations_assignAdvice operations_assignFixed
  operations_copyAdvice operations_enable operations_enableLookup
  operations_constrainEqual operations_constrainInstance operations_loadTable
  operations_constrainConstant operations_assignAdviceFromInstance
  operations_cellAt operations_cellVec

end Zcash.Circuits.Trace
