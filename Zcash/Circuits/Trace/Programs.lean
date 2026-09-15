import Zcash.Circuits.Trace.Activations

/-!
# Activation traces through circuit composition

The `activation_trace_norm` simp set, which reduces a gadget's operation stream to its compact
activation list. The rules project the stream before reducing field values or witness programs,
child calls stay available as separate proof boundaries, and loop rules keep their finite
iteration structure.

`Activations.lean` registers the attribute and this module applies it, because an attribute
cannot be applied in the module that registers it.

A gadget proof states its hypotheses on `regionActivations`, so the set rewrites at that name
rather than unfolding it to a `flatMap`. Unfolding would leave those hypotheses unable to match,
and simp cannot fold a definition back up by name.
-/

namespace Zcash.Circuits.Trace

open Halo2

attribute [activation_trace_norm]
  regionActivations_nil regionActivations_cons regionActivations_append
  regionActivations_flatMap regionActivations_flatten
  regionActivations_enableGate regionActivations_enableLookup
  regionActivations_assignAdvice regionActivations_assignFixed
  regionActivations_constrainEqual regionActivations_constrainConstant
  regionActivations_constrainInstance
  activationTrace_nil activationTrace_cons activationTrace_append activationTrace_flatMap
  activationTrace_region activationTrace_constrainInstance activationTrace_loadTable
  activationTrace_flatten
  regionActivations_forRange' regionActivations_forRangeVar' regionActivations_foldRange
  activationTrace_toFormal_call
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  operations_assignRegion operations_assignAdvice operations_assignFixed
  operations_copyAdvice operations_enable operations_enableLookup
  operations_constrainEqual operations_constrainInstance operations_loadTable
  operations_constrainConstant operations_assignAdviceFromInstance
  operations_cellAt operations_cellVec
  List.append_nil List.nil_append

end Zcash.Circuits.Trace
