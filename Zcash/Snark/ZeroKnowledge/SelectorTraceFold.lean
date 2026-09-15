import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Circuits.Trace.Activations
import Clean.Halo2.Subcircuit

/-!
# Selector traces of serial subcircuit folds

An input-independent trace for each child suffices to reduce the whole fold,
without evaluating its intermediate witnesses or region-index expressions.

The fold rule does not depend on what is being extracted, so this is
`Zcash/Circuits/Trace/Activations.lean`'s rule at `selectorOf`.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

/-- Serial calls preserve the exact concatenation of their per-iteration traces. -/
theorem selectorTrace_foldCall {F ConfigInput Config : Type} [FiniteField F]
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (children : ℕ → FormalCircuit F ConfigInput Config Input Output)
    (toInput : Var Output F → Var Input F) (config : Config) (initial : Var Input F)
    (count : ℕ) (region : RegionIndex) (traces : ℕ → List (List (ℕ × ℕ)))
    (htrace : ∀ index input current,
      selectorTrace (((children index).call config input).operations current) = traces index) :
    selectorTrace ((FormalCircuit.foldCall children toInput config initial count).operations region) =
      (List.ofFn fun i : Fin count => traces i.val).flatten :=
  trace_foldCall selectorOf children toInput config initial count region traces htrace

end Zcash.Snark.ZeroKnowledge
