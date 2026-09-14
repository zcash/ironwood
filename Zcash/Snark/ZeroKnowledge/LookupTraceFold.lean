import Zcash.Snark.ZeroKnowledge.LookupTracePrograms
import Clean.Halo2.Subcircuit

/-!
# Lookup traces of serial subcircuit folds

An input-independent trace for each child suffices to reduce the whole fold,
without evaluating its intermediate witnesses or region-index expressions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Serial calls preserve the exact concatenation of their per-iteration traces. -/
theorem lookupTrace_foldCall {F ConfigInput Config : Type} [FiniteField F]
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (children : ℕ → FormalCircuit F ConfigInput Config Input Output)
    (toInput : Var Output F → Var Input F) (config : Config) (initial : Var Input F)
    (count : ℕ) (region : RegionIndex) (traces : ℕ → List (List (ℕ × ℕ)))
    (htrace : ∀ index input current,
      lookupTrace (((children index).call config input).operations current) = traces index) :
    lookupTrace ((FormalCircuit.foldCall children toInput config initial count).operations region) =
      (List.ofFn fun i : Fin count => traces i.val).flatten := by
  rw [FormalCircuit.foldCall_operations]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [FormalCircuit.foldOps, lookupTrace_append, ih, htrace,
        List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rfl

end Zcash.Snark.ZeroKnowledge
