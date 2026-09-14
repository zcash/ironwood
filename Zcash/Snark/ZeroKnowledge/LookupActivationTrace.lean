import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace

/-!
# Compact lookup-activation traces

The lookup counterpart of `SelectorActivationTrace`. A region's lookup activations
are recorded before floor-planner placement, so a circuit's lookup labels follow
from its synthesis stages one at a time, each stage's trace proved separately.

The trace keeps each lookup argument's own master selector rather than the selectors
the activation enables, so lookup membership is never inferred from a selector index
alone. Placement reuses `placeSelectorTrace`: a compact lookup trace has the same
shape as a compact selector trace.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

-- `register_simp_attr` expands to a `meta initialize` block that installs the attribute
-- handler, and initializers run when a module is loaded by an importer, not while that
-- module is itself being elaborated. So the lemmas below cannot carry this attribute here;
-- `LookupTracePrograms` applies it to them. The selector traces are split the same way.
register_simp_attr lookup_trace_norm

variable {F : Type}

/-- A region's ordered lookup-master activations, before floor-planner placement. -/
def regionLookupTrace (body : RegionOperations F) : List (ℕ × ℕ) :=
  body.flatMap fun operation => match operation with
    | .enableLookup argument _ row => [(argument.masterSelector.index, row)]
    | _ => []

/-- The ordered region lookup traces; a region with no lookups still occupies one slot. -/
def lookupTrace (operations : Operations F) : List (List (ℕ × ℕ)) :=
  operations.filterMap fun operation => match operation with
    | .region _ body => some (regionLookupTrace body)
    | _ => none

/-- The placed compact trace and the direct label projection agree on every operation
stream, so either may be used to state a circuit's lookup labels. -/
theorem operationSourceLookupLabels_eq_placeTrace (starts : List ℕ)
    (operations : Operations F) (initial : ℕ) :
    operationSourceLookupLabels (fun region => starts.getD region 0) operations initial =
      placeSelectorTrace starts (lookupTrace operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationSourceLookupLabels, lookupTrace, List.filterMap_cons,
            placeSelectorTrace, List.zipIdx_cons, List.flatMap_cons]
          rw [ih]
          congr 1
          induction body with
          | nil => rfl
          | cons op rest2 ih2 =>
              cases op <;> simp_all [regionSourceLookupLabels, regionLookupTrace]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

/-- An empty region has no lookup activations. -/
theorem regionLookupTrace_nil :
    regionLookupTrace ([] : RegionOperations F) = [] := rfl

/-- One operation contributes its lookups before the remaining trace. -/
theorem regionLookupTrace_cons (operation : RegionOperation F)
    (rest : RegionOperations F) :
    regionLookupTrace (operation :: rest) =
      regionLookupTrace [operation] ++ regionLookupTrace rest := by
  simp only [regionLookupTrace, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Region traces concatenate. -/
theorem regionLookupTrace_append (first second : RegionOperations F) :
    regionLookupTrace (first ++ second) = regionLookupTrace first ++ regionLookupTrace second := by
  simp only [regionLookupTrace, List.flatMap_append]

/-- Region traces commute with `flatMap`. -/
theorem regionLookupTrace_flatMap {α : Type} (items : List α)
    (body : α → RegionOperations F) :
    regionLookupTrace (items.flatMap body) =
      items.flatMap (fun item => regionLookupTrace (body item)) := by
  simp only [regionLookupTrace, List.flatMap_assoc]

/-- A lookup activation contributes its argument's master selector. -/
theorem regionLookupTrace_enableLookup (argument : LookupArgument F)
    (enabled : List ComplexSelector) (row : ℕ) :
    regionLookupTrace [.enableLookup argument enabled row] =
      [(argument.masterSelector.index, row)] := rfl

/-- A gate activation contributes no lookup. -/
theorem regionLookupTrace_enableGate (gate : Gate F) (row : ℕ) :
    regionLookupTrace [.enableGate gate row] = [] := rfl

/-- Synthesis traces concatenate. -/
theorem lookupTrace_append (first second : Operations F) :
    lookupTrace (first ++ second) = lookupTrace first ++ lookupTrace second := by
  simp only [lookupTrace, List.filterMap_append]

/-- Synthesis traces commute with `flatMap`. -/
theorem lookupTrace_flatMap {α : Type} (items : List α)
    (body : α → Operations F) :
    lookupTrace (items.flatMap body) = items.flatMap (fun item => lookupTrace (body item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, lookupTrace_append, ih]

/-- A region contributes exactly its own lookup trace, even when empty. -/
theorem lookupTrace_region (name : String) (body : RegionOperations F) :
    lookupTrace [.region name body] = [regionLookupTrace body] := rfl

end Zcash.Snark.ZeroKnowledge
