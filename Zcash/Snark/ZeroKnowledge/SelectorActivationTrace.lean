import Clean.Halo2.Formal.Call
import Clean.Halo2.FormalRegion.Call
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Zcash.Circuits.Trace.Activations

/-!
# Compositional selector-activation traces

These projections discard witness computations and keep every selector activation,
its local row, and its region's position in the synthesis stream. Empty regions
remain in the trace because they still advance the floor planner's region index.
`activations_eq_placeSelectorTrace` connects this smaller representation to the
compiler's actual activation walk, for any supplied placement.

The trace is the shared extractor form of `Zcash/Circuits/Trace/Activations.lean` at
`selectorOf`, so the rules below that hold for any extractor are that module's rules applied
here. What this module adds is the selector vocabulary, the placement, and the walk.
-/

register_simp_attr selector_trace_norm

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- A region's ordered selector activations, before floor-planner placement. -/
def regionSelectorTrace (body : RegionOperations F) : List (ℕ × ℕ) :=
  body.flatMap selectorOf

/-- The ordered region traces; even a region with no selectors occupies one slot. -/
def selectorTrace (operations : Operations F) : List (List (ℕ × ℕ)) :=
  trace selectorOf operations

/-- Apply the compiler's region starts to a compact selector trace. -/
def placeSelectorTrace (starts : List ℕ) (trace : List (List (ℕ × ℕ)))
    (initial : ℕ := 0) : List (ℕ × ℕ) :=
  (trace.zipIdx initial).flatMap fun (body, index) =>
    body.map fun (selector, row) => (selector, starts.getD index 0 + row)

/-- One selector activation at each successive row of a compact trace. -/
def selectorRowRun (selector offset count : ℕ) : List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count => [(selector, offset + i.val)]).flatten

/-- An empty region has no activations, supplying the base case for compositional trace proofs. -/
theorem regionSelectorTrace_nil : regionSelectorTrace ([] : RegionOperations F) = [] := rfl

/-- One operation contributes its selectors before the remaining trace, enabling instruction-wise
trace reduction. -/
theorem regionSelectorTrace_cons (operation : RegionOperation F) (rest : RegionOperations F) :
    regionSelectorTrace (operation :: rest) =
      (match operation with
        | .enableGate gate row => [(gate.selector.index, row)]
        | .enableLookup _ enabled row => enabled.map fun selector => (selector.index, row)
        | _ => []) ++ regionSelectorTrace rest := rfl

/-- Concatenating region programs concatenates their activations, allowing separate stages to be
certified independently. -/
theorem regionSelectorTrace_append (left right : RegionOperations F) :
    regionSelectorTrace (left ++ right) = regionSelectorTrace left ++ regionSelectorTrace right := by
  simp only [regionSelectorTrace, List.flatMap_append]

/-- Repeated region programs contribute their traces in source order, enabling loop certificates
without expanding witnesses. -/
theorem regionSelectorTrace_flatMap {α : Type} (items : List α)
    (body : α → RegionOperations F) :
    regionSelectorTrace (items.flatMap body) = items.flatMap (fun item => regionSelectorTrace (body item)) := by
  simp only [regionSelectorTrace, List.flatMap_assoc]

/-- Enabling a gate records its selector and row, anchoring the trace to the compiler instruction. -/
theorem regionSelectorTrace_enableGate (gate : Gate F) (row : ℕ) :
    regionSelectorTrace [.enableGate gate row] = [(gate.selector.index, row)] := rfl

/-- A lookup records every enabled selector at its row, preserving shared activation information for
coverage checks. -/
theorem regionSelectorTrace_enableLookup (argument : LookupArgument F)
    (enabled : List Selector) (row : ℕ) :
    regionSelectorTrace [.enableLookup argument enabled row] =
      enabled.map (fun selector => (selector.index, row)) := by
  simp only [regionSelectorTrace, selectorOf, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- Advice assignment contributes no selector activation, allowing witness computations to be
removed from the trace. -/
theorem regionSelectorTrace_assignAdvice (column : Column .advice) (witness : WitgenIR F 1) (row : ℕ) :
    regionSelectorTrace [.assignAdvice column row witness] = [] := rfl

/-- Fixed assignment contributes no selector activation, separating fixed values from activation
metadata. -/
theorem regionSelectorTrace_assignFixed (column : Column .fixed) (row : ℕ) (value : F) :
    regionSelectorTrace [.assignFixed column row value] = [] := rfl

/-- A copy constraint contributes no selector activation, keeping copy equations separate from gate
coverage. -/
theorem regionSelectorTrace_constrainEqual (left right : Cell) :
    regionSelectorTrace [.constrainEqual left right] (F := F) = [] := rfl

/-- A constant constraint contributes no selector activation, allowing trace reduction to skip it. -/
theorem regionSelectorTrace_constrainConstant (cell : Cell) (value : F) :
    regionSelectorTrace [.constrainConstant cell value] = [] := rfl

/-- An instance constraint contributes no region selector activation, keeping public-input wiring
separate from gate coverage. -/
theorem regionSelectorTrace_constrainInstance (cell : Cell) (column : Column .instance) (row : ℕ) :
    regionSelectorTrace [.constrainInstance cell column row] (F := F) = [] := rfl

/-- An empty synthesis stream has no regions, supplying the base case for source-trace composition. -/
theorem selectorTrace_nil : selectorTrace ([] : Operations F) = [] := rfl

/-- Only region operations add a trace slot, preserving the compiler region index during
instruction-wise reduction. -/
theorem selectorTrace_cons (operation : Operation F) (rest : Operations F) :
    selectorTrace (operation :: rest) = match operation with
      | .region _ body => regionSelectorTrace body :: selectorTrace rest
      | _ => selectorTrace rest :=
  trace_cons selectorOf operation rest

/-- Sequential synthesis stages concatenate their region traces, allowing stage certificates to
compose. -/
theorem selectorTrace_append (left right : Operations F) :
    selectorTrace (left ++ right) = selectorTrace left ++ selectorTrace right :=
  trace_append selectorOf left right

/-- A synthesis loop retains each iteration's region traces in order, enabling compositional loop
certificates. -/
theorem selectorTrace_flatMap {α : Type} (items : List α) (body : α → Operations F) :
    selectorTrace (items.flatMap body) = items.flatMap (fun item => selectorTrace (body item)) :=
  trace_flatMap selectorOf items body

/-- A region occupies one trace slot even when it has no activations, preserving floor-planner
indices. -/
theorem selectorTrace_region (name : String) (body : RegionOperations F) :
    selectorTrace [.region name body] = [regionSelectorTrace body] := rfl

/-- A top-level instance constraint adds no region slot, preserving placement indices when it is
skipped. -/
theorem selectorTrace_constrainInstance (cell : Cell) (column : Column .instance) (row : ℕ) :
    selectorTrace [.constrainInstance cell column row] (F := F) = [] := rfl

/-- Loading a lookup table adds no region slot, preserving placement indices independently of table
contents. -/
theorem selectorTrace_loadTable (table : TableColumn) (values : List F) :
    selectorTrace [.loadTable table values] = [] := rfl

/-- Compact trace placement is exactly the compiler's activation walk, including
region-index advancement through empty traces and ignored non-region operations. -/
theorem activations_eq_placeSelectorTrace (starts : List ℕ) (operations : Operations F) (initial : ℕ) :
    activations starts (indexedRegions operations initial).1 =
      placeSelectorTrace starts (selectorTrace operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, activations, List.flatMap_cons,
            selectorTrace, trace, List.filterMap_cons, placeSelectorTrace, List.zipIdx_cons,
            List.map_flatMap] at ih ⊢
          rw [ih]
          congr 1
          apply List.flatMap_congr
          intro operation hoperation
          cases operation <;> simp [selectorOf]
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
