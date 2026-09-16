import Clean.Halo2.FormalRegion.Call
import Clean.Halo2.FormalRegion.ToFormal
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Clean.Halo2.Subcircuit

/-!
# Compact activation traces

A region's activations, kept as the operations themselves rather than projected to labels.
Selector labels, gate labels and lookup labels are all projections of this one list, so a gadget
needs one trace lemma rather than one per label shape.

This is pure Halo2 compiler semantics: it does not mention any ironwood vocabulary, and is written
to be lifted into Clean, where the surrounding machinery already lives. Clean already provides the
placed selector form (`FloorPlanner.activations`), the region indexing (`indexedRegions`), and the
synthesis summaries with `combine`/`empty` and their associativity and unit laws. What is added
here is the pre-placement compact form, the label shapes as projections of it, the composition
rules stated generically in the extractor, and placement generic in the label payload.

## The structure this rests on

`List α` is the free monoid, and `List.flatMap f` is the homomorphism extending an extractor
`f : α → List β`. Every trace function here is exactly such an extension, which is why the base
rules — empty, singleton, concatenation, flattening — are not restated per trace: they are the
core `List.flatMap` lemmas, applying directly.

Two consequences do the work below:

* `List.flatMap_assoc` is the list monad's associativity law, which is what makes
  `project_of_vanishing` available for every label shape at once rather than one shape at a
  time. Its side condition is the honest content — a projection must vanish off activations to
  factor through them.
* A label is a payload paired with a row, and placement moves only the row. So one placement
  function serves every label shape, instead of one per shape.

In the vocabulary of Gibbons and Oliveira's *The Essence of the Iterator Pattern*, each
projection is a traversal in a monoidal applicative: at the free monoid it collects labels, at
the additive naturals it counts, at `max` it measures extents — which is what the synthesis
summary's fields are. `project_of_vanishing` is an instance of that paper's naturality law
rather than a fact peculiar to circuits.
-/

-- `register_simp_attr` expands to a `meta initialize` block, and initializers run when a module
-- is loaded by an importer rather than while that module is itself being elaborated. So the
-- rules below cannot carry this attribute here; `Trace/Programs.lean` applies it to them.
register_simp_attr activation_trace_norm

namespace Zcash.Circuits.Trace

open Halo2

variable {F α β γ : Type}

/-! ## Activations -/

/-- The activation operations one operation contributes: itself, if it is one. -/
def activationOf : RegionOperation F → List (RegionOperation F)
  | operation@(.enableGate _ _) => [operation]
  | operation@(.enableLookup _ _ _) => [operation]
  | _ => []

/-- The ordered region traces of an extractor; a region contributes a slot even where it
extracts nothing. -/
def trace (f : RegionOperation F → List β) (operations : Operations F) : List (List β) :=
  operations.filterMap fun operation => match operation with
    | .region _ body => some (body.flatMap f)
    | _ => none

/-! ## Projections

Each label shape is an extractor on a single operation, and the trace of that shape is its free
extension. The base rules come from `List.flatMap`.
-/

/-- The selector labels one operation contributes. A gate contributes its own selector; a lookup
contributes every selector the activation enables. -/
def selectorOf : RegionOperation F → List (ℕ × ℕ)
  | .enableGate gate row => [(gate.selector.index, row)]
  | .enableLookup _ enabled row => enabled.map fun selector => (selector.index, row)
  | _ => []

/-- The gate labels one operation contributes, retaining the gate's name. A lookup does not
contribute any, since the selectors it enables are not gate activations. -/
def gateOf : RegionOperation F → List ((ℕ × String) × ℕ)
  | .enableGate gate row => [((gate.selector.index, gate.name), row)]
  | _ => []

/-- The lookup labels one operation contributes, retaining the argument's master selector rather
than the selectors the activation enables. -/
def lookupOf : RegionOperation F → List (ℕ × ℕ)
  | .enableLookup argument _ row => [(argument.masterSelector.index, row)]
  | _ => []

/-- A projection that vanishes off the kept items factors through them: keeping first and then
projecting gives the same result as projecting directly. The vanishing hypothesis is what the
statement turns on — without it the projection would also read the items `keep` discards. -/
theorem project_of_vanishing (keep : α → List α) (f : α → List β)
    (vanishes : ∀ item, (keep item).flatMap f = f item) (items : List α) :
    (items.flatMap keep).flatMap f = items.flatMap f := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun item _ => vanishes item

/-- A whole synthesis trace of labels is the activation trace with the labels read off each
region. This is what lets a circuit's label trace be *defined* as a projection, so the equation
relating the two needs no proof of its own. -/
theorem trace_eq_project (f : RegionOperation F → List β)
    (vanishes : ∀ operation, (activationOf operation).flatMap f = f operation)
    (operations : Operations F) :
    trace f operations = (trace activationOf operations).map fun body => body.flatMap f := by
  simp only [trace, List.map_filterMap]
  congr 1
  funext operation
  cases operation <;>
    simp only [Option.map_some, Option.map_none, project_of_vanishing _ _ vanishes]

/-- Selector labels read the activations and nothing else. -/
theorem selectorOf_vanishes (operation : RegionOperation F) :
    (activationOf operation).flatMap selectorOf = selectorOf operation := by
  cases operation <;> simp [activationOf, selectorOf]

/-- Gate labels read the activations and nothing else. -/
theorem gateOf_vanishes (operation : RegionOperation F) :
    (activationOf operation).flatMap gateOf = gateOf operation := by
  cases operation <;> simp [activationOf, gateOf]

/-- Lookup labels read the activations and nothing else. -/
theorem lookupOf_vanishes (operation : RegionOperation F) :
    (activationOf operation).flatMap lookupOf = lookupOf operation := by
  cases operation <;> simp [activationOf, lookupOf]

/-- One activation of the same gate at each of `count` successive rows from `offset`. Enabling a
gate across a row range is what most loop gadgets do, so their traces are stated with this. -/
def gateRowRun (gate : Gate F) (offset count : ℕ) : List (RegionOperation F) :=
  (List.ofFn fun i : Fin count => [RegionOperation.enableGate gate (offset + i.val)]).flatten

/-! ## Placement

A label is a payload paired with a row, and placement adds a region's start to the row, whatever
the payload. So one placement function serves every label shape.
-/

/-- Apply the compiler's region starts to a compact trace of labels of any payload. -/
def placeLabels (starts : List ℕ) (trace : List (List (α × ℕ))) (initial : ℕ := 0) :
    List (α × ℕ) :=
  (trace.zipIdx initial).flatMap fun (body, index) =>
    body.map fun label => (label.1, starts.getD index 0 + label.2)

/-! ## Composition

Every trace here is `List.flatMap` of an extractor, so the rules for composing traces — through
concatenation, flattening, the loop combinators, and a child call — do not depend on which
extractor is in play. Stating them once, generically, is what lets one set of rules serve the
activations, all three label shapes, and any shape added later.
-/

/-- Projecting a flattened list is projecting each piece and then flattening. -/
theorem flatten_flatMap (bodies : List (List α)) (f : α → List β) :
    bodies.flatten.flatMap f = (bodies.map fun body => body.flatMap f).flatten := by
  induction bodies with
  | nil => rfl
  | cons body rest ih => simp only [List.flatten_cons, List.flatMap_append, ih, List.map_cons]

/-- An empty synthesis stream has no regions. -/
theorem trace_nil (f : RegionOperation F → List β) : trace f ([] : Operations F) = [] := rfl

/-- Only a region operation adds a trace slot, which preserves the compiler's region index. -/
theorem trace_cons (f : RegionOperation F → List β) (operation : Operation F)
    (rest : Operations F) :
    trace f (operation :: rest) = match operation with
      | .region _ body => body.flatMap f :: trace f rest
      | _ => trace f rest := by
  cases operation <;> rfl

/-- Synthesis traces concatenate. -/
theorem trace_append (f : RegionOperation F → List β) (first second : Operations F) :
    trace f (first ++ second) = trace f first ++ trace f second := by
  simp only [trace, List.filterMap_append]

/-- Synthesis traces commute with `flatMap`. -/
theorem trace_flatMap (f : RegionOperation F → List β) (items : List α)
    (body : α → Operations F) :
    trace f (items.flatMap body) = items.flatMap fun item => trace f (body item) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, trace_append, ih]

/-- A region contributes exactly its own trace, even where that trace is empty. -/
theorem trace_region (f : RegionOperation F → List β) (name : String)
    (body : RegionOperations F) : trace f [.region name body] = [body.flatMap f] := rfl

/-- An instance constraint outside a region does not contribute any trace slot. -/
theorem trace_constrainInstance (f : RegionOperation F → List β) (cell : Cell)
    (column : Column .instance) (row : ℕ) :
    trace f [.constrainInstance cell column row] = [] := rfl

/-- A table load does not contribute any trace slot. -/
theorem trace_loadTable (f : RegionOperation F → List β) (table : TableColumn)
    (values : List F) : trace f [.loadTable table values] = [] := rfl

/-- Flattening synthesis-program lists preserves region order, which the generated loop normal
forms rely on. -/
theorem trace_flatten (f : RegionOperation F → List β) (bodies : List (Operations F)) :
    trace f bodies.flatten = (bodies.map (trace f)).flatten := by
  simp only [List.flatten_eq_flatMap, trace_flatMap, List.flatMap_map]
  rfl

section Loops
variable [FiniteField F]

/-- A fixed-stride loop exposes only its per-iteration traces. -/
theorem flatMap_forRange' (f : RegionOperation F → List β) (offset stride count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    ((RegionCircuit.forRange' offset stride count body).operations region).flatMap f =
      (List.ofFn fun i : Fin count =>
        ((body i.val (offset + i.val * stride)).operations region).flatMap f).flatten := by
  rw [RegionCircuit.forRange'_operations, flatten_flatMap, List.map_ofFn]
  rfl

/-- A variable row schedule keeps the same projection. -/
theorem flatMap_forRangeVar' (f : RegionOperation F → List β) (rows : ℕ → ℕ) (count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    ((RegionCircuit.forRangeVar' rows count body).operations region).flatMap f =
      (List.ofFn fun i : Fin count =>
        ((body i.val (rows i.val)).operations region).flatMap f).flatten := by
  rw [RegionCircuit.forRangeVar'_operations, flatten_flatMap, List.map_ofFn]
  rfl

/-- An accumulator-dependent fold preserves every operation of each actual iteration. -/
theorem flatMap_foldRange (f : RegionOperation F → List β) (offset stride count : ℕ)
    (initial : γ) (body : ℕ → ℕ → γ → RegionCircuit F γ) (region : RegionIndex) :
    ((RegionCircuit.foldRange offset stride count initial body).operations region).flatMap f =
      (List.ofFn fun i : Fin count =>
        ((body i.val (offset + i.val * stride)
          (RegionCircuit.foldAcc (fun j => offset + j * stride) initial body i.val
            region)).operations region).flatMap f).flatten := by
  unfold RegionCircuit.foldRange RegionCircuit.foldRangeVar
  rw [RegionCircuit.foldRangeVarAux_operations, flatten_flatMap, List.map_ofFn]
  rfl

/-- Serial calls preserve the exact concatenation of their per-iteration traces. An
input-independent trace for each child suffices to reduce the whole fold, without evaluating its
intermediate witnesses or region-index expressions. -/
theorem trace_foldCall {ConfigInput Config : Type}
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (f : RegionOperation F → List β)
    (children : ℕ → FormalCircuit F ConfigInput Config Input Output)
    (toInput : Var Output F → Var Input F) (config : Config) (initial : Var Input F)
    (count : ℕ) (region : RegionIndex) (traces : ℕ → List (List β))
    (htrace : ∀ index input current,
      trace f (((children index).call config input).operations current) = traces index) :
    trace f ((FormalCircuit.foldCall children toInput config initial count).operations region) =
      (List.ofFn fun i : Fin count => traces i.val).flatten := by
  rw [FormalCircuit.foldCall_operations]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [FormalCircuit.foldOps, trace_append, ih, htrace,
        List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rfl

/-- Promoting a region gadget to a layouter gadget contributes exactly one region, including
where that region's trace is empty. -/
theorem trace_toFormal_call {ConfigInput Config : Type}
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (f : RegionOperation F → List β)
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F) (region : RegionIndex) :
    trace f (((child.toFormal name).call config input).operations region) =
      [((child.call config 0 input).operations region).flatMap f] := by
  rw [FormalCircuit.call_operations, FormalRegionCircuit.call_operations]
  rfl

end Loops

end Zcash.Circuits.Trace
