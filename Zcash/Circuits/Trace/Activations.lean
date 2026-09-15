import Clean.Halo2.FormalRegion.Call
import Clean.Halo2.Keygen.FloorPlanner.RegionShape

/-!
# Compact activation traces

A region's activations, kept as the operations themselves rather than projected to labels.
Selector labels, gate labels and lookup labels are all projections of this one list, so a gadget
needs one trace lemma rather than one per label shape.

This is pure Halo2 compiler semantics: it does not mention any ironwood vocabulary, and is written
to be lifted into Clean, where the surrounding machinery already lives. Clean already provides the
placed selector form (`FloorPlanner.activations`), the region indexing (`indexedRegions`), and the
synthesis summaries with `combine`/`empty` and their associativity and unit laws. What is added
here is the pre-placement compact form, the label shapes as projections of it, and placement
generic in the label payload.

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
  function and one commutation theorem serve every label shape, instead of one per shape.

In the vocabulary of Gibbons and Oliveira's *The Essence of the Iterator Pattern*, each
projection is a traversal in a monoidal applicative: at the free monoid it collects labels, at
the additive naturals it counts, at `max` it measures extents — which is what the synthesis
summary's fields are. `project_of_vanishing` and the placement commutation are instances of that
paper's naturality and fusion laws rather than facts peculiar to circuits.
-/

namespace Zcash.Circuits.Trace

open Halo2

variable {F α β : Type}

/-! ## Activations -/

/-- The activation operations one operation contributes: itself, if it is one. -/
def activationOf : RegionOperation F → List (RegionOperation F)
  | operation@(.enableGate _ _) => [operation]
  | operation@(.enableLookup _ _ _) => [operation]
  | _ => []

/-- A region's activation operations, in source order, before floor-planner placement. -/
def regionActivations (body : RegionOperations F) : List (RegionOperation F) :=
  body.flatMap activationOf

/-- The ordered region activation lists; a region without activations still occupies a slot. -/
def activationTrace (operations : Operations F) : List (List (RegionOperation F)) :=
  operations.filterMap fun operation => match operation with
    | .region _ body => some (regionActivations body)
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

/-! ## Placement

A label is a payload paired with a row, and placement adds a region's start to the row. So
placing the activations determines the placement of every label shape at once.
-/

/-- Shift one activation's local row by a region start. -/
def shiftActivation (offset : ℕ) : RegionOperation F → RegionOperation F
  | .enableGate gate row => .enableGate gate (offset + row)
  | .enableLookup argument enabled row => .enableLookup argument enabled (offset + row)
  | operation => operation

/-- Apply the compiler's region starts to a compact activation trace. -/
def placeActivationTrace (starts : List ℕ) (trace : List (List (RegionOperation F)))
    (initial : ℕ := 0) : List (RegionOperation F) :=
  (trace.zipIdx initial).flatMap fun (body, index) =>
    body.map (shiftActivation (starts.getD index 0))

/-- Apply the compiler's region starts to a compact trace of labels of any payload. -/
def placeLabels (starts : List ℕ) (trace : List (List (α × ℕ))) (initial : ℕ := 0) :
    List (α × ℕ) :=
  (trace.zipIdx initial).flatMap fun (body, index) =>
    body.map fun label => (label.1, starts.getD index 0 + label.2)

/-- An extractor whose labels move with the row it reads. Every projection here satisfies it,
which is why one placement theorem serves them all. -/
abbrev ShiftsWithRow (f : RegionOperation F → List (α × ℕ)) : Prop :=
  ∀ offset operation, f (shiftActivation offset operation) =
    (f operation).map fun label => (label.1, offset + label.2)

theorem selectorOf_shiftsWithRow : ShiftsWithRow (F := F) selectorOf := by
  intro offset operation
  cases operation <;> simp [selectorOf, shiftActivation]

theorem gateOf_shiftsWithRow : ShiftsWithRow (F := F) gateOf := by
  intro offset operation
  cases operation <;> simp [gateOf, shiftActivation]

theorem lookupOf_shiftsWithRow : ShiftsWithRow (F := F) lookupOf := by
  intro offset operation
  cases operation <;> simp [lookupOf, shiftActivation]

/-- Placement commutes with any row-shifting projection, so placed labels of any shape may be
read off the one placed activation trace. -/
theorem placeLabels_eq_project (starts : List ℕ) (trace : List (List (RegionOperation F)))
    (initial : ℕ) (f : RegionOperation F → List (α × ℕ)) (hshift : ShiftsWithRow f) :
    placeLabels starts (trace.map fun body => body.flatMap f) initial =
      (placeActivationTrace starts trace initial).flatMap f := by
  induction trace generalizing initial with
  | nil => rfl
  | cons body rest ih =>
      simp only [List.map_cons, placeLabels, placeActivationTrace, List.zipIdx_cons,
        List.flatMap_cons, List.flatMap_append, List.map_flatMap, List.flatMap_map] at *
      rw [ih]
      congr 1
      simp only [hshift]

/-! ## Loops

A loop's activations arrive as a flattened list of per-iteration lists, so every loop gadget's
derivation needs the fact that projection commutes with flattening.
-/

/-- Projecting a flattened list is projecting each piece and then flattening. -/
theorem flatten_flatMap (bodies : List (List α)) (f : α → List β) :
    bodies.flatten.flatMap f = (bodies.map fun body => body.flatMap f).flatten := by
  induction bodies with
  | nil => rfl
  | cons body rest ih => simp only [List.flatten_cons, List.flatMap_append, ih, List.map_cons]

variable [FiniteField F]

/-- A fixed-stride loop exposes only its per-iteration activations. -/
theorem regionActivations_forRange' (offset stride count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    regionActivations ((RegionCircuit.forRange' offset stride count body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionActivations ((body i.val (offset + i.val * stride)).operations region)).flatten := by
  rw [RegionCircuit.forRange'_operations, regionActivations, flatten_flatMap, List.map_ofFn]
  rfl

end Zcash.Circuits.Trace
