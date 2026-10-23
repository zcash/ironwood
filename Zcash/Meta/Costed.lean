/-!
# Values with their costs

A cost function derived by `assert_efficient` charges one unit per call, and must charge the calls
of every function that the priced definition runs. That includes functions that arrive inside
values: a continuation stored in a constructor, a function field of a structure that a call returns,
or a value of a type variable that a caller instantiates with a function type. To price those, a
derived cost function takes *costed forms* of values, not the values themselves:

* For a first-order type, which does not hold any function, the costed form is the type itself.
* For a function type, it is the function with its instrumented version, which returns the cost of a
  call together with the costed form of its result.
* For an inductive type whose constructors hold functions, it is a generated mirror of the type with
  each function field replaced by its costed form.

`WithCosts T` is a value of `T` together with the cost function of every function inside it.
`Costed T` gives the costed form of `T`, the map `forget` from it back to the value, and the
predicate `Consistent`. The latter says that the costs' results agree with the value: for a
function, that its instrumented version returns, at every consistent argument, the consistent
costed form of what the original function returns. Costed forms preserve universes: the costed
form of a type in `Type u` is in `Type u`, which lets a generator compute the universe of a costed
form from the original type before the costed form exists.

## Background

The costed form of a function type is a Kleisli arrow of the writer monad `Nat × -`. A derived
cost function is the call-by-value monadic translation of the definition into that monad, in the
sense of Moggi, "Notions of computation and monads", Information and Computation 93(1), 1991,
<https://doi.org/10.1016/0890-5401(91)90052-4>. Charging one unit per call is the tick of
Danielsson's thunk monad, "Lightweight semiformal time complexity analysis for purely functional
data structures", POPL 2008, <https://doi.org/10.1145/1328438.1328457>. Keeping the function beside
its instrumented version, related by `forget` and `Consistent`, is the logical relation between the
standard semantics and the instrumented one, packaged as glueing, as in Mitchell and Scedrov,
"Notes on sconing and relators", CSL 1992 (LNCS 702),
<https://link.springer.com/content/pdf/10.1007/3-540-56992-8_21.pdf>.

## What the class guarantees, and what it does not

`Consistent` is a law about *results*. It rules out an instance whose instrumented functions
compute something other than the function. It cannot rule out an instance whose instrumented
functions report too little cost: Lean has no notion of the cost of running one of its own terms,
so a cost is defined by the derivation and by the registered costs of primitives. There is nothing
inside the logic to check it against. For example, an instrumented function that returns zero for
every call satisfies every law that can be stated here.

So an instance of `Costed` written by hand is a *trusted assumption about cost*, like a cost
function registered for a primitive with `efficient_cost`. In particular, the first-order instance
`Costed.firstOrder T` asserts that no value of `T` holds a function, which is a fact about the
constructors of `T` that a proposition about its values cannot express. The derivation therefore
creates that instance for an inductive type only after reading every constructor, and there is no
instance that applies to every type by default. An instance written by hand is registered as such,
and `assert_efficient` reports, for each pinned definition, the hand-written instances and
registered costs that its cost function rests on, as `#print axioms` reports the axioms a theorem
rests on.
-/

universe u v

namespace Zcash.Meta

/-- The costed form of a type: its values with the cost functions of the functions inside them.
See the module documentation for what an instance asserts. -/
class Costed (T : Type u) where
  /-- A value of `T` together with the cost function of every function inside it. -/
  WithCosts : Type u
  /-- The value, with the cost functions forgotten. -/
  forget : WithCosts → T
  /-- The cost functions' results agree with the value. -/
  Consistent : WithCosts → Prop

namespace Costed

/-- The costed form of a first-order type is the type itself. This instance asserts that no value
of `T` holds a function, which nothing in the logic checks: it is written by hand only for the
primitive types below, and generated for an inductive type after its constructors have been read. -/
abbrev firstOrder (T : Type u) : Costed T where
  WithCosts := T
  forget := id
  Consistent _ := True

@[reducible] instance : Costed Nat := firstOrder Nat
@[reducible] instance : Costed Int := firstOrder Int
@[reducible] instance : Costed Bool := firstOrder Bool
@[reducible] instance : Costed PUnit.{u + 1} := firstOrder PUnit
@[reducible] instance : Costed Char := firstOrder Char
@[reducible] instance : Costed String := firstOrder String
@[reducible] instance (n : Nat) : Costed (Fin n) := firstOrder (Fin n)
@[reducible] instance : Costed UInt8 := firstOrder UInt8
@[reducible] instance : Costed UInt16 := firstOrder UInt16
@[reducible] instance : Costed UInt32 := firstOrder UInt32
@[reducible] instance : Costed UInt64 := firstOrder UInt64

/-- A function with its instrumented version, which returns the cost of a call and the costed
form of its result. The instrumented version takes the costed form of the argument, and its
result's type may depend on the argument's value. `forget` recovers that value, forgetting the
cost. -/
@[reducible] instance instPi {α : Type u} {β : α → Type v} [Costed α] [∀ a, Costed (β a)] :
    Costed ((a : α) → β a) where
  WithCosts := ((a : α) → β a) × ((ac : WithCosts α) → Nat × WithCosts (β (forget ac)))
  forget fc := fc.1
  Consistent fc := ∀ ac, Consistent ac →
    forget (fc.2 ac).2 = fc.1 (forget ac) ∧ Consistent (fc.2 ac).2

/-! A parametric inductive type whose constructors hold functions only through its parameters
is its own mirror: its costed form is the type at the costed forms of its parameters. -/

@[reducible] instance {α : Type u} [Costed α] : Costed (List α) where
  WithCosts := List (WithCosts α)
  forget := List.map forget
  Consistent l := ∀ x ∈ l, Consistent x

@[reducible] instance {α : Type u} [Costed α] : Costed (Array α) where
  WithCosts := Array (WithCosts α)
  forget := Array.map forget
  Consistent l := ∀ x ∈ l, Consistent x

@[reducible] instance {α : Type u} [Costed α] : Costed (Option α) where
  WithCosts := Option (WithCosts α)
  forget := Option.map forget
  Consistent
    | none => True
    | some x => Consistent x

@[reducible] instance {α : Type u} {β : Type v} [Costed α] [Costed β] : Costed (α × β) where
  WithCosts := WithCosts α × WithCosts β
  forget p := (forget p.1, forget p.2)
  Consistent p := Consistent p.1 ∧ Consistent p.2

@[reducible] instance {α : Type u} {β : Type v} [Costed α] [Costed β] : Costed (α ⊕ β) where
  WithCosts := WithCosts α ⊕ WithCosts β
  forget
    | .inl a => .inl (forget a)
    | .inr b => .inr (forget b)
  Consistent
    | .inl a => Consistent a
    | .inr b => Consistent b

@[reducible] instance {α : Type u} {β : α → Type v} [Costed α] [∀ a, Costed (β a)] :
    Costed ((a : α) × β a) where
  WithCosts := (ac : WithCosts α) × WithCosts (β (forget ac))
  forget p := ⟨forget p.1, forget p.2⟩
  Consistent p := Consistent p.1 ∧ Consistent p.2

@[reducible] instance {α : Type u} {p : α → Prop} [Costed α] : Costed { a : α // p a } where
  WithCosts := { ac : WithCosts α // p (forget ac) }
  forget s := ⟨forget s.1, s.2⟩
  Consistent s := Consistent s.1

end Costed

end Zcash.Meta
