import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Random-oracle collision vocabulary (classical ROM)

Shared foundation for the classical-ROM security arguments (key-binding `H^*`, and — reused
by the ledger-model games — note-commitment / nullifier `H^rcm`). We follow the *deterministic-exhibition*
style of `BindingSignature/Balance.lean`: a security theorem reduces a break to an *exhibited*
random-oracle collision, and the probability that such a collision occurs within `q` oracle queries —
the birthday bound `q(q-1)/|F|` — is a separate concern, carried as a named quantity
until discharged.

An abstract oracle is any function `O : Q → F` from queries to field outputs; "randomness" enters only
at the probability layer, so nothing here mentions probability.

## Collisions are data, reductions are functions

For any compressing oracle, collisions *exist* propositionally (pigeonhole), so an ∃-closed
collision `Prop` is true at every instantiation of interest. Conclusions of the form
`... ∨ (∃ collision)` and hypotheses of the form `¬ (∃ collision)` are then vacuous or
unsatisfiable, and proof irrelevance prevents a consumer from recovering the exhibited
collision from a proof. Collision events are therefore **structures carrying the colliding
queries as data**, and reductions are **computable functions** producing them. The
discipline: a plain `def`, never `noncomputable` — choice could conjure the data from mere
existence. Check with `#print axioms`, which reports the *transitive* axiom dependencies;
this catches a `sorry` or an unintended axiom hiding in a cited lemma rather than in the
definition itself, while `Classical.choice` appearing only via erased `Prop` fields is
harmless. Eyeball for efficiency — the one property Lean cannot express. (The convention is
documented in the Ironwood Book:
<https://zcash.github.io/ironwood/formal-verification.html#breaks-as-computed-data>.)

The `±`-collision variant `CollisionUpToSign` is the shape produced by arguments that pass through the
`Extract` coordinate extractor, whose fibres are `{P, -P}`: an `Extract`-equality of two commitments
yields an equality-or-negation of the underlying scalars. Both key-binding and the nullifier
(Faerie-Gold) argument bottom out in a `CollisionUpToSign`.
-/

namespace Zcash.Security.RandomOracle

variable {Q F : Type*}

/-- Equality up to sign: `a = b ∨ a = -b`, written `a =± b`. The `±`-collision events and the
algebraic ±-equations are stated with this. An `abbrev`, so it is definitionally transparent. -/
abbrev EqUpToSign [Neg F] (a b : F) : Prop := a = b ∨ a = -b

@[inherit_doc] scoped infix:50 " =± " => EqUpToSign

/-- A collision of an oracle `O`, as data: two distinct queries with equal outputs. -/
structure Collision (O : Q → F) where
  q₁ : Q
  q₂ : Q
  ne : q₁ ≠ q₂
  eq : O q₁ = O q₂

/-- A `±`-collision of `O`, as data: two distinct queries whose outputs are equal or negatives of
each other. This is the event exhibited by `Extract`-based reductions (key-binding, nullifier). -/
structure CollisionUpToSign [Neg F] (O : Q → F) where
  q₁ : Q
  q₂ : Q
  ne : q₁ ≠ q₂
  pm : O q₁ =± O q₂

/-- Every collision is a `±`-collision. -/
def Collision.upToSign [Neg F] {O : Q → F} (c : Collision O) : CollisionUpToSign O :=
  ⟨c.q₁, c.q₂, c.ne, Or.inl c.eq⟩

/-- A collision of a partial oracle `O`, as data: two distinct queries on which `O` is
defined, with equal outputs.  For a totalized partial function, plain `Collision` would
also accept two undefined queries mapped to the same sentinel; requiring the successful
evaluations keeps the event a genuine collision. -/
structure DefinedCollision (O : Q → Option F) where
  q₁ : Q
  q₂ : Q
  ne : q₁ ≠ q₂
  output : F
  eval₁ : O q₁ = some output
  eval₂ : O q₂ = some output

end Zcash.Security.RandomOracle
