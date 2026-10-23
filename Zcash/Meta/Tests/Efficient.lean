import Zcash.Meta.Efficient
import Zcash.Meta.AxiomCheck

/-!
# Regression tests for `Zcash.Meta.Efficient` and `assert_efficient`

Cost functions derived for small first-order definitions, with their values pinned by `#eval`,
one bound proved by induction, and the rejections pinned by `#guard_msgs`. `assert_efficient`
is pinned on a passing definition, on a rejected one, and with a flag it does not deserve.
-/

namespace Zcash.Meta.Tests.Efficient

universe u v w

/-! ## Primitive costs: one unit per arithmetic operation, `length` linear. -/

def hAddCost {α : Type u} {β : Type v} {γ : Type w} [HAdd α β γ] (_a : α) (_b : β) : Nat := 1
def hMulCost {α : Type u} {β : Type v} {γ : Type w} [HMul α β γ] (_a : α) (_b : β) : Nat := 1
def hModCost {α : Type u} {β : Type v} {γ : Type w} [HMod α β γ] (_a : α) (_b : β) : Nat := 1
def lengthCost {α : Type u} (xs : List α) : Nat := xs.length + 1

efficient_cost HAdd.hAdd := hAddCost
efficient_cost HMul.hMul := hMulCost
efficient_cost HMod.hMod := hModCost
efficient_cost List.length := lengthCost

/-! ## Derived costs -/

/-- One addition: one unit for the call and one for the operation. -/
efficient def double (n : Nat) : Nat := n + n

/-- info: 2 -/
#guard_msgs in
#eval double.cost 5

/-- Structural recursion through `match`: one unit per decision, then the branch. -/
efficient def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + sumList rest

/-- info: 13 -/
#guard_msgs in
#eval sumList.cost [1, 2, 3]

theorem sumList_cost_le (xs : List Nat) : sumList.cost xs ≤ 4 * xs.length + 1 := by
  induction xs with
  | nil => simp [sumList.cost]
  | cons x rest ih => simp [sumList.cost, hAddCost]; omega

/-- A call of an `efficient` function is priced at its cost function. -/
efficient def twiceSum (xs : List Nat) : Nat := double (sumList xs)

/-- info: 17 -/
#guard_msgs in
#eval twiceSum.cost [1, 2, 3]

/-- Insertion with an `if`: the comparison is one decision, so inserting past three elements
costs three matches, three comparisons, three recursive calls, and the final match. -/
efficient def insort1 (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insort1 x ys

/-- info: 10 -/
#guard_msgs in
#eval insort1.cost 5 [1, 2, 3]

/-- Well-founded recursion: the termination suffix is copied to the cost function. -/
efficient def gcd' (a b : Nat) : Nat :=
  if _h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

/-- info: 13 -/
#guard_msgs in
#eval gcd'.cost 12 18

-- A pin is silent on success, like `assert_computable`.
#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.gcd'

-- The flags are `assert_computable`'s, with the same checks behind them.
#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.double

/--
error: Zcash.Meta.Tests.Efficient.double does not depend on Classical.choice; drop the '+choice' flag
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.double +choice

/-! ## On-demand derivation: a plain definition, a recursive one in equation style, and a call
into the core library, each priced from its definition by `assert_efficient` alone. -/

def triple (n : Nat) : Nat := n + n + n

-- The pin derives `triple.cost`; two additions and two calls.
#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.triple

/-- info: 4 -/
#guard_msgs in
#eval triple.cost 1

def sumList' : List Nat → Nat
  | [] => 0
  | x :: rest => x + sumList' rest

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.sumList'

/-- info: 13 -/
#guard_msgs in
#eval sumList'.cost [1, 2, 3]

/-- `List.reverse` is priced from its own definition, through `List.reverseAux`, whose derived
cost is private to this module. -/
def rev (xs : List Nat) : List Nat := xs.reverse

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.rev

/-- info: 9 -/
#guard_msgs in
#eval rev.cost [1, 2, 3]

/-- Well-founded recursion with a hand-written decreasing proof. The on-demand derivation can
only offer Lean's default decreasing tactic for the cost function's recursion, which does not
prove `a % b < b`, so the pin fails with Lean's report (dropped here, since it quotes source
positions) and leaves `gcd''` without a cost function. `gcd'` above shows the way through: an
`efficient def`, whose termination suffix is copied to the cost function. -/
def gcd'' (a b : Nat) : Nat :=
  if _h : b = 0 then a else gcd'' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

#guard_msgs (drop error) in
assert_efficient Zcash.Meta.Tests.Efficient.gcd''

/-- info: false -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  Lean.logInfo m!"{(Zcash.Meta.Efficient.costFn? (← Lean.getEnv) ``Zcash.Meta.Tests.Efficient.gcd'').isSome}"

/-! ## Rejections -/

partial def spin (n : Nat) : Nat := spin n

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.spin':
  'Zcash.Meta.Tests.Efficient.spin' is a `partial` definition (an opaque constant implemented by unsafe code), so it has no body to price; register a cost function for it with `efficient_cost Zcash.Meta.Tests.Efficient.spin := <cost function>`
-/
#guard_msgs (whitespace := lax) in
efficient def useSpin (n : Nat) : Nat := n + spin n

/-- An honest `opaque` with a value is a reduction barrier for proofs; what runs is its value,
which is what gets priced. -/
opaque hidden : Nat := 3

#guard_msgs in
efficient def useHidden (n : Nat) : Nat := n + hidden

/--
error: efficient def: `f` is a function, and `efficient def` cannot price a call of a function parameter: the cost function it builds has no companion for the parameter's cost. Define `Zcash.Meta.Tests.Efficient.applyTwice` with `def` and pin it with `assert_efficient`, which derives a cost function that takes a companion `f.cost`.
-/
#guard_msgs (whitespace := lax) in
efficient def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

/-! ## Higher order, on demand: a function-typed parameter gets a cost companion, a lambda
argument is priced by its body, and a library function such as `List.map` derives with
companions of its own. -/

def applyTwice' (f : Nat → Nat) (n : Nat) : Nat := f (f n)

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.applyTwice'

-- The companion `f.cost` follows the original binders. Two calls of `f`, each one unit plus
-- `f`'s own cost of one.
/-- info: 4 -/
#guard_msgs in
#eval applyTwice'.cost (· + 1) 3 (fun _ => 1)

def incrAll (xs : List Nat) : List Nat := xs.map (· + 1)

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.incrAll

-- One call of `map`; per element a match, a call of the lambda, its addition (one for the call
-- and one for the operation), and the recursive call; and the match of the empty case.
/-- info: 17 -/
#guard_msgs in
#eval incrAll.cost [1, 2, 3]

/-! ## Functions stored in structures: a field that is called gets a companion keyed by the
parameter and the field, and a caller that builds the structure in place supplies that
companion from the field's lambda. -/

structure Oracle where
  query : Nat → Nat
  bound : Nat

def twoQueries (o : Oracle) (x : Nat) : Nat := o.query x + o.query o.bound

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.twoQueries

-- Two calls of the stored function, each one unit plus its own cost of two, and one addition.
/-- info: 8 -/
#guard_msgs in
#eval twoQueries.cost ⟨(· * 2), 5⟩ 3 (fun _ => 2)

def viaLiteral (x : Nat) : Nat := twoQueries ⟨(· + 1), 7⟩ x

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.viaLiteral

-- One call of `twoQueries`, whose companion is the cost of `(· + 1)`, two per call.
/-- info: 9 -/
#guard_msgs in
#eval viaLiteral.cost 3

/-! ## A recursor with induction hypotheses: each hypothesis contributes the cost of the
recursive result and stands for its value in the branch. -/

def pow2 (n : Nat) : Nat := Nat.rec 1 (fun _ ih => ih + ih) n

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.pow2

-- Per step one decision, the recursive result's cost, and an addition (a call and an
-- operation); the base case is one decision.
/-- info: 10 -/
#guard_msgs in
#eval pow2.cost 3

/-! A recursor whose motive is a function type: the minor premise binds the result's argument
after the induction hypothesis, and the hypothesis is a cost function, charged at each
application. -/

def iter (f : Nat → Nat) (n : Nat) : Nat → Nat := Nat.rec id (fun _ ih x => f (ih x)) n

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.iter

-- Per step one decision, a call of the hypothesis at the argument, and a call of `f` with its
-- own cost of one; the base case is one decision.
/-- info: 13 -/
#guard_msgs in
#eval iter.cost (· + 1) 3 0 (fun _ => 1)

/-! A matcher whose alternative rebinds a parameter as a pattern variable, as `Option.bind`'s
`| some a, f => f a` does: the matcher is unfolded, which restores the parameter and its
companion. -/

def bindOpt (x : Option Nat) (f : Nat → Option Nat) : Option Nat := x.bind f

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.bindOpt

-- One call of `bind`, its decision, one call of `f`, and `f`'s own cost of one.
/-- info: 4 -/
#guard_msgs in
#eval bindOpt.cost (some 3) (fun n => some (n + 1)) (fun _ => 1)

/-! An alternative that is a bare parameter: once the unfolded matcher is beta-reduced, the
branch is a local, which is a value and not a call. -/

def getD' (x : Option Nat) (f : Nat → Nat) (d : Nat) : Nat :=
  match x, f with
  | some a, g => g a
  | none, _ => d

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.getD'

-- The decision, one call of `f`, and `f`'s own cost of one; the decision alone for `none`.
/-- info: 3 -/
#guard_msgs in
#eval getD'.cost (some 3) (· + 1) 0 (fun _ => 1)

/-- info: 1 -/
#guard_msgs in
#eval getD'.cost none (· + 1) 0 (fun _ => 1)

/-! ## A local function without a companion: the report names it and gives its type. A local
that the elaborator named, such as a field bound by a `match` through the unfolded matcher, is
shown as the pretty-printer renders it, with the expression that uses it. -/

def callIn (s : Sum Nat (Nat → Nat)) : Nat :=
  match s with
  | .inl n => n
  | .inr g => g 1

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.callIn':
  in the body of `Zcash.Meta.Tests.Efficient.callIn`, the function `val✝` of type `ℕ → ℕ` is called in `val✝ 1`, but its cost is unknown there. It is a local with no name of its own, bound by a lambda, a `let`, or a `match` pattern. The derivation has cost companions only for the parameters of `Zcash.Meta.Tests.Efficient.callIn`, and for functions stored in fields of those parameters.
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.callIn

def callInCases (s : Sum Nat (Nat → Nat)) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s (fun n => n) (fun g => g 1)

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.callInCases':
  in the body of `Zcash.Meta.Tests.Efficient.callInCases`, the function `g` of type `ℕ → ℕ` is called, but its cost is unknown there. It is a local bound by a lambda, a `let`, or a `match` pattern. The derivation has cost companions only for the parameters of `Zcash.Meta.Tests.Efficient.callInCases`, and for functions stored in fields of those parameters.
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.callInCases

def passIn (s : Sum Nat (Nat → Nat)) : List Nat :=
  match s with
  | .inl n => [n]
  | .inr g => [1].map g

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.passIn':
  in the body of `Zcash.Meta.Tests.Efficient.passIn`, the function `val✝` of type `ℕ → ℕ` is passed on, but its cost is unknown there. It is a local with no name of its own, bound by a lambda, a `let`, or a `match` pattern. The derivation has cost companions only for the parameters of `Zcash.Meta.Tests.Efficient.passIn`, and for functions stored in fields of those parameters.
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.passIn

/-! ## A class method on an instance that is a field of a parameter: its companion is keyed by
the parameter, the field, and the method, as a function field's is, and a method that returns
data gets a constant companion. A caller whose structure is built on the spot supplies them
from the fields' values. -/

class Counter (α : Type) where
  limit : Nat
  step : α → Nat

structure Holder (α : Type) where
  counter : Counter α
  seed : α

def viaHolder (h : Holder Nat) : Nat := h.counter.step h.seed + h.counter.limit

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.viaHolder

-- The addition at two, the call of `step` and its cost of one, and the access of `limit` at
-- its cost of zero.
/-- info: 5 -/
#guard_msgs in
#eval viaHolder.cost ⟨⟨7, (· + 1)⟩, 3⟩ 0 (fun _ => 1)

def viaLiteralHolder (x : Nat) : Nat := viaHolder ⟨⟨7, (· + 1)⟩, x⟩

#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.viaLiteralHolder

-- One call of `viaHolder`, with `limit`'s literal free and `step`'s lambda at two.
/-- info: 7 -/
#guard_msgs in
#eval viaLiteralHolder.cost 3

/-! An instance that is neither a parameter nor a field of one: the report says what it is. -/

def onLocal (xs : List (Counter Nat)) : List Nat := xs.map fun c => c.limit

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.onLocal':
  the class method 'Zcash.Meta.Tests.Efficient.Counter.limit' is used on an instance whose methods cannot be priced: the instance `c` is a local bound by a lambda, a `let`, or a `match` pattern, not a parameter of `Zcash.Meta.Tests.Efficient.onLocal`. Register a cost function for the method with `efficient_cost Zcash.Meta.Tests.Efficient.Counter.limit := <cost function>`
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.onLocal

opaque hiddenCounter : Counter Nat := ⟨0, id⟩

def onOpaque (n : Nat) : Nat := Counter.step (self := hiddenCounter) n

/--
error: efficient: while deriving the cost of 'Zcash.Meta.Tests.Efficient.onOpaque':
  the class method 'Zcash.Meta.Tests.Efficient.Counter.step' is used on an instance whose methods cannot be priced: the instance `hiddenCounter` is headed by `Zcash.Meta.Tests.Efficient.hiddenCounter`, an `opaque` constant. Register a cost function for the method with `efficient_cost Zcash.Meta.Tests.Efficient.Counter.step := <cost function>`
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.onOpaque

end Zcash.Meta.Tests.Efficient
