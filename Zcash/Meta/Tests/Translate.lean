import Zcash.Meta.Translate

/-! Tests of the instrumented translation: first-order definitions, a function-typed parameter, a
lambda passed to a library function, a structure with a function field, `match` through `casesOn`,
recursion, and the oracle-computation monad's `run`, whose continuation the companion design could
not price. -/

namespace Zcash.Meta.Tests.Translate

open Lean Elab Term Meta Zcash.Meta.Instrument Zcash.Meta.Translate

-- The primitives of `Nat` arithmetic, at one unit each: the instrumented version returns the
-- cost and the value.
efficient_inst Nat.add := fun (a b : Nat) => (1, a + b)
efficient_inst Nat.mul := fun (a b : Nat) => (1, a * b)
efficient_inst Nat.sub := fun (a b : Nat) => (1, a - b)
efficient_inst Nat.mod := fun (a b : Nat) => (1, a % b)

/-! ## First order -/

def triple (n : Nat) : Nat := n + n + n

#guard_msgs in
instrument triple

-- Two additions at one unit each, plus one for each call of `Nat.add`.
/-- info: (4, 9) -/
#guard_msgs in
#eval triple.inst 3

/-! ## A function-typed parameter: the costed form of `f` is `f` with its instrumented
version. -/

def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

#guard_msgs in
instrument applyTwice

-- Two applications of `f`, each one plus what its instrumented version reports.
/-- info: (4, 5) -/
#guard_msgs in
#eval applyTwice.inst (Nat.succ, fun n => (1, Nat.succ n)) 3

/-! ## A structure with a function field: the parameter comes as the mirror. -/

structure Oracle where
  query : Nat → Nat
  bound : Nat

def twoQueries (o : Oracle) (x : Nat) : Nat := o.query x + o.query o.bound

#guard_msgs in
instrument twoQueries

-- Two calls of `query` at one plus two each, and the addition at two.
/-- info: (8, 16) -/
#guard_msgs in
#eval twoQueries.inst (Oracle.withCosts.mk (fun n => n * 2, fun n => (2, n * 2)) 5) 3

/-! ## `match` and recursion -/

def sumList : List Nat → Nat
  | [] => 0
  | x :: rest => x + sumList rest

#guard_msgs in
instrument sumList

-- Per element: the decision, the addition at two, the recursive call; the empty case's decision.
/-- info: (13, 6) -/
#guard_msgs in
#eval sumList.inst [1, 2, 3]

/-! ## The oracle-computation monad: the continuation inside `query` is called through its
instrumented version, which the mirror carries. -/

inductive OC (T F α : Type) where
  | pure (a : α)
  | query (t : T) (k : F → OC T F α)

def OC.run {T F α : Type} : OC T F α → (T → F) → α
  | .pure a, _ => a
  | .query t k, O => (k (O t)).run O

#guard_msgs in
instrument OC.run

-- `query 3 k` with `k f = pure (f + 1)`, under the oracle `fun t => t * 10`: the decision; the call
-- of the oracle at one plus one; the call of the continuation at one plus one; the recursive `run`
-- on `pure` at one for the call plus one for its decision.
/-- info: (7, 31) -/
#guard_msgs in
#eval OC.run.inst (T := Nat) (F := Nat) (α := Nat)
  (OC.withCosts.query 3 (fun f => .pure (f + 1)) (fun _ => 1)
    (fun f => OC.withCosts.pure (f + 1)))
  (fun t => t * 10, fun t => (1, t * 10))

end Zcash.Meta.Tests.Translate
