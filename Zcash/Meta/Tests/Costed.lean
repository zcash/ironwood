import Zcash.Meta.Costed

/-! Tests of `Costed`: the costed form of a first-order type is the type, that of a function type is
the function with its instrumented version, and a parametric inductive is its own mirror. The
equalities hold by unfolding the instances, which is what lets a derived cost function be stated at
the plain types. -/

namespace Zcash.Meta.Tests.Costed

open Zcash.Meta.Costed

example : WithCosts Nat = Nat := rfl
example : WithCosts (List Nat) = List Nat := rfl
example : WithCosts (Option (Nat × Bool)) = Option (Nat × Bool) := rfl
example : WithCosts (Fin 3 ⊕ Unit) = (Fin 3 ⊕ Unit) := rfl

example : WithCosts (Nat → Nat) = ((Nat → Nat) × (Nat → Nat × Nat)) := rfl

example : WithCosts (List (Nat → Bool)) = List ((Nat → Bool) × (Nat → Nat × Bool)) := rfl

example : WithCosts ((n : Nat) → Fin (n + 1)) =
    (((n : Nat) → Fin (n + 1)) × ((n : Nat) → Nat × Fin (n + 1))) := rfl

-- A function's costed form forgets to the function, and is consistent when its instrumented version
-- returns the function's results. (In the instrumented half, `n : WithCosts Nat`, which is `Nat` by
-- unfolding but not syntactically, so `n + 1` would not find its instance.)
def succWithCosts : WithCosts (Nat → Nat) := (Nat.succ, fun n => (1, Nat.succ n))

example : forget succWithCosts 4 = 5 := rfl

example : Consistent succWithCosts := by
  intro n _
  exact ⟨rfl, trivial⟩

-- A list of functions: each element's costs travel with it.
example : WithCosts (List (Nat → Nat)) := [succWithCosts, (id, fun n => (0, n))]

example : (forget (T := List (Nat → Nat)) [succWithCosts, (id, fun n => (0, n))]).map (· 1) =
    [2, 1] := rfl

end Zcash.Meta.Tests.Costed
