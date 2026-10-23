import Mathlib.Data.Fintype.Card
import Zcash.Meta.Efficient

/-!
# The cost model of the primitives

`efficient def` and `assert_efficient` derive costs from definitions down to the primitives, and
a primitive needs a registered cost function (`Zcash.Meta.Efficient`). This module registers the
arithmetic class methods at one unit each, whatever the carrier: a field operation, a `Nat` or
`Int` operation, a negation or an inverse costs one. That is the usual model for a concrete
security reduction, where the cost is counted in field operations, and it is also the only model
that a polymorphic registration can express: the carrier is a type parameter, so the cost cannot
depend on the size of the operands.

Two consequences to keep in mind. First, `x ^ n` is charged as one operation, although
exponentiation by a large exponent costs about `log₂ n` multiplications; a reduction whose cost
rests on exponentiations is under-counted by that factor. Second, a class method is priced at the
method, not by unfolding the instance; so the cost of a `Nat` addition does not depend on the
size of the numbers, and the cost of an operation on a structure that bundles several field
operations (a point addition, say) is still one, unless the operation is a definition of its own
rather than a class method, in which case it is derived from that definition.
-/

namespace Zcash.Meta.Efficient.Prelude

universe u v w

def hAddCost {α : Type u} {β : Type v} {γ : Type w} [HAdd α β γ] (_a : α) (_b : β) : Nat := 1
def hSubCost {α : Type u} {β : Type v} {γ : Type w} [HSub α β γ] (_a : α) (_b : β) : Nat := 1
def hMulCost {α : Type u} {β : Type v} {γ : Type w} [HMul α β γ] (_a : α) (_b : β) : Nat := 1
def hDivCost {α : Type u} {β : Type v} {γ : Type w} [HDiv α β γ] (_a : α) (_b : β) : Nat := 1
def hModCost {α : Type u} {β : Type v} {γ : Type w} [HMod α β γ] (_a : α) (_b : β) : Nat := 1
def hPowCost {α : Type u} {β : Type v} {γ : Type w} [HPow α β γ] (_a : α) (_b : β) : Nat := 1
def hSMulCost {α : Type u} {β : Type v} {γ : Type w} [HSMul α β γ] (_a : α) (_b : β) : Nat := 1
def negCost {α : Type u} [Neg α] (_a : α) : Nat := 1
def invCost {α : Type u} [Inv α] (_a : α) : Nat := 1
def beqCost {α : Type u} [BEq α] (_a _b : α) : Nat := 1
/-- The constants `0` and `1` of a structure are free, like numerals. -/
def zeroCost {α : Type u} [Zero α] : Nat := 0
def oneCost {α : Type u} [One α] : Nat := 0
/-- Enumerating a finite type costs one step per element. -/
def fintypeElemsCost {α : Type u} [Fintype α] : Nat := Fintype.card α
/-- A default element is a constant. -/
def defaultCost {α : Type u} [Inhabited α] : Nat := 0
/-- Returning a value in a monad does no work of its own. -/
def pureCost {f : Type u → Type v} [Pure f] {α : Type u} (_a : α) : Nat := 0

efficient_cost Zero.zero := zeroCost
efficient_cost One.one := oneCost
efficient_cost Fintype.elems := fintypeElemsCost
efficient_cost Inhabited.default := defaultCost
efficient_cost Pure.pure := pureCost
efficient_cost HAdd.hAdd := hAddCost
efficient_cost HSub.hSub := hSubCost
efficient_cost HMul.hMul := hMulCost
efficient_cost HDiv.hDiv := hDivCost
efficient_cost HMod.hMod := hModCost
efficient_cost HPow.hPow := hPowCost
efficient_cost HSMul.hSMul := hSMulCost
efficient_cost Neg.neg := negCost
efficient_cost Inv.inv := invCost
efficient_cost BEq.beq := beqCost

end Zcash.Meta.Efficient.Prelude
