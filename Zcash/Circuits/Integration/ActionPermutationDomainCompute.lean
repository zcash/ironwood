import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.ActionGateCoherenceCompute
import Mathlib.Util.AssertNoSorry
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `actionCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (deltaFp)

open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 :=
  ActionGateCoherence.domainExponent_lt

/-- The Action permutation-column prefix fits easily inside `deltaFp`'s
certified order. This residual concrete count awaits a configure law bounding the
derived equality-enabled column list. -/
theorem permutationColumnCount_eq :
    actionCircuit.permutationColumnCount =
      15 := by
  native_decide

/-- The Action circuit configures exactly one instance column. -/
theorem numInstanceColumns_eq :
    actionCircuit.constraintSystem.numInstanceColumns = 1 := by
  native_decide

/-- The Action fixed-column and common-permutation table is tiny: the adaptive-statement zero
family carries one representation per column, and its structural `2 ^ 89` interface cap
(`adaptiveStatementFixedRepresentationLimit`) consumes this bound. Like the counts above, this
residual concrete bound awaits a configure law for the pinned constraint system's column lists. -/
theorem fixedColumnCount_add_permutationColumnCount_lt :
    actionCircuit.fixedColumnCount + actionCircuit.permutationColumnCount < 2 ^ 20 := by
  native_decide

/-- Every instance query in the Action circuit's pinned layout names the single
configured instance column. -/
theorem instanceQueryLayout_columns_lt :
    ∀ entry ∈ actionCircuit.instanceQueryLayout, entry.1 < 1 := by
  native_decide

def ColumnRefCoherent : ColumnRef → Prop
  | .advice i =>
      i < actionCircuit.adviceQueryLayout.length ∧
        (actionCircuit.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < actionCircuit.fixedQueryLayout.length ∧
        (actionCircuit.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < actionCircuit.instanceQueryLayout.length ∧
        (actionCircuit.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Executable form of one reference's L-classified routing obligations. -/
def routingCoherentBool (ref : ColumnRef × ℕ) : Bool :=
  match ref.1 with
  | .advice i =>
      decide (i < actionCircuit.adviceQueryLayout.length) &&
      decide
        ((actionCircuit.adviceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide (ref.2 < actionCircuit.permutationColumnCount)
  | .fixed i =>
      decide (i < actionCircuit.fixedQueryLayout.length) &&
      decide
        ((actionCircuit.fixedQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide (ref.2 < actionCircuit.permutationColumnCount)
  | .instance i =>
      decide (i < actionCircuit.instanceQueryLayout.length) &&
      decide
        ((actionCircuit.instanceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide (ref.2 < actionCircuit.permutationColumnCount)

theorem routingCoherentBool_eq_true_iff (ref : ColumnRef × ℕ) :
    routingCoherentBool ref = true ↔
      ColumnRefCoherent ref.1 ∧
        ref.2 < actionCircuit.permutationColumnCount := by
  rcases ref with ⟨ref, common⟩
  cases ref <;> simp [routingCoherentBool, ColumnRefCoherent]

/-- Compiled Action references that fail either query routing or global-index
bounds. This remains the L-classified routing diagnostic. -/
def routingFailures : List (ColumnRef × ℕ) :=
  actionCircuit.verifierCS.permutationChunks.flatten.filter fun ref =>
      !routingCoherentBool ref

theorem routingFailures_eq_nil : routingFailures = [] := by
  native_decide

/-- Every Action permutation reference selects an in-range rotation-zero query and
every accompanying common-permutation index is in range. -/
theorem routingCoherent :
    ∀ chunk ∈
        actionCircuit.verifierCS.permutationChunks,
      ∀ ref ∈ chunk,
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            actionCircuit.permutationColumnCount := by
  intro chunk hchunk ref href
  by_contra hfailure
  have hmem :
      ref ∈ routingFailures := by
    rw [routingFailures, List.mem_filter]
    refine ⟨List.mem_flatten.mpr ⟨chunk, hchunk, href⟩, ?_⟩
    have hfalse : routingCoherentBool ref = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun htrue =>
        hfailure ((routingCoherentBool_eq_true_iff ref).mp htrue)
    simp [hfalse]
  rw [routingFailures_eq_nil] at hmem
  simp at hmem

assert_no_sorry domainExponent_lt
assert_no_sorry permutationColumnCount_eq
assert_no_sorry routingFailures_eq_nil
assert_no_sorry routingCoherent

end ActionPermutationDomain

end Zcash.Snark
