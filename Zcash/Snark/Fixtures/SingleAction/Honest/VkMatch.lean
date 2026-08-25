import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Arithmetic.Domain
import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.PlannerTrace
import Zcash.Circuits.Action.TopLevel
import Clean.Halo2.TopLevel
import Mathlib.Util.AssertNoSorry

/-!
# VK equality: the capture is the derived Action circuit

The captured verifying key's constraint-system fields — gates, the three query layouts, the
permutation columns and chunks, the lookup families, the domain and permutation scalars — are
computed equal to those derived from the ported `Action.Circuit.configure`. No fixture input is
left in the derivation, and `configure` records the query-registration order itself, so a wrong
per-gate list shifts the layouts and fails here.

The equality is a record update (`capturedPinnedView = actionPinnedCs`) because the exporter
omits five pinned-CS metadata fields (`numFixedColumns`, `numAdviceColumns`, `numSelectors`,
`constants`, `minimumDegree`). Those carry over uncompared, but their consequences are pinned
elsewhere: wrong counts or constants fail the commitment certificate (`Keygen/Certificate.lean`),
and `chunkLen` is compared directly below. Per-field theorems name the diverging field on drift.

Like the fingerprint match, these are `native_decide` facts about one capture, never general
theorems.
-/

namespace Zcash.Snark.Fixture

open Zcash.Arithmetic (deltaFp omegaOf)

open Halo2
open Zcash.Circuits.Action (actionCircuit)

/-- The pinned CS derived from the closed Action circuit — the
`TopLevelCircuit.pinnedCS` method (Clean's `FormalCircuit.toPinnedCS`): query order
from the circuit's own configure-recorded registration (see the module docstring), at
the derived domain size (`TopLevelCircuit.domainExponent`, the keygen fit condition —
no domain constant survives as an input either). -/
def actionPinnedCs : PinnedConstraintSystem Fp :=
  actionCircuit.pinnedCS

/-! Nullary evaluation shares: every occurrence of a method APPLICATION in a decided
proposition re-runs the circuit's configure/synthesize chain during `native_decide`
evaluation, so the bundles below are stated over these once-per-process definitions.
The public theorems restate the facts in method spelling via `simp only` unfolding. -/

/-- The capture's permutation columns, in raw column space. The captured
`vk.permutationChunks` stores the verifier view — `ColumnRef`s in QUERY-INDEX space
(`ColumnRef.resolve` reads the eval arrays by query index) — so each ref resolves to
its column through the captured query layouts (permutation queries are always
cur-rotation, so the lookup is exact). -/
def capturedPermutationColumns : List Halo2.AnyColumn :=
  vk.permutationChunks.flatten.map fun p =>
    match p.1 with
    | .advice qi => ⟨.advice, (vk.adviceQueryLayout.getD qi (0, 0)).1⟩
    | .fixed qi => ⟨.fixed, (vk.fixedQueryLayout.getD qi (0, 0)).1⟩
    | .instance qi => ⟨.instance, (vk.instanceQueryLayout.getD qi (0, 0)).1⟩

/-- The derived pinned record with every CAPTURED family overridden by the capture's
value: the captured gate/lookup expressions are verifier-typed `Zcash.Snark.Expr`, so
they convert at the boundary (`RichExpression.ofExpr`); the lookup families are the
`Fin`-function views re-listed. Equality with `actionPinnedCs` pins exactly the
captured data (the five uncaptured metadata fields are carried over — see the module
docstring). -/
def capturedPinnedView : PinnedConstraintSystem Fp :=
  { actionPinnedCs with
    numInstanceColumns := capturedNumInstanceColumns
    gates := vk.gates.map RichExpression.ofExpr
    adviceQueryLayout := vk.adviceQueryLayout
    fixedQueryLayout := vk.fixedQueryLayout
    instanceQueryLayout := vk.instanceQueryLayout
    permutationColumns := capturedPermutationColumns
    lookupInputExprs := (List.ofFn vk.lookupInputExprs).map (·.map RichExpression.ofExpr)
    lookupTableExprs := (List.ofFn vk.lookupTableExprs).map (·.map RichExpression.ofExpr) }

/-- **The capture is the derived Action circuit** (pinned CS, captured families). -/
theorem capturedPinnedView_eq_derived : capturedPinnedView = actionPinnedCs := by native_decide

/-- The derived domain exponent is orchard's pinned `K = 11` (`circuit.rs:76`). -/
theorem actionK_eq : actionCircuit.domainExponent = 11 := by
  rw [Halo2.TopLevelCircuit.domainExponent,
    Zcash.Circuits.Action.actionCircuit_shape_eq,
    Zcash.Circuits.Action.actionShape_k]

/-- **The captured verifying key's gates are the derived Action circuit's.** The
verifying key holds `Zcash.Snark.Expr` gates and the derivation holds
`Halo2.RichExpression` gates, so the equality is stated through the boundary
conversion `RichExpression.ofExpr`. -/
theorem vk_gates_eq_derived :
    vk.gates.map RichExpression.ofExpr = actionPinnedCs.gates :=
  congrArg PinnedConstraintSystem.gates capturedPinnedView_eq_derived

theorem vk_adviceQueryLayout_eq_derived :
    vk.adviceQueryLayout = actionPinnedCs.adviceQueryLayout :=
  congrArg PinnedConstraintSystem.adviceQueryLayout capturedPinnedView_eq_derived

theorem vk_fixedQueryLayout_eq_derived :
    vk.fixedQueryLayout = actionPinnedCs.fixedQueryLayout :=
  congrArg PinnedConstraintSystem.fixedQueryLayout capturedPinnedView_eq_derived

theorem vk_instanceQueryLayout_eq_derived :
    vk.instanceQueryLayout = actionPinnedCs.instanceQueryLayout :=
  congrArg PinnedConstraintSystem.instanceQueryLayout capturedPinnedView_eq_derived

theorem vk_lookupInputExprs_eq_derived :
    (List.ofFn vk.lookupInputExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupInputExprs :=
  congrArg PinnedConstraintSystem.lookupInputExprs capturedPinnedView_eq_derived

theorem vk_lookupTableExprs_eq_derived :
    (List.ofFn vk.lookupTableExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupTableExprs :=
  congrArg PinnedConstraintSystem.lookupTableExprs capturedPinnedView_eq_derived

theorem permutationColumns_eq :
    capturedPermutationColumns = actionPinnedCs.permutationColumns :=
  congrArg PinnedConstraintSystem.permutationColumns capturedPinnedView_eq_derived

theorem numInstanceColumns_eq :
    capturedNumInstanceColumns = actionPinnedCs.numInstanceColumns :=
  congrArg PinnedConstraintSystem.numInstanceColumns capturedPinnedView_eq_derived

/-! ## The VK's domain and permutation scalars, derived

The captured `vk`'s scalar fields are computable from the circuit: `omega`/`n` from the derived domain exponent
(`TopLevelCircuit.domainExponent`), `blindingFactors` from the configure-recorded
advice queries, `delta` a pasta constant, `chunkLen` from the ported `cs.degree()`,
and `permutationChunks` the recorded permutation columns chunked by it. -/

theorem vk_scalars_and_chunks_derived :
    ((vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen), vk.permutationChunks)
      = ((actionCircuit.omega, actionCircuit.n,
            actionCircuit.blindingFactors, deltaFp, actionCircuit.chunkLen),
          actionCircuit.verifierCS.permutationChunks) := by
  native_decide

theorem vk_scalars_derived :
    (vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen)
      = (actionCircuit.omega,
          actionCircuit.n,
          actionCircuit.blindingFactors, deltaFp,
          actionCircuit.chunkLen) := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h ⊢
  exact h.1

theorem vk_permutationChunks_derived :
    vk.permutationChunks
      = actionCircuit.verifierCS.permutationChunks := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h
  exact h.2

assert_no_sorry capturedPinnedView_eq_derived
assert_no_sorry actionK_eq
assert_no_sorry vk_scalars_and_chunks_derived

end Zcash.Snark.Fixture
