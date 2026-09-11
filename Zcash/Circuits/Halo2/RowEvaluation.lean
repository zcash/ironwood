import Zcash.Circuits.Halo2.QueryLayout

/-! # Row semantics of compiled expressions

Query indices are read through the compiler's layouts. These definitions involve
only column values and integer rotations, not polynomials or commitments.
-/

namespace Halo2

namespace QueryState

variable {F : Type} [Field F]

/-- Read one indexed query at a row of an environment. -/
def queryValues (queries : Array (ℕ × ℤ)) (kind : ColumnKind)
    (env : Environment F) (row : ℤ) (index : ℕ) : F :=
  let query := queries[index]?.getD (0, 0)
  env.get ⟨kind, query.1⟩ (row + query.2)

/-- Evaluate a compiled expression using the column/rotation query layouts. -/
def eval (queries : QueryState) (env : Environment F) (row : ℤ)
    (expression : RichExpression F) : F :=
  expression.eval (queryValues queries.fixed .fixed env row)
    (queryValues queries.advice .advice env row)
    (queryValues queries.inst .instance env row)

/-- Reading registered coordinates interprets the corresponding source queries. -/
theorem interprets (queries : QueryState) (env : Environment F) (row : ℤ) :
    Interprets queries (queryValues queries.fixed .fixed env row)
      (queryValues queries.advice .advice env row)
      (queryValues queries.inst .instance env row)
      (Query.eval env (fun _ => 0) row) := by
  constructor <;> intro index column rotation hentry <;>
    simp only [queryValues, hentry, Option.getD_some, Query.eval]
    <;> rfl

end QueryState

namespace TopLevelCircuit

variable {F : Type} [FiniteField F] {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Compilation preserves the number of source gate constraints. -/
theorem pinnedCS_gates_length :
    top.pinnedCS.gates.length = (flatGates top.constraintSystem).length := by
  rw [top.pinnedCS_eq_derive]
  exact PinnedConstraintSystem.derive_gates_length _ _

/-- Compiled gate evaluation agrees with the selector-substituted source valuation. -/
theorem pinnedCS_gates_eval_subst (fixed advice instanceFeed : ℕ → F)
    (valuation : Query → F)
    (hcoverage : ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (hinterprets : Interprets (Zcash.Snark.pinnedQueryState top.pinnedCS)
      fixed advice instanceFeed valuation)
    (index : ℕ) (hcompiled : index < top.pinnedCS.gates.length)
    (hsource : index < (flatGates top.constraintSystem).length) :
    top.pinnedCS.gates[index].eval fixed advice instanceFeed =
      (flatGates top.constraintSystem)[index].eval
        (substValuation top.selectorMap.lookup valuation) := by
  rw [top.pinnedQueryState_eq_gateQueryState] at hinterprets
  exact PinnedConstraintSystem.derive_gates_eval top.constraintSystem top.selectorMap
    fixed advice instanceFeed valuation hcoverage top.gateQueriesResolved
    hinterprets index hcompiled hsource

/-- The row evaluation is the selector-substituted source evaluation. -/
theorem pinnedCS_gates_eval (env : Environment F) (row : ℤ)
    (hcoverage : ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (index : ℕ) (hcompiled : index < top.pinnedCS.gates.length)
    (hsource : index < (flatGates top.constraintSystem).length) :
    (Zcash.Snark.pinnedQueryState top.pinnedCS).eval env row top.pinnedCS.gates[index] =
      (flatGates top.constraintSystem)[index].eval
        (substValuation top.selectorMap.lookup (Query.eval env (fun _ => 0) row)) :=
  top.pinnedCS_gates_eval_subst _ _ _ _ hcoverage
    ((Zcash.Snark.pinnedQueryState top.pinnedCS).interprets env row) index hcompiled hsource

end TopLevelCircuit

end Halo2
