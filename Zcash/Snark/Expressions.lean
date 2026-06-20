import Mathlib
import Zcash.Snark.ProofString

/-!
# The vanishing argument's `expected_h_eval`

The vanishing check confirms the quotient identity `h(x) · (xⁿ − 1) = Σ gates + Σ permutation + Σ lookup`
at the evaluation point: the verifier recomputes the right-hand side from the claimed evaluations and
divides by `xⁿ − 1` to get the value `expected_h_eval` it opens the folded `h` commitment to (halo2
`plonk/verifier.rs` `expressions` + `vanishing/verifier.rs` `verify`). This module transcribes that
recomputation:

* `Expr` / `Expr.eval` — the gate-polynomial AST and its evaluation at the claimed evals (halo2
  `Expression::evaluate`; virtual selectors are removed before verification, so they are absent).
* `permutationExpressions` — the permutation argument's constraint values (`permutation/verifier.rs`).
* `lookupExpressions` — the lookup argument's constraint values (`lookup/verifier.rs`).
* `expectedHEval` — fold all constraint values by `y` and divide by `xⁿ − 1`.

The gate polynomials, the permutation column/eval layout, and the lookup input/table expressions are
VK-fixed circuit data, supplied as inputs.
-/

namespace Zcash.Snark

/-- A gate (or lookup input/table) polynomial as halo2 evaluates it during verification
(`Expression::evaluate`): a constant, a fixed/advice/instance query (by query index into the claimed
evals), or a negation / sum / product / scaling. Virtual selectors are removed during circuit
optimization, so they never appear here. -/
inductive Expr (F : Type*) where
  | constant : F → Expr F
  | fixed : ℕ → Expr F
  | advice : ℕ → Expr F
  | instance : ℕ → Expr F
  | negated : Expr F → Expr F
  | sum : Expr F → Expr F → Expr F
  | product : Expr F → Expr F → Expr F
  | scaled : Expr F → F → Expr F

/-- Evaluate a gate polynomial at the claimed evaluations (halo2 `Expression::evaluate` with the
verifier's closures): queries resolve to `fixedEvals`/`adviceEvals`/`instanceEvals` at their index. -/
def Expr.eval {F : Type*} [CommRing F] (fixedEvals adviceEvals instanceEvals : ℕ → F) :
    Expr F → F
  | .constant c => c
  | .fixed i => fixedEvals i
  | .advice i => adviceEvals i
  | .instance i => instanceEvals i
  | .negated a => -(a.eval fixedEvals adviceEvals instanceEvals)
  | .sum a b => a.eval fixedEvals adviceEvals instanceEvals + b.eval fixedEvals adviceEvals instanceEvals
  | .product a b =>
      a.eval fixedEvals adviceEvals instanceEvals * b.eval fixedEvals adviceEvals instanceEvals
  | .scaled a c => a.eval fixedEvals adviceEvals instanceEvals * c

/-- Compress a list of expressions by `theta` (halo2 lookup `compress_expressions`):
`(((e₀)·θ + e₁)·θ + …)`. -/
def compressExprs {F : Type*} [CommRing F] (fixedEvals adviceEvals instanceEvals : ℕ → F)
    (theta : F) (exprs : List (Expr F)) : F :=
  exprs.foldl (fun acc e => acc * theta + e.eval fixedEvals adviceEvals instanceEvals) (0 : F)

/-- One chunk of the permutation argument's running rule (halo2 `permutation/verifier.rs`, lines
160–187): `(left − right) · (1 − (l_last + l_blind))`, where `left` folds `eval + β·permEval + γ` over
the chunk's `(columnEval, permEval)` pairs starting from `z(ωx)`, and `right` folds `eval + δ_cur + γ`
over the column evals starting from `z(x)` with `δ_cur` beginning at `β·x·δ^(chunkIndex·chunkLen)` and
multiplied by `δ` each column. -/
def permChunkExpression {F : Type*} [Field F] (beta gamma x delta : F) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval F) (pairs : List (F × F)) (lLast lBlind : F) : F :=
  let left := pairs.foldl (fun acc p => acc * (p.1 + beta * p.2 + gamma)) set.nextEval
  let deltaStart := beta * x * delta ^ (chunkIndex * chunkLen)
  let right := (pairs.foldl (fun (acc : F × F) p => (acc.1 * (p.1 + acc.2 + gamma), acc.2 * delta))
    (set.eval, deltaStart)).1
  (left - right) * (1 - (lLast + lBlind))

/-- The permutation argument's constraint values (halo2 `permutation/verifier.rs` `expressions`): the
first-set rule `l₀·(1 − z₀)`, the last-set rule `(z_l² − z_l)·l_last`, the inter-set rules
`(zᵢ − z_{i−1}(ω^last x))·l₀`, and the per-chunk running rule. `chunks` pairs each set with its
`(columnEval, permEval)` list (VK-fixed column→eval layout zipped with the common evals). -/
def permutationExpressions {F : Type*} [Field F] (sets : List (PermSetEval F))
    (chunks : List (PermSetEval F × List (F × F))) (beta gamma x delta : F) (chunkLen : ℕ)
    (l0 lLast lBlind : F) : List F :=
  (match sets.head? with | some first => [l0 * (1 - first.eval)] | none => [])
  ++ (match sets.getLast? with | some last => [(last.eval ^ 2 - last.eval) * lLast] | none => [])
  ++ ((sets.drop 1).zip sets).map (fun p => (p.1.eval - p.2.lastEval.getD 0) * l0)
  ++ ((List.range chunks.length).zip chunks).map
      (fun p => permChunkExpression beta gamma x delta chunkLen p.1 p.2.1 p.2.2 lLast lBlind)

/-- The lookup argument's constraint values (halo2 `lookup/verifier.rs` `expressions`): the first/last
rules on the product `z`, the product rule
`(z(ωx)·(a'+β)·(s'+γ) − z·(compress(input)+β)·(compress(table)+γ))·active`, and the two permuted-column
rules. `active = 1 − (l_last + l_blind)`; `inputExprs`/`tableExprs` are the VK-fixed lookup expressions. -/
def lookupExpressions {F : Type*} [Field F] (le : LookupEval F) (inputExprs tableExprs : List (Expr F))
    (fixedEvals adviceEvals instanceEvals : ℕ → F) (theta beta gamma l0 lLast lBlind : F) : List F :=
  let active := 1 - (lLast + lBlind)
  let left := le.productNextEval * (le.permutedInputEval + beta) * (le.permutedTableEval + gamma)
  let right := le.productEval
    * (compressExprs fixedEvals adviceEvals instanceEvals theta inputExprs + beta)
    * (compressExprs fixedEvals adviceEvals instanceEvals theta tableExprs + gamma)
  [ l0 * (1 - le.productEval),
    lLast * (le.productEval ^ 2 - le.productEval),
    (left - right) * active,
    l0 * (le.permutedInputEval - le.permutedTableEval),
    (le.permutedInputEval - le.permutedTableEval) * (le.permutedInputEval - le.permutedInputInvEval)
      * active ]

/-- `expected_h_eval` (halo2 `vanishing/verifier.rs` `verify`): fold all constraint values by `y`
(`acc·y + v`) and divide by `xⁿ − 1`. The verifier opens the folded `h` commitment to this value. -/
def expectedHEval {F : Type*} [Field F] (exprs : List F) (y xn : F) : F :=
  (exprs.foldl (fun acc v => acc * y + v) (0 : F)) * (xn - 1)⁻¹

end Zcash.Snark
