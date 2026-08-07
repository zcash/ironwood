import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Common.Expr
import Zcash.Snark.Core.ProofString

/-!
# The vanishing argument's `expected_h_eval`

The vanishing check confirms the quotient identity `h(x) · (xⁿ − 1) = Σ gates + Σ permutation + Σ lookup`
at the evaluation point: the verifier recomputes the right-hand side from the claimed evaluations and
divides by `xⁿ − 1` to get the value `expected_h_eval` it opens the folded `h` commitment to (halo2
`plonk/verifier.rs` `expressions` + `vanishing/verifier.rs` `verify`). This module transcribes that
recomputation:

* `Expr` / `Expr.eval` — the gate-polynomial AST and its evaluation at the claimed evals, from
  the shared leaf `Zcash/Common/Expr.lean` (also the target of the circuit-side VK-match
  projection, `Zcash.Circuits.Fixtures`).
* `permutationExpressions` — the permutation argument's constraint values (`permutation/verifier.rs`).
* `lookupExpressions` — the lookup argument's constraint values (`lookup/verifier.rs`).
* `expectedHEval` — fold all constraint values by `y` and divide by `xⁿ − 1`.

The gate polynomials, the permutation column/eval layout, and the lookup input/table expressions are
VK-fixed circuit data, supplied as inputs.
-/

namespace Zcash.Snark

/-- Compress a list of expressions by `theta` (halo2 lookup `compress_expressions`):
`(((e₀)·θ + e₁)·θ + …)`. -/
def compressExprs {F : Type*} [CommRing F] (fixedEvals adviceEvals instanceEvals : ℕ → F)
    (theta : F) (exprs : List (Expr F)) : F :=
  exprs.foldl (fun acc e => acc * theta + e.eval fixedEvals adviceEvals instanceEvals) (0 : F)

/-- Evaluating a gate expression commutes with a ring hom: the AST is built from constants, column
queries, and ring operations, so pushing `f` to the leaves gives the same value. -/
theorem Expr.eval_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (fixedEvals adviceEvals instanceEvals : ℕ → F) (e : Expr F) :
    f (e.eval fixedEvals adviceEvals instanceEvals)
      = (e.map f).eval (fun i => f (fixedEvals i)) (fun i => f (adviceEvals i))
          (fun i => f (instanceEvals i)) := by
  induction e with
  | constant c => simp [Expr.eval, Expr.map]
  | fixed i => simp [Expr.eval, Expr.map]
  | advice i => simp [Expr.eval, Expr.map]
  | «instance» i => simp [Expr.eval, Expr.map]
  | negated e ih => simp [Expr.eval, Expr.map, ih]
  | sum a b iha ihb => simp [Expr.eval, Expr.map, iha, ihb]
  | product a b iha ihb => simp [Expr.eval, Expr.map, iha, ihb]
  | scaled e c ih => simp [Expr.eval, Expr.map, ih]

/-- A `y`-fold of ring elements commutes with a ring hom. -/
theorem RingHom.map_foldByY {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G) (y : F)
    (l : List F) (init : F) :
    f (l.foldl (fun acc v => acc * y + v) init)
      = (l.map f).foldl (fun acc v => acc * f y + v) (f init) := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih, map_add, map_mul]

/-- Compressing a list of gate expressions by `theta` commutes with a ring hom. -/
theorem compressExprs_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (fixedEvals adviceEvals instanceEvals : ℕ → F) (theta : F) (exprs : List (Expr F)) :
    f (compressExprs fixedEvals adviceEvals instanceEvals theta exprs)
      = compressExprs (fun i => f (fixedEvals i)) (fun i => f (adviceEvals i))
          (fun i => f (instanceEvals i)) (f theta) (exprs.map (Expr.map f)) := by
  unfold compressExprs
  suffices h : ∀ (l : List (Expr F)) (init : F),
      f (l.foldl (fun acc e => acc * theta + e.eval fixedEvals adviceEvals instanceEvals) init)
        = (l.map (Expr.map f)).foldl
            (fun acc e => acc * f theta + e.eval (fun i => f (fixedEvals i))
              (fun i => f (adviceEvals i)) (fun i => f (instanceEvals i))) (f init) by
    simpa using h exprs 0
  intro l
  induction l with
  | nil => intro init; simp
  | cons a t ih => intro init; simp [ih, map_add, map_mul, Expr.eval_map f]

/-- Both folds inside `permChunkExpression` commute with a ring hom. -/
theorem permChunk_left_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (beta gamma : F) (pairs : List (F × F)) (init : F) :
    f (pairs.foldl (fun acc p => acc * (p.1 + beta * p.2 + gamma)) init)
      = (pairs.map (fun p => (f p.1, f p.2))).foldl
          (fun acc p => acc * (p.1 + f beta * p.2 + f gamma)) (f init) := by
  induction pairs generalizing init with
  | nil => simp
  | cons a t ih => simp [ih, map_add, map_mul]

theorem permChunk_right_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (gamma delta : F) (pairs : List (F × F)) :
    ∀ init : F × F,
      f ((pairs.foldl (fun acc p => (acc.1 * (p.1 + acc.2 + gamma), acc.2 * delta)) init).1)
        = ((pairs.map (fun p => (f p.1, f p.2))).foldl
            (fun acc p => (acc.1 * (p.1 + acc.2 + f gamma), acc.2 * f delta))
            (f init.1, f init.2)).1 := by
  induction pairs with
  | nil => intro init; simp
  | cons a t ih =>
      intro init
      simpa [map_add, map_mul] using
        ih (init.1 * (a.1 + init.2 + gamma), init.2 * delta)

/-- One chunk's step of the permutation argument's running product `z` (halo2
`permutation/verifier.rs`): moving down one row, `z` multiplies in each column's factor
`value + β·name + γ` under the column's own cell name and divides out the same factor under the
name `σ` assigns it. Over the whole table the two must cancel — the multiset identity that
`Soundness/Argument/Permutation.lean` turns into the copy constraints. Switched off on the
last/blinding rows. -/
def permChunkExpression {F : Type*} [CommRing F] (beta gamma x delta : F) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval F) (pairs : List (F × F)) (lLast lBlind : F) : F :=
  let left := pairs.foldl (fun acc p => acc * (p.1 + beta * p.2 + gamma)) set.nextEval
  let deltaStart := beta * x * delta ^ (chunkIndex * chunkLen)
  let right := (pairs.foldl (fun (acc : F × F) p => (acc.1 * (p.1 + acc.2 + gamma), acc.2 * delta))
    (set.eval, deltaStart)).1
  (left - right) * (1 - (lLast + lBlind))

/-- The step rule's left fold is a running product: each column contributes
`value + β·permutation + γ`, on top of the running product at the next row. -/
theorem permChunk_left_eq_prod {F : Type*} [CommRing F] (beta gamma : F) (pairs : List (F × F))
    (init : F) :
    pairs.foldl (fun acc p => acc * (p.1 + beta * p.2 + gamma)) init
      = init * ∏ j ∈ Finset.range pairs.length,
          ((pairs.getD j (0, 0)).1 + beta * (pairs.getD j (0, 0)).2 + gamma) := by
  induction pairs generalizing init with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, ih, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      ring_nf

/-- The step rule's right fold is the same running product with the columns named by their
`δ`-coset position: column `j` of chunk `c` carries the name `d₀·δ^j`, where `d₀` already holds the
chunk's offset `β·x·δ^{c·chunkLen}`. -/
theorem permChunk_right_eq_prod {F : Type*} [CommRing F] (gamma delta : F) (pairs : List (F × F))
    (init d₀ : F) :
    (pairs.foldl (fun (acc : F × F) p => (acc.1 * (p.1 + acc.2 + gamma), acc.2 * delta))
        (init, d₀)).1
      = init * ∏ j ∈ Finset.range pairs.length,
          ((pairs.getD j (0, 0)).1 + d₀ * delta ^ j + gamma) := by
  induction pairs generalizing init d₀ with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, ih, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
      ring_nf

/-- **The step rule is a one-row recurrence.** `permChunkExpression` vanishes exactly when the
running product at the next row times the `σ`-named factors equals the running product at this row
times the identity-named factors — or the row is switched off. This is the shape the telescoping
consumes. -/
theorem permChunkExpression_eq {F : Type*} [CommRing F] (beta gamma x delta : F)
    (chunkLen chunkIndex : ℕ) (set : PermSetEval F) (pairs : List (F × F)) (lLast lBlind : F) :
    permChunkExpression beta gamma x delta chunkLen chunkIndex set pairs lLast lBlind
      = (set.nextEval * ∏ j ∈ Finset.range pairs.length,
            ((pairs.getD j (0, 0)).1 + beta * (pairs.getD j (0, 0)).2 + gamma)
          - set.eval * ∏ j ∈ Finset.range pairs.length,
            ((pairs.getD j (0, 0)).1
              + beta * x * delta ^ (chunkIndex * chunkLen) * delta ^ j + gamma))
        * (1 - (lLast + lBlind)) := by
  simp only [permChunkExpression, permChunk_left_eq_prod, permChunk_right_eq_prod]

/-- The permutation argument's constraint values (halo2 `permutation/verifier.rs` `expressions`):
the running product must start at `1` and end at `0` or `1`, consecutive sets must chain (each
set's start equals the previous set's end), and every chunk must satisfy the step rule
(`permChunkExpression`). `chunks` pairs each set with its `(columnEval, permEval)` list. -/
def permutationExpressions {F : Type*} [CommRing F] (sets : List (PermSetEval F))
    (chunks : List (PermSetEval F × List (F × F))) (beta gamma x delta : F) (chunkLen : ℕ)
    (l0 lLast lBlind : F) : List F :=
  (match sets.head? with | some first => [l0 * (1 - first.eval)] | none => [])
  ++ (match sets.getLast? with | some last => [(last.eval ^ 2 - last.eval) * lLast] | none => [])
  ++ ((sets.drop 1).zip sets).map (fun p => (p.1.eval - p.2.lastEval.getD 0) * l0)
  ++ ((List.range chunks.length).zip chunks).map
      (fun p => permChunkExpression beta gamma x delta chunkLen p.1 p.2.1 p.2.2 lLast lBlind)

/-- The lookup argument's constraint values (halo2 `lookup/verifier.rs` `expressions`): the running
product must start at `1` and end at `0` or `1`; its step multiplies in the compressed input/table
factors and divides out the permuted columns' `(a'+β)·(s'+γ)`; and the permuted columns must
satisfy the two run-structure rules that `Soundness/Lookup.run_structure` consumes as hypotheses.
`active = 1 − (l_last + l_blind)` switches rules off on the last/blinding rows. -/
def lookupExpressions {F : Type*} [CommRing F] (le : LookupEval F) (inputExprs tableExprs : List (Expr F))
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

/-- `permChunkExpression` commutes with a ring hom: both interior folds do
(`permChunk_left_map`/`permChunk_right_map`) and the rest is ring arithmetic. -/
theorem permChunkExpression_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (beta gamma x delta : F) (chunkLen chunkIndex : ℕ) (set : PermSetEval F)
    (pairs : List (F × F)) (lLast lBlind : F) :
    f (permChunkExpression beta gamma x delta chunkLen chunkIndex set pairs lLast lBlind)
      = permChunkExpression (f beta) (f gamma) (f x) (f delta) chunkLen chunkIndex
          (set.map f) (pairs.map (fun p => (f p.1, f p.2))) (f lLast) (f lBlind) := by
  unfold permChunkExpression
  simp only [PermSetEval.map, map_sub, map_mul, map_add, map_one]
  rw [permChunk_left_map f beta gamma pairs set.nextEval,
    permChunk_right_map f gamma delta pairs (set.eval, beta * x * delta ^ (chunkIndex * chunkLen))]
  simp [map_mul, map_pow]

/-- The permutation constraint values commute with a ring hom: each of the four pieces is built
from the set evaluations by ring operations, and the chunk terms by `permChunkExpression_map`. -/
theorem permutationExpressions_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) :
    (permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind).map f
      = permutationExpressions (sets.map (PermSetEval.map f))
          (chunks.map (fun c => (c.1.map f, c.2.map (fun p => (f p.1, f p.2)))))
          (f beta) (f gamma) (f x) (f delta) chunkLen (f l0) (f lLast) (f lBlind) := by
  unfold permutationExpressions
  simp only [List.map_append]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_
  · cases sets <;> simp [PermSetEval.map, map_mul, map_sub, map_one]
  · rcases h : sets.getLast? with _ | last <;>
      simp [List.getLast?_map, h, PermSetEval.map, map_mul, map_sub, map_pow]
  · rw [← List.map_drop, List.zip_map, List.map_map, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    obtain ⟨a, b⟩ := p
    cases hb : b.lastEval <;> simp [PermSetEval.map, hb, map_sub, map_mul]
  · rw [List.length_map, List.zip_map_right, List.map_map, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp [permChunkExpression_map f]

/-- The lookup constraint values commute with a ring hom: the compressed input/table terms by
`compressExprs_map`, the rest by ring arithmetic on the lookup evaluations. -/
theorem lookupExpressions_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (le : LookupEval F) (inputExprs tableExprs : List (Expr F))
    (fixedEvals adviceEvals instanceEvals : ℕ → F) (theta beta gamma l0 lLast lBlind : F) :
    (lookupExpressions le inputExprs tableExprs fixedEvals adviceEvals instanceEvals
        theta beta gamma l0 lLast lBlind).map f
      = lookupExpressions (le.map f) (inputExprs.map (Expr.map f)) (tableExprs.map (Expr.map f))
          (fun i => f (fixedEvals i)) (fun i => f (adviceEvals i)) (fun i => f (instanceEvals i))
          (f theta) (f beta) (f gamma) (f l0) (f lLast) (f lBlind) := by
  unfold lookupExpressions
  simp [LookupEval.map, map_add, map_sub, map_mul, map_one, map_pow, compressExprs_map f]

/-- All constraint values for one sub-proof over any commutative ring (halo2 `plonk/verifier.rs`,
the per-proof `flat_map`): the gate values, then the permutation-argument values, then the
lookup-argument values. The verifier instantiates this at its claimed evaluations; the soundness
proof instantiates the same builder one level up, at column polynomials. -/
def subProofConstraints {F : Type*} [CommRing F] (fixedFeed adviceFeed instanceFeed : ℕ → F)
    (gates : List (Expr F)) (sets : List (PermSetEval F))
    (chunks : List (PermSetEval F × List (F × F)))
    (lookups : List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) : List F :=
  gates.map (fun g => g.eval fixedFeed adviceFeed instanceFeed)
  ++ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind
  ++ (lookups.map (fun lk => lookupExpressions lk.1 lk.2.1 lk.2.2 fixedFeed adviceFeed instanceFeed
      theta beta gamma l0 lLast lBlind)).flatten

/-- The whole constraint list commutes with a ring hom. Building the constraints over polynomials and
then evaluating at a point gives exactly the verifier's list at that point's evaluations — this is
what makes the polynomial and value levels agree term by term rather than only after the `y` fold. -/
theorem subProofConstraints_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G)
    (fixedFeed adviceFeed instanceFeed : ℕ → F) (gates : List (Expr F))
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (lookups : List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) :
    (subProofConstraints fixedFeed adviceFeed instanceFeed gates sets chunks lookups
        beta gamma x delta theta chunkLen l0 lLast lBlind).map f
      = subProofConstraints (fun i => f (fixedFeed i)) (fun i => f (adviceFeed i))
          (fun i => f (instanceFeed i)) (gates.map (Expr.map f)) (sets.map (PermSetEval.map f))
          (chunks.map (fun c => (c.1.map f, c.2.map (fun q => (f q.1, f q.2)))))
          (lookups.map (fun lk =>
            (lk.1.map f, lk.2.1.map (Expr.map f), lk.2.2.map (Expr.map f))))
          (f beta) (f gamma) (f x) (f delta) (f theta) chunkLen (f l0) (f lLast) (f lBlind) := by
  unfold subProofConstraints
  simp only [List.map_append, List.map_flatten, List.map_map]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ (permutationExpressions_map f ..)) ?_
  · exact List.map_congr_left fun g _ => Expr.eval_map f _ _ _ g
  · exact congrArg List.flatten (List.map_congr_left fun lk _ => lookupExpressions_map f ..)

/-- The rule chaining chunk `c` to chunk `c + 1` is one of the permutation constraint values: the
next chunk's running product starts where this one's ended. -/
theorem chain_mem_permutationExpressions {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {c : ℕ} (hc : c + 1 < sets.length) :
    (sets[c + 1].eval - sets[c].lastEval.getD 0) * l0
      ∈ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  unfold permutationExpressions
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨(sets[c + 1], sets[c]), ?_, rfl⟩))))
  have hlen : ((sets.drop 1).zip sets).length = sets.length - 1 := by
    simp [List.length_zip]
  refine List.mem_iff_getElem.mpr ⟨c, by rw [hlen]; omega, ?_⟩
  rw [List.getElem_zip, List.getElem_drop]
  simp [Nat.add_comm]

/-- The lookup rules, written out: start, end, the step rule, the row-0 equality, and the
run-structure rule. -/
theorem lookupExpressions_eq {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixedEvals adviceEvals instanceEvals : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    lookupExpressions le inputExprs tableExprs fixedEvals adviceEvals instanceEvals
        theta beta gamma l0 lLast lBlind
      = [ l0 * (1 - le.productEval),
          lLast * (le.productEval ^ 2 - le.productEval),
          (le.productNextEval * (le.permutedInputEval + beta) * (le.permutedTableEval + gamma)
            - le.productEval
              * (compressExprs fixedEvals adviceEvals instanceEvals theta inputExprs + beta)
              * (compressExprs fixedEvals adviceEvals instanceEvals theta tableExprs + gamma))
            * (1 - (lLast + lBlind)),
          l0 * (le.permutedInputEval - le.permutedTableEval),
          (le.permutedInputEval - le.permutedTableEval)
            * (le.permutedInputEval - le.permutedInputInvEval) * (1 - (lLast + lBlind)) ] := rfl

/-- A lookup constraint value is one of the sub-proof's constraint values. -/
theorem mem_subProofConstraints_of_mem_lookupExpressions {F : Type*} [CommRing F]
    (fixedFeed adviceFeed instanceFeed : ℕ → F) (gates : List (Expr F))
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (lookups : List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {lk : LookupEval F × List (Expr F) × List (Expr F)} (hlk : lk ∈ lookups) {v : F}
    (h : v ∈ lookupExpressions lk.1 lk.2.1 lk.2.2 fixedFeed adviceFeed instanceFeed
      theta beta gamma l0 lLast lBlind) :
    v ∈ subProofConstraints fixedFeed adviceFeed instanceFeed gates sets chunks lookups
        beta gamma x delta theta chunkLen l0 lLast lBlind := by
  unfold subProofConstraints
  exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨lk, hlk, rfl⟩, h⟩))

/-! ## Locating a single constraint in the list

The soundness argument needs one constraint at a time — the step rule for a chunk, the rule pinning
the running product at the first row — but the verifier hands over one flat list. These lemmas place
each rule inside that list, so a fact proved about the whole list transfers to the rule. -/

/-- The step rule for chunk `c` is one of the permutation constraint values. -/
theorem permChunkExpression_mem_permutationExpressions {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {c : ℕ} (hc : c < chunks.length) :
    permChunkExpression beta gamma x delta chunkLen c (chunks[c].1) (chunks[c].2) lLast lBlind
      ∈ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  unfold permutationExpressions
  refine List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(c, chunks[c]), ?_, rfl⟩))
  have hlen : ((List.range chunks.length).zip chunks).length = chunks.length := by
    simp [List.length_zip]
  refine List.mem_iff_getElem.mpr ⟨c, by rw [hlen]; exact hc, ?_⟩
  rw [List.getElem_zip]
  simp

/-- The rule pinning the running product at the first row is one of the permutation constraint
values. -/
theorem start_mem_permutationExpressions {F : Type*} [CommRing F]
    {sets : List (PermSetEval F)} (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {first : PermSetEval F} (hhead : sets.head? = some first) :
    l0 * (1 - first.eval)
      ∈ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  unfold permutationExpressions
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl ?_)))))
  rw [hhead]
  simp

/-- The rule pinning the running product at the last row is one of the permutation constraint
values. -/
theorem end_mem_permutationExpressions {F : Type*} [CommRing F]
    {sets : List (PermSetEval F)} (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {last : PermSetEval F} (hlast : sets.getLast? = some last) :
    (last.eval ^ 2 - last.eval) * lLast
      ∈ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  unfold permutationExpressions
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr ?_)))))
  rw [hlast]
  simp

/-- Every constraint value across the sub-proofs, in the verifier's order. The fixed columns, the
gates and the challenge-derived scalars are shared; the advice and instance evaluations, the
permutation sets and the lookups vary per sub-proof. -/
def allConstraints {F : Type*} [CommRing F] {np : ℕ} (fixedFeed : ℕ → F)
    (adviceFeed instanceFeed : Fin np → ℕ → F) (gates : List (Expr F))
    (sets : Fin np → List (PermSetEval F))
    (chunks : Fin np → List (PermSetEval F × List (F × F)))
    (lookups : Fin np → List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) : List F :=
  (List.ofFn (fun p : Fin np =>
    subProofConstraints fixedFeed (adviceFeed p) (instanceFeed p) gates (sets p) (chunks p)
      (lookups p) beta gamma x delta theta chunkLen l0 lLast lBlind)).flatten

/-- The whole constraint list, across all sub-proofs, commutes with a ring hom. -/
theorem allConstraints_map {F G : Type*} [CommRing F] [CommRing G] (f : F →+* G) {np : ℕ}
    (fixedFeed : ℕ → F) (adviceFeed instanceFeed : Fin np → ℕ → F) (gates : List (Expr F))
    (sets : Fin np → List (PermSetEval F))
    (chunks : Fin np → List (PermSetEval F × List (F × F)))
    (lookups : Fin np → List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) :
    (allConstraints fixedFeed adviceFeed instanceFeed gates sets chunks lookups
        beta gamma x delta theta chunkLen l0 lLast lBlind).map f
      = allConstraints (fun i => f (fixedFeed i)) (fun p i => f (adviceFeed p i))
          (fun p i => f (instanceFeed p i)) (gates.map (Expr.map f))
          (fun p => (sets p).map (PermSetEval.map f))
          (fun p => (chunks p).map (fun c => (c.1.map f, c.2.map (fun q => (f q.1, f q.2)))))
          (fun p => (lookups p).map (fun lk =>
            (lk.1.map f, lk.2.1.map (Expr.map f), lk.2.2.map (Expr.map f))))
          (f beta) (f gamma) (f x) (f delta) (f theta) chunkLen (f l0) (f lLast) (f lBlind) := by
  unfold allConstraints
  rw [List.map_flatten, List.map_ofFn]
  simp only [Function.comp_def]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun p => ?_))
  exact subProofConstraints_map f ..

/-- A permutation constraint value is one of the sub-proof's constraint values. -/
theorem mem_subProofConstraints_of_mem_permutationExpressions {F : Type*} [CommRing F]
    (fixedFeed adviceFeed instanceFeed : ℕ → F) (gates : List (Expr F))
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (lookups : List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) {v : F}
    (h : v ∈ permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind) :
    v ∈ subProofConstraints fixedFeed adviceFeed instanceFeed gates sets chunks lookups
        beta gamma x delta theta chunkLen l0 lLast lBlind := by
  unfold subProofConstraints
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

/-- A sub-proof's constraint value is one of the whole list's. -/
theorem mem_allConstraints_of_mem_subProofConstraints {F : Type*} [CommRing F] {np : ℕ}
    (fixedFeed : ℕ → F) (adviceFeed instanceFeed : Fin np → ℕ → F) (gates : List (Expr F))
    (sets : Fin np → List (PermSetEval F))
    (chunks : Fin np → List (PermSetEval F × List (F × F)))
    (lookups : Fin np → List (LookupEval F × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F) (chunkLen : ℕ) (l0 lLast lBlind : F) (p : Fin np) {v : F}
    (h : v ∈ subProofConstraints fixedFeed (adviceFeed p) (instanceFeed p) gates (sets p)
      (chunks p) (lookups p) beta gamma x delta theta chunkLen l0 lLast lBlind) :
    v ∈ allConstraints fixedFeed adviceFeed instanceFeed gates sets chunks lookups
        beta gamma x delta theta chunkLen l0 lLast lBlind := by
  unfold allConstraints
  exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, h⟩

/-- `expected_h_eval` (halo2 `vanishing/verifier.rs` `verify`): fold all constraint values by `y`
(`acc·y + v`) and divide by `xⁿ − 1`. The verifier opens the folded `h` commitment to this value. -/
def expectedHEval {F : Type*} [Field F] (exprs : List F) (y xn : F) : F :=
  (exprs.foldl (fun acc v => acc * y + v) (0 : F)) * (xn - 1)⁻¹

end Zcash.Snark
