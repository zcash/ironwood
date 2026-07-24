import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.LookupAssembly

/-!
# What the capstone's satisfaction predicate actually says

`circuitSatViaConstraints` is the capstone's notion of circuit satisfaction over the whole
constraint list. On its own that is just a polynomial identity. These theorems say what it buys:
the identity *is* the hypothesis the row-level results consume, so a witness satisfying it satisfies
the permutation argument's copy constraints and the lookup argument's inclusion.

That closes the loop. The capstone hands over `SnarkRelation … circuitSatViaConstraints`
(`snarkRelation_constraints`), and these read the two arguments' relations back out of it.
-/

namespace Zcash.Snark

open Polynomial Finset

open Finset in
/-- **The circuit's declared equalities, read out of the capstone's predicate.** Circuit
satisfaction over the full constraint list gives the permutation argument's conclusion: cells the
circuit's copy constraints force equal do hold equal values — across every chunk, for any number of
sub-proofs. -/
theorem declared_equalities_of_circuitSat
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ) {nc m : ℕ} (hnc : 0 < nc)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {kk np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ kk) → Fp) → Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n : ℕ} (hn : n ≠ 0) (p : Fin np)
    (a : Fin (2 ^ kk) → Fp)
    (hsets : sets p = deployedPermSets omega nc z lastP)
    (hchunks : chunks p = deployedPermChunks omega nc z lastP cols)
    (cs : List (((c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length)
      × ((c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length)))
    (hsat : circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates sets chunks
      lookups beta gamma delta theta y chunkLen l0P lLastP lBlindP hpoly n a)
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols
      (decodeAdvice a) (decodeInstance a) gates sets chunks lookups
      beta gamma delta theta chunkLen l0P lLastP lBlindP) n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ m) ≠ 0)
    (hlastEval : ∀ c, c + 1 < nc → ((lastP c).getD 0).eval (omega ^ 0) = (z c).eval (omega ^ m))
    (hσ : ∀ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
      chunkSigma omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
        = chunkName omega delta chunkLen ((PermConstruction.build cs cell).1 : ℕ)
            ((PermConstruction.build cs cell).2.1 : ℕ)
            ((PermConstruction.build cs cell).2.2 : ℕ))
    (hnm : Function.Injective
      fun cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length =>
        chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols)).map (fun q => q.1 + q.2 * beta))
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols))
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen))).coeff j))
    {x w : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length}
    (hxw : Relation.EqvGen (fun a b => (a, b) ∈ cs) x w) :
    chunkValue omega cols (x.1 : ℕ) (x.2.1 : ℕ) (x.2.2 : ℕ)
        = chunkValue omega cols (w.1 : ℕ) (w.2.1 : ℕ) (w.2.2 : ℕ)
      ∨ ∃ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
          chunkValue omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + beta * chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + gamma = 0 :=
  deployed_declared_equalities_of_identity_chunks omega beta gamma delta theta y chunkLen hnc z
    lastP cols fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks lookups
    l0P lLastP lBlindP hpoly hn p hsets hchunks cs hsat hgoodY hrow hactive hl0 hlast hlastEval
    hσ hnm hgoodγ hgoodβ hxw

open Finset in
/-- **The lookup relation, read out of the capstone's predicate.** The same satisfaction predicate
gives the lookup argument's conclusion: every input value appears in the table. -/
theorem lookup_relation_of_circuitSat (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (zP aP sP : Polynomial Fp) (inputExprs tableExprs : List (Expr Fp))
    {kk np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n m : ℕ} (hn : n ≠ 0) (p : Fin np)
    (a : Fin (2 ^ kk) → Fp) (homega : omega ≠ 0)
    (hlk : (lookupEvalPolys omega zP aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hsat : circuitSatViaConstraints fixedCols (fun _ => adviceCols) (fun _ => instanceCols) gates
      sets chunks lookups beta gamma delta theta y chunkLen l0P lLastP lBlindP hpoly n a)
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m + 1, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ (m + 1)) ≠ 0)
    (hgoodγ : gamma ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).map (evalRingHom beta)))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).coeff j))
    (i : Fin (m + 1)) :
    (∃ j : Fin (m + 1),
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))
          = (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ (j : ℕ)))
    ∨ ∃ t ∈ range (m + 1), ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ t) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ t) + gamma) = 0 :=
  deployed_lookup_relation_of_identity omega beta gamma delta theta y chunkLen zP aP sP inputExprs
    tableExprs fixedCols adviceCols instanceCols gates sets chunks lookups l0P lLastP lBlindP hpoly
    hn p homega hlk hsat hgoodY hrow hactive hl0 hlast hgoodγ hgoodβ i


open Finset in
/-- **The tuple-level lookup, read out of the capstone's predicate.** With `θ` outside each row
pair's collision root set, the same satisfaction predicate gives membership of whole rows: every
input row of the lookup appears as a table row. This is the form a circuit's table statement
consumes. -/
theorem lookup_tuple_of_circuitSat (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (zP aP sP : Polynomial Fp) (inputExprs tableExprs : List (Expr Fp))
    {kk np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n m : ℕ} (hn : n ≠ 0) (p : Fin np)
    (a : Fin (2 ^ kk) → Fp) (homega : omega ≠ 0)
    (harity : inputExprs.length = tableExprs.length)
    (hlk : (lookupEvalPolys omega zP aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hsat : circuitSatViaConstraints fixedCols (fun _ => adviceCols) (fun _ => instanceCols) gates
      sets chunks lookups beta gamma delta theta y chunkLen l0P lLastP lBlindP hpoly n a)
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m + 1, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ (m + 1)) ≠ 0)
    (hgoodγ : gamma ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).map (evalRingHom beta)))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).coeff j))
    (hgoodθ : ∀ i j : Fin (m + 1), theta ∉ szBadSet
      (foldPoly (rowTuple fixedCols (adviceCols p) (instanceCols p) omega inputExprs (i : ℕ))
        - foldPoly (rowTuple fixedCols (adviceCols p) (instanceCols p) omega tableExprs (j : ℕ))))
    (i : Fin (m + 1)) :
    (∃ j : Fin (m + 1),
        rowTuple fixedCols (adviceCols p) (instanceCols p) omega inputExprs (i : ℕ)
          = rowTuple fixedCols (adviceCols p) (instanceCols p) omega tableExprs (j : ℕ))
    ∨ ∃ t ∈ range (m + 1), ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ t) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ t) + gamma) = 0 :=
  deployed_lookup_tuple_of_identity omega beta gamma delta theta y chunkLen zP aP sP inputExprs
    tableExprs fixedCols adviceCols instanceCols gates sets chunks lookups l0P lLastP lBlindP hpoly
    hn p homega harity hlk hsat hgoodY hrow hactive hl0 hlast hgoodγ hgoodβ hgoodθ i

end Zcash.Snark
