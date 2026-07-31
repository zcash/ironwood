import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.ConstraintCore
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# The routed vanishing-slot fold, carrying its break as data

Upstream replaced the budgeted capstone lane wholesale with the rewind-free AGM route and deleted
`Soundness.VestaBudget` with it. Two declarations from that file are still consumed by the
canonical quotient terminal and have no upstream counterpart in this shape: main's
`AGM.DeployedConstraintSupply.hfold_of_constraint_polys_of_xn_ne_direct` is *relation-free* —
there the break branch is discharged ahead of the fold by the AGM decode rather than threaded
through it as `hbindAll`, so it is not a drop-in for a caller that does thread it.

They are kept here unchanged apart from carrying `⊕' NontrivialRelation` in place of the vacuous
`∨ HasNontrivialRelation`, so the terminal keeps building across the merge. Retiring this module
in favour of the AGM route is follow-up work; it is a change to how the terminal obtains its
premises, not a repair to this fold.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

/-- **`hfold` from the budget's good branch.** `deployed_member_budget` ends in a disjunction:
*either* the joint accept measure sits inside the four-threshold budget, *or* every decoded member
column takes its claimed evaluation (or a `(g, u, w)` relation is at hand). Consuming the second
branch (`hbindAll`) at the slot `vanishing_slot_routed` names — point list `[ch.x]` (`hroute`), eval
list `[expectedHEval …]` (`hevals`), so the index-`0` binding is a binding at `ch.x` — gives the
capstone's `hfold` equation or the relation. Acceptance supplies the root-of-unity exclusion; the
one remaining input is the expression-fold fingerprint `hfp`. `hquot` names the extracted quotient
as the routed member's own column, not an arbitrary member recording the `vanishingH` identity. -/
def hfold_of_member_budget {G : Type*} [AddCommGroup G] [Module Fp G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (constraints : List Fp)
    (hpoly : CPoly) (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → CPoly)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hfp : constraints.foldl (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    constraints.foldl (fun acc v => acc * ch.y + v) 0
      = hpoly.eval ch.x * (ch.x ^ vk.n - 1)
    ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hlt : 0 < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length := by
    rw [hroute]; simp
  -- `hbindAll` is consumed at a single index, so no search is needed: the outcome threads through.
  refine bindOrRelationWitness (hbindAll ⟨0, hlt⟩ ⟨m, hm⟩) fun hb => ?_
  refine hfold_of_vanishing_slot_binding vk instanceCommitment ps ch constraints hpoly i m
    hevals ?_ (deployedAccepts_xn_ne_one urs hk vk instanceCommitment ps ch hacc) hfp
  have hx : ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
      [])[(0 : ℕ)]'hlt
      = ch.x := by
    rw [List.getElem_of_eq hroute hlt]
    simp
  rw [hquot, ← hx]
  exact hb

open CompPoly.CPolynomial in
/-- **`hfold`, with the fingerprint discharged.** `hfold_of_member_budget` run on the full
constraint list — gates, permutation argument and lookup argument together — instead of an abstract
gate family. That list is the evaluation of the constraint *polynomials* at `ch.x`, so the
fingerprint premise follows from `eval_combineConstraints_deployed` and the node
binding alone.

Named assumptions: `hfixed`/`hadvice`/`hinstance` — the fed columns take the claimed evaluations at
`ch.x`; `hsets`/`hchunks`/`hlookups` — the permutation sets, chunks and lookups do the same;
`hl0`/`hlLast`/`hlBlind` — the Lagrange polynomials take the verifier's Lagrange values;
`hbindAll`/`hquot`/`hroute`/`hevals`/`hacc` — unchanged from `hfold_of_member_budget`. -/
def hfold_of_constraint_polys {G : Type*} [AddCommGroup G] [Module Fp G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin shape.numProofs → ℕ → CPoly)
    (sets : Fin shape.numProofs → List (PermSetEval (CPoly)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin shape.numProofs →
      List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0 lLast lBlind : CPoly)
    (hpoly : CPoly) (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → CPoly)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
              [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ)
              (.point 0, [])).2.getD (idx : ℕ) 0
        ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
      [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hfixed : ∀ j, (fixedCols j).eval ch.x = finFn ps.fixedEvals j)
    (hadvice : ∀ p j, (adviceCols p j).eval ch.x = finFn (ps.adviceEvals p) j)
    (hinstance : ∀ p j, (instanceCols p j).eval ch.x = finFn (ps.instanceEvals p) j)
    (hsets : ∀ p, (sets p).map (PermSetEval.map (fun q => q.eval ch.x)) = subProofPermSets ps p)
    (hchunks : ∀ p, (chunks p).map (fun c => (c.1.map (fun q => q.eval ch.x),
        c.2.map (fun q => (q.1.eval ch.x, q.2.eval ch.x)))) = subProofPermChunks vk ps p)
    (hlookups : ∀ p, (lookups p).map (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p)
    (hl0 : l0.eval ch.x = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1)
    (hlLast : lLast.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1)
    (hlBlind : lBlind.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) :
    (combineConstraints fixedCols adviceCols instanceCols vk.gates sets chunks lookups
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0 lLast lBlind).eval ch.x
      = hpoly.eval ch.x * (ch.x ^ vk.n - 1)
    ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hfp := eval_combineConstraints_deployed vk ps ch fixedCols adviceCols instanceCols
    sets chunks lookups l0 lLast lBlind hfixed hadvice hinstance hsets hchunks hlookups
    hl0 hlLast hlBlind
  rw [eval_combineConstraints] at hfp ⊢
  exact hfold_of_member_budget urs hk vk instanceCommitment ps ch _ hpoly i m hm colPoly hbindAll
    hquot hroute hevals hacc hfp


end Zcash.Snark
