import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction

/-!
# The budgeted deployed capstone and the budgeted computed path

The derived capstone (`Soundness.Vesta`) quantifies its extraction floors over every splice run;
the budgeted extraction (`Multiopen.BudgetedExtraction`) needs one joint accept floor. This module
joins them:

* `orchard_verifier_vesta_member_constraint_budgeted` — the capstone with its seven run-quantified
  floor premises replaced by one joint floor `t₁ + (t₂ + t₃ + t₄) < μ(memberJointAccept)`, plus
  sample avoidance at the canonical runs only.
* `member_relation_or_dlr_of_instance_budgeted` and companions — the computed path routed through
  it: the member decode is *constructed* (`openedMemberDecode_of_x1Prob`) and `hquot` *derived*
  (`quotientCheck_of_claimed`), so neither is a hypothesis. What remain are acceptance, the two
  accept floors, sample avoidance, the gate surfaces `hfold`/`hgood`, and the layout identities.

The layout/committed-quotient identities are the halo2 faithfulness boundary — the VK's declared
layout is the circuit's real column structure — and are fail-safe, not silently satisfiable: each
demands a `getD` value whose default is a different `CommitmentId` constructor, so a mismatched
layout makes the premise false, never vacuously true. The `x₁` floor `hprob1` follows from the
joint floor but stays named, because the statement's decode terms carry its proof.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against (`Soundness.Composition.Bridge`
-- and `Forking.Adversary.Algebraic` use the same concrete `Inhabited VestaG`); a binder would be a
-- different instance term, forcing the `multiopenCommitment` fold through `whnf`. Named to avoid an
-- auto-generated-name collision on co-import.
local instance vestaInhabitedVestaBudget : Inhabited VestaG := ⟨0⟩

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Budgeted deployed member capstone: the floor family priced by one joint accept floor.** The
conclusion of the derived capstone — the gate check at `ch.x` on the decoded member columns, the
claimed evaluations derived and `hquot` produced — from a single joint accept floor per point set,
`t₁(i) + (t₂ + t₃ + t₄) < μ(memberJointAccept)`, in place of seven run-quantified floors. The floor
is the whole multiopen-side premise: `t₃` carries a `+ |allPts|` collision summand that buys the
interpolation samples off the opened set points, so no sample-avoidance hypothesis is taken (see
`Multiopen.BudgetedExtraction`).

Named assumptions: `hacc0` (acceptance), `hprob1` (the honest-base `x₁` floor, feeding the member
decode), `hJ` (the joint floor), `hfold` (the gate fold at the deployed claimed
evaluations), `hgood` (Schwartz–Zippel at the *fixed* `ch.x`), the layout identities, the
committed-quotient identity, `hencodes`.

`hgood` is irreducible at the fixed `ch.x` — the decoded columns are pinned at `ch.x`'s rotation
points, so the check cannot move to a resampled challenge without re-running the value binding —
but its failure over the `x`-squeeze is priced (`hgood_failure_priced`), and `hfold` decomposes
into the vanishing-slot binding, `ch.x^vk.n ≠ 1`, and the fold fingerprint; see the `hfold`/`hgood`
section note at the end of this file. -/
theorem orchard_verifier_vesta_member_constraint_budgeted {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval (fun n => (fixedCols n).eval ch.x)
          (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval ch.x * (ch.x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  -- derive `hadvice`: the rotated advice feed's value at `ch.x` is the deployed claimed eval
  have hadvice : ∀ n, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
          (adviceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout n := by
    intro n
    by_cases h : n < numAdvice
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := advice_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hadvLen ⟨n, h⟩).1 (hadvLen ⟨n, h⟩).2
      have hltm : ((adviceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (adviceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).getD ((adviceMem ⟨n, h⟩ : ℕ))
          CommitmentId.vanishingH = q.commId := (hadviceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)
        (hadviceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet ⟨n, h⟩)
          (hadviceSet ⟨n, h⟩) (hlen _ (hadviceSet ⟨n, h⟩)) (hprob1 _ (hadviceSet ⟨n, h⟩)) hacc0)
        b₂f (hJ _ (hadviceSet ⟨n, h⟩)) hpt (adviceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- derive `hinstance` symmetrically
  have hinstance : ∀ n, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout n := by
    intro n
    by_cases h : n < numInstance
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := instance_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hinstLen ⟨n, h⟩).1 (hinstLen ⟨n, h⟩).2
      have hltm : ((instanceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (instanceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).getD
          ((instanceMem ⟨n, h⟩ : ℕ)) CommitmentId.vanishingH = q.commId :=
        (hinstanceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)
        (hinstanceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet ⟨n, h⟩)
          (hinstanceSet ⟨n, h⟩) (hlen _ (hinstanceSet ⟨n, h⟩)) (hprob1 _ (hinstanceSet ⟨n, h⟩))
          hacc0)
        b₂f (hJ _ (hinstanceSet ⟨n, h⟩)) hpt (instanceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- the gate check at the deployed opening challenge, from the derived claimed evaluations
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk instanceCommitment ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg ch.x
    pbatch hξcur hlen hprob1 hacc0
    (quotientCheck_of_claimed fixedCols _ _ y gates hpoly deg ch.x
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout)
      (fun _ => rfl) hadvice hinstance hfold)
    hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The budgeted witness tie on the computed path.** `member_relation_or_dlr_of_instance`
(`Soundness.Composition.Bridge`) with the member decode *constructed* and `hquot` *derived*: on the
agreement branch the budgeted deployed capstone runs at the algebraic instance's base
`(p.proof.1, chRecord ν)`; on the disagreement branch the two openings of the shared commitment
collide into a computed `(g, u, w)` relation. No `mdec`/`hquot` hypothesis remains — the measure
premises are the honest-base `x₁` floor and the joint accept floor. -/
theorem member_relation_or_dlr_of_instance_budgeted
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  by_cases hae : o.1 = a₀
  · exact orchard_verifier_vesta_member_constraint_budgeted (ursOfAugmentedBasis shape.k basis)
      rfl vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (p.multiU ν) (p.multiBlind ν)
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
      hpoly deg pbatch hξcur hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ hfold hgood
      hadviceLayout hinstanceLayout hquotCommitted hencodes
  · exact Or.inr (hasNontrivialRelation_of_two_openings (ursOfAugmentedBasis shape.k basis) hae
      ((opening_commit_deployed_of_instance p ν cert hz hvalid o).trans
        (pbatch.ipaRelation_of_x4Current hξcur).1.symm))

open Polynomial in
open scoped ENNReal in
open Classical in
/-- The budgeted `runToSnark`-analogue on the computed path: `member_snark_of_instance`
(`Soundness.Composition.Bridge`) with the clean-opening branch routed through the budgeted witness tie, so
no member decode or quotient identity is hypothesised. On the clean-opening branch the budgeted
capstone produces the member SNARK relation (or a binding `HasNontrivialRelation`); on the
relation branch, the algebraic extraction's own `AlgebraicRelationWitness`. -/
noncomputable def member_snark_of_instance_budgeted
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  match (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run with
  | PSum.inl o =>
      PSum.inl (member_relation_or_dlr_of_instance_budgeted p ν cert hz hvalid o pbatch hξcur
        adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
        hpoly deg hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ hfold hgood
        hadviceLayout hinstanceLayout hquotCommitted hencodes)
  | PSum.inr rel => PSum.inr rel

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed soundness on the computed path, extraction data derived.** The budgeted counterpart
of `orchard_verifier_sound_vesta_computed` (`Soundness.Composition.Bridge`): the same
`KnowledgeSoundness.SnarkRelation`-based `S` / `HasNontrivialRelation` / `AlgebraicRelationWitness`
trichotomy, but with the member decode constructed and the quotient identity derived — no
`mdec`/`hquot` hypothesis. What remains hypothesised: the deployed acceptance `hacc0`, the two
accept-measure floors (`hprob1` and the joint floor `hJ`), canonical-run sample avoidance, the
fingerprint surfaces `hfold`/`hgood`, the layout identities, the committed-quotient identity, and
the batch `pbatch` itself (an `x₄`-rewind output; producing it from bare acceptance is the open
composition surface recorded in `Soundness.Multiopen.Decode`). -/
noncomputable def orchard_verifier_sound_vesta_budgeted
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ (a : Fin (2 ^ shape.k) → Fp)
        (bo : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
          (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0)))
          (x4BatchEvals vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) a (p.multiU ν) (p.multiBlind ν))
        (md : ∀ i (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))),
          OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0)) bo i hi),
      SnarkRelation (ursOfAugmentedBasis shape.k basis)
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
        (circuitSatViaGates fixedCols
          (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((md (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
          (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((md (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
          y gates hpoly deg) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  member_snark_of_instance_budgeted p ν cert hz hvalid pbatch hξcur adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg hlen hprob1 hacc0 pp
    hadvLen hinstLen b₂f hJ hfold hgood hadviceLayout hinstanceLayout hquotCommitted
    (S := S)
    (fun a hmem => hencodes a hmem.batchOpenings hmem.memberDecode
      (snarkRelation_of_memberColumns hmem))

/-! ## The clean-opening extraction hand-off

`hasCleanOpening` (`Forking.Adversary.Algebraic`) packages an instance the computed family
produced together with its clean-opening branch. `instanceAttempt_provenance`
(`Soundness.Composition.Bridge`) exposes the `AlgebraicWfProof` behind that instance, and the budgeted
witness tie above turns the opening into the member SNARK relation given the multiopen rewind
data. The two theorems below chain these: the extraction *logic* of the conditional
knowledge-error bound's `hExtract` hypothesis is discharged, leaving a data-supply obligation
that receives the concrete proof, oracle scalars, and opening.

What remains for a fully unconditional bound is the *coupling*: the supply's inputs — the batch
`pbatch` and the accept floors `hprob1`/`hJ` — are outputs of the multiopen challenge draw, which
the family's coin space does not range over. `deployed_member_budget`
(`Soundness.Multiopen.BudgetedExtraction`) prices exactly that draw's failure event at
`t₁ + (t₂ + t₃ + t₄)`; joining it to the family bound needs a product space over
(oracle coins × the four fresh challenges) and a measure statement relating the two draws — a
genuine probabilistic modeling step, not a composition of what exists. -/

/-- A clean opening's provenance: the produced instance is a `deployedAlgebraicInstanceOfCert` of
a concrete `AlgebraicWfProof`, oracle scalars, and certificate, and its run took the clean-opening
branch. `hasCleanOpening` unpacked through `instanceAttempt_provenance`. -/
theorem cleanOpening_provenance (family : ComputedAlgebraicFSFamily shape)
    (coins : family.Coins) (h : family.hasCleanOpening basis coins) :
    ∃ (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k basis)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
          (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
          (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
        cert.toDForkCert),
      (family.instanceAttempt basis coins).output
          = some (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) ∧
      ∃ o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening,
        (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run = PSum.inl o := by
  obtain ⟨x, hout, o, hrun⟩ := h
  obtain ⟨p, ν, cert, hz, hvalid, hx⟩ := instanceAttempt_provenance family coins hout
  subst hx
  exact ⟨p, ν, cert, hz, hvalid, hout, o, hrun⟩

open scoped ENNReal in
open ComputedAlgebraicFSFamily in
/-- **The knowledge-error bound with the extraction logic discharged.** The conditional bound with
`hExtract` reduced through the clean-opening provenance: the supply obligation receives the
concrete proof, oracle scalars, certificate, and clean opening behind each produced instance —
exactly the inputs of the budgeted witness tie, which concludes the extraction given the multiopen
rewind data. The bound is the clean-opening bound, verbatim; the residual is the coin–challenge
coupling recorded in this section's note. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_budgeted {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (hSupply : ∀ (bs : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins)
      (p : AlgebraicWfProof bs (family.vk bs) (family.instanceCommitment bs)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k bs).g
          (ursOfAugmentedBasis shape.k bs).u (ursOfAugmentedBasis shape.k bs).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k bs).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k bs).u
        (ursOfAugmentedBasis shape.k bs).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k bs)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk bs) (family.instanceCommitment bs) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
          (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k bs).u +
          (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k bs).w)
        cert.toDForkCert),
      (family.instanceAttempt bs coins).output
          = some (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) →
      ∀ o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening,
        (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run = PSum.inl o →
        extracted bs coins) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound :=
  snarkExtraction_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL extracted
    (fun bs coins h => by
      obtain ⟨p, ν, cert, hz, hvalid, hout, o, hrun⟩ := cleanOpening_provenance family coins h
      exact hSupply bs coins p ν cert hz hvalid hout o hrun)

/-! ## The `hfold`/`hgood` surfaces: derivation core and price

The two gate-check surfaces of the budgeted capstone decompose further; neither is an opaque
assumption.

* **`hfold` is a value binding, not a check the verifier skips.** The deployed verifier computes
  halo2's `expected_h_eval` — the `ch.y`-fold of `allExpressions` divided by `ch.x^vk.n − 1` — and
  pins the vanishing-`h` opening query at exactly that value. The grouping routes that query to a
  member whose point list is `[ch.x]` and whose eval list is `[expectedHEval …]`
  (`vanishing_slot_routed`); binding `hpoly.eval ch.x` to it gives the capstone's `hfold` equation
  (`hfold_of_vanishing_slot_binding`, `hfold_of_member_budget`). Its inputs are settled: `hxn`
  follows from acceptance (`deployedAccepts_xn_ne_one`), `hbind` from the good branch of
  `deployed_member_budget`, and `hfp` is proved outright on the full constraint list
  (`hfold_of_constraint_polys`) — the permutation and lookup arguments are part of the model, so
  the two folds are two runs of the same code rather than an assumed correspondence.

* **`hgood`'s failure is Schwartz–Zippel-priced.** For the capstone's difference polynomial the
  failure event of the exact `hgood` implication has uniform-squeeze measure at most
  `max (deg numerator) (deg hpoly + deg) / p` (`hgood_failure_priced`), and every challenge
  outside the bad set satisfies the implication verbatim (`hgood_of_good_challenge`). The two
  hooks a probabilistic assembly must supply are the same random-oracle coupling the joint accept
  floor carries: that `ch.x` is one fresh uniform squeeze, and that the difference polynomial is
  pinned before `x` is squeezed (`adviceCommitments_mem_preXTranscript` /
  `hPieces_mem_preXTranscript`, `Soundness.Forking.Ordering`).

* **Every other challenge surface carries the same shape of price**
  (`Soundness.ChallengePricing`): the fold split's `y` (`goodY_failure_measure_le`,
  `≤ n·length/p`), the multiset bridge's `γ` and `β` (`perm_gamma_failure_measure_le`,
  `perm_beta_failure_measure_le`), the vanishing-factor escapes (`escape_measure_le`), and the
  tuple decompression's pairwise `θ` (`theta_failure_measure_le`). Each is a per-challenge
  uniform measure bound with its data pinned in the transcript before that challenge is squeezed
  (θ after the advice commitments, β and γ after θ, `y` after the lookup commitments, `x` last).
  Composing them into the terminal error is the same single coupling hook `hgood` awaits — the
  events live on different squeezes, so their joint bound needs exactly the sequential coupling
  above, once, for all of them. -/

/-- The vanishing-`h` opening query is a deployed opening query with its claimed evaluation
*computed* by the verifier: slot identity `vanishingH`, opening point `ch.x`, and evaluation
`expectedHEval` of the full claimed-evaluation expression list — the fact `hfold`'s derivation
consumes. (halo2 `plonk/verifier.rs`: the verifier recomputes `expected_h_eval` and queries the
`h` commitment at it; `assembleQueries` appends `vanishingQueries` last, so the query is the
head of that suffix.) -/
theorem vanishing_query_mem_assembleQueries {G : Type*} [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.vanishingH ∧ q.point = ch.x ∧
      q.eval = expectedHEval
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
        ch.y (ch.x ^ vk.n) := by
  refine ⟨{ point := ch.x,
            commitment := .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)),
            eval := expectedHEval
              (allExpressions vk ps ch
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
              ch.y (ch.x ^ vk.n),
            commId := .vanishingH }, ?_, rfl, rfl, rfl⟩
  simp only [assembleQueries, vanishingQueries]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_self))

/-- **The vanishing slot's routed member carries the verifier-computed evaluation.** The vanishing
query opens at `ch.x` with evaluation `expectedHEval …` (`vanishing_query_mem_assembleQueries`), no
other query carries its slot (`assembleQueries_vanishingH_unique`), so the grouping routes it to a
member of a single point set with `points i = [ch.x]`, identity `vanishingH`, and eval list
`[expectedHEval …]` (`constructIntermediateSets_unique_comm_routed`) — the eval-faithfulness fact
the `hfold` derivation reads. -/
theorem vanishing_slot_routed {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ i, i < (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length ∧
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x] ∧
      ∃ m, m < (deployedSetQueries vk instanceCommitment ps ch i).length ∧
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD m c₀ = CommitmentId.vanishingH) ∧
        ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
          = [expectedHEval
              (allExpressions vk ps ch
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
              ch.y (ch.x ^ vk.n)] := by
  obtain ⟨q, hq, hid, hpt, hev⟩ := vanishing_query_mem_assembleQueries vk instanceCommitment ps ch
  have huniq : ∀ q' ∈ assembleQueries vk instanceCommitment ps ch, q'.commId = q.commId → q' = q := by
    intro q' hq' hq'id
    exact assembleQueries_vanishingH_unique vk instanceCommitment ps ch hq' hq (hq'id.trans hid) hid
  obtain ⟨i, hi, hpts, m, hm, hids, hsets⟩ :=
    constructIntermediateSets_unique_comm_routed (assembleQueries vk instanceCommitment ps ch) hq huniq
  refine ⟨i, hi, by rw [hpts, hpt], m, ?_, ?_, ?_⟩
  · simp only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
    exact hm
  · intro c₀
    simp only [deployedSetCommIds]
    rw [hids c₀]
    exact hid
  · intro d₀
    simp only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
    rw [hsets d₀, hev]

/-- **The `hfold` derivation core.** The capstone's fold equation from the vanishing-slot value
binding: if the extracted quotient's evaluation at `ch.x` is the verifier-computed `expectedHEval`
(`hbind` — supplied by the member node binding at the `hquotCommitted` slot), the squeeze avoids the
`deg`-th roots of unity (`hxn`), and the constraint list folds to the same value as the deployed
expression list (`hfp` — the fingerprint, sharpened to one equation), then `hfold` holds verbatim.
Pure field algebra: `expectedHEval` clears its `(x^deg − 1)⁻¹` against `hxn`. The constraint list
stays abstract — the gates alone instantiate it, and so does the full gate / permutation / lookup
list (`eval_combineConstraints_deployed`), which discharges `hfp`. -/
theorem hfold_of_expectedHEval_binding (constraints : List Fp) (y x : Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (exprs : List Fp)
    (hxn : x ^ deg ≠ 1)
    (hbind : hpoly.eval x = expectedHEval exprs y (x ^ deg))
    (hfp : constraints.foldl (fun acc v => acc * y + v) 0
        = exprs.foldl (fun acc v => acc * y + v) 0) :
    constraints.foldl (fun acc v => acc * y + v) 0 = hpoly.eval x * (x ^ deg - 1) := by
  rw [hfp, hbind, expectedHEval, mul_assoc,
    inv_mul_cancel₀ (sub_ne_zero.mpr hxn), mul_one]

/-- Acceptance excludes the roots of unity: `assemble?` returns `none` at `ch.x ^ vk.n = 1` (the
deployed verifier panics there; the model renders the panic as rejection), and `DeployedAccepts` is
`False` on the `none` branch. `hfold`'s side condition `hxn` therefore needs no squeeze budget. -/
theorem deployedAccepts_xn_ne_one {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) : ch.x ^ vk.n ≠ 1 := by
  intro hx
  have hnone : assemble? vk instanceCommitment ps ch = none := by
    unfold assemble?
    by_cases hwf : proofStringWellFormed ps = true
    · rw [if_pos hwf, if_pos hx]
    · rw [if_neg hwf]
  unfold DeployedAccepts at hacc
  rw [hnone] at hacc
  exact hacc

/-- **The `hfold` derivation, reading the routed vanishing-slot value.**
`hfold_of_expectedHEval_binding` with its `hbind` premise supplied through the grouping: the member
node binding at the `hquotCommitted` slot pins `hpoly.eval ch.x` to the value the grouping recorded
for the vanishing member, and `vanishing_slot_routed` says that value *is* the verifier-computed
`expectedHEval`. The two standing side conditions are unchanged and explicit: root-of-unity
avoidance `hxn` (a `vk.n / p`-priced squeeze exclusion) and the sharpened expression-fold fingerprint `hfp`. -/
theorem hfold_of_vanishing_slot_binding {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (constraints : List Fp)
    (hpoly : Polynomial Fp) (i m : ℕ)
    (hrouted : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hbind : hpoly.eval ch.x
      = ((deployedSetQueries vk instanceCommitment ps ch i).getD m (CommitmentRef.point 0, [])).2.getD 0 0)
    (hxn : ch.x ^ vk.n ≠ 1)
    (hfp : constraints.foldl (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    constraints.foldl (fun acc v => acc * ch.y + v) 0
      = hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
  refine hfold_of_expectedHEval_binding constraints ch.y ch.x hpoly vk.n _ hxn ?_ hfp
  rw [hbind, hrouted (CommitmentRef.point 0, [])]
  rfl

/-- **`hfold` from the budget's good branch.** `deployed_member_budget` ends in a disjunction:
*either* the joint accept measure sits inside the four-threshold budget, *or* every decoded member
column takes its claimed evaluation (or a `(g, u, w)` relation is at hand). Consuming the second
branch (`hbindAll`) at the slot `vanishing_slot_routed` names — point list `[ch.x]` (`hroute`), eval
list `[expectedHEval …]` (`hevals`), so the index-`0` binding is a binding at `ch.x` — gives the
capstone's `hfold` equation or the relation. Acceptance supplies the root-of-unity exclusion; the
one remaining input is the expression-fold fingerprint `hfp`. `hquot` names the extracted quotient
as the routed member's own column, not an arbitrary member recording the `vanishingH` identity. -/
theorem hfold_of_member_budget {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (constraints : List Fp)
    (hpoly : Polynomial Fp) (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
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
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hlt : 0 < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length := by
    rw [hroute]; simp
  rcases hbindAll ⟨0, hlt⟩ ⟨m, hm⟩ with hb | hrel
  · refine Or.inl (hfold_of_vanishing_slot_binding vk instanceCommitment ps ch constraints hpoly i m
      hevals ?_ (deployedAccepts_xn_ne_one urs hk vk instanceCommitment ps ch hacc) hfp)
    have hx : ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
        [])[(0 : ℕ)]'hlt
        = ch.x := by
      rw [List.getElem_of_eq hroute hlt]
      simp
    rw [hquot, ← hx]
    exact hb
  · exact Or.inr hrel

open Polynomial in
/-- **`hfold`, with the fingerprint discharged.** `hfold_of_member_budget` run on the full
constraint list — gates, permutation argument and lookup argument together — instead of an abstract
gate family. That list is the evaluation of the constraint *polynomials* at `ch.x`, so the
fingerprint premise is no longer assumed: `eval_combineConstraints_deployed` proves it from the node
binding alone.

Named assumptions: `hfixed`/`hadvice`/`hinstance` — the fed columns take the claimed evaluations at
`ch.x`; `hsets`/`hchunks`/`hlookups` — the permutation sets, chunks and lookups do the same;
`hl0`/`hlLast`/`hlBlind` — the Lagrange polynomials take the verifier's Lagrange values;
`hbindAll`/`hquot`/`hroute`/`hevals`/`hacc` — unchanged from `hfold_of_member_budget`. -/
theorem hfold_of_constraint_polys {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin shape.numProofs → ℕ → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin shape.numProofs →
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (hpoly : Polynomial Fp) (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
              [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ)
              (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
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
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hfp := eval_combineConstraints_deployed vk ps ch fixedCols adviceCols instanceCols
    sets chunks lookups l0 lLast lBlind hfixed hadvice hinstance hsets hchunks hlookups
    hl0 hlLast hlBlind
  rw [eval_combineConstraints] at hfp ⊢
  exact hfold_of_member_budget urs hk vk instanceCommitment ps ch _ hpoly i m hm colPoly hbindAll
    hquot hroute hevals hacc hfp

open Polynomial in
open scoped ENNReal in
/-- **The `hgood` failure event, Schwartz–Zippel-priced.** The set of squeezes at which the
budgeted capstone's exact `hgood` implication *fails* — the gate identity fails as polynomials
yet its difference vanishes at the squeeze — is the difference's root set, of uniform measure at
most `max (deg numerator) (deg hq + n) / p` (the caller-computable budget of
`szBadSet_quotient_card_le`). The assembly hooks (that `ch.x` is one fresh uniform squeeze and
the difference is pinned pre-squeeze) are recorded in this section's note. -/
theorem hgood_failure_priced (numerator hq : Polynomial Fp) (n : ℕ) :
    uniformChallenge.toOuterMeasure
        {x : Fp | ¬(numerator ≠ hq * (X ^ n - 1) →
          (numerator - hq * (X ^ n - 1)).eval x ≠ 0)}
      ≤ ((max numerator.natDegree (hq.natDegree + n) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞) := by
  have hset : {x : Fp | ¬(numerator ≠ hq * (X ^ n - 1) →
        (numerator - hq * (X ^ n - 1)).eval x ≠ 0)}
      = ↑(szBadSet (numerator - hq * (X ^ n - 1))) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_szBadSet, Classical.not_imp, not_not,
      sub_ne_zero]
  rw [hset, uniformChallenge_badSet]
  gcongr
  exact_mod_cast szBadSet_quotient_card_le numerator hq n

open Polynomial in
/-- Any squeeze outside the priced bad set satisfies the budgeted capstone's `hgood` implication
verbatim (`not_mem_szBadSet` at the quotient difference). -/
theorem hgood_of_good_challenge (numerator hq : Polynomial Fp) (n : ℕ) {x : Fp}
    (hx : x ∉ szBadSet (numerator - hq * (X ^ n - 1))) :
    numerator ≠ hq * (X ^ n - 1) → (numerator - hq * (X ^ n - 1)).eval x ≠ 0 :=
  fun hne => (not_mem_szBadSet.mp hx) (sub_ne_zero.mpr hne)

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The budgeted member capstone with `hfold` derived.** The capstone at the deployed
instantiation (`y := ch.y`, `deg := vk.n`, forced by `hy`/`hdeg`), its `hfold` premise supplied by
`hfold_of_member_budget`: that lemma is generic in the constraint list, so it instantiates at this
capstone's gate fold over its own `deployedClaimedFeed`s, and its relation branch merges into the
capstone's `HasNontrivialRelation` disjunct. In place of `hfold` the caller supplies the routed
vanishing-slot data (`hroute`/`hevals`, from `vanishing_slot_routed`), the budget's good branch
(`hbindAll`), the routed quotient (`hquot`), and the fingerprint (`hfp`); the root-of-unity
exclusion is read off `hacc0`. Instantiating the same lemma at the full constraint list instead
proves `hfp` rather than assuming it (`hfold_of_constraint_polys`). `hgood` remains a premise —
priced (`hgood_failure_priced`), but its pricing hook needs the adaptive coupling (the standing
gap in `Soundness.Composition.Prefixes`). Superseded for deployed use: the gate-only fold cannot
match the committed quotient, which absorbs the permutation and lookup terms — use the
constraint-carrying capstones at the end of this file. -/
theorem orchard_verifier_vesta_member_constraint_budgeted_hfold_derived {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S)
    (hy : y = ch.y) (hdeg : deg = vk.n)
    (i m : ℕ) (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hfp : (List.ofFn (fun j : Fin ng =>
          (gates j).eval (fun n => (fixedCols n).eval ch.x)
            (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
            (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
            (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst hy
  subst hdeg
  rcases hfold_of_member_budget urs hk vk instanceCommitment ps ch
      (List.ofFn (fun j : Fin ng => (gates j).eval (fun n => (fixedCols n).eval ch.x)
        (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
        (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem
          vk.instanceQueryLayout)))
      hpoly i m hm colPoly hbindAll hquot hroute hevals hacc0 hfp with hfold | hrel
  · exact orchard_verifier_vesta_member_constraint_budgeted urs hk vk instanceCommitment ps ch pU pW adviceSet
      hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols ch.y gates hpoly vk.n
      pbatch hξcur hlen hprob1 hacc0 p hadvLen hinstLen b₂f hJ hfold hgood
      hadviceLayout hinstanceLayout hquotCommitted hencodes
  · exact Or.inr hrel


/-! ## The member relation over the full constraint system

`SnarkRelationWithMemberColumns` carries the gate check on the decoded member columns. The twin
below carries satisfaction of the whole constraint list — gates, permutation argument and lookup
argument — over the same decoded columns and the same witness chain. The chain enters the assembly
as hypotheses, so nothing probabilistic is re-derived: the deployed capstone family gains a member
whose conclusion mentions the two arguments. -/

variable {G : Type*}

open Polynomial in
/-- The member-column SNARK relation over the full constraint system: the witness chain of
`SnarkRelationWithMemberColumns`, with circuit satisfaction stated by `circuitSatViaConstraints`
on the decoded member columns instead of the gate check alone. -/
structure SnarkRelationWithMemberConstraints [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp) (p : Fin shape.numProofs)
    {numAdvice numInstance np : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp) where
  opens : IpaRelation urs P b v a
  batchOpenings : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    (x4BatchEvals vk instanceCommitment ps ch) a pU pW
  /-- Advice selection is forced by the verifying key's query layout, as in the gate relation. -/
  adviceLayout : ∀ j : Fin numAdvice,
    (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
      = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1
  /-- Instance selection is likewise forced by the layout. -/
  instanceLayout : ∀ j : Fin numInstance,
    (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
      = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1
  memberDecode : ∀ i (hi : i < deployedX4PairCount vk instanceCommitment ps ch),
    OpenedMemberDecode urs hk vk instanceCommitment ps ch batchOpenings i hi
  /-- The quotient is the committed vanishing-`h` polynomial, as in the gate relation. -/
  quotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
      (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
    hpoly = coeffsToPoly ((memberDecode hSet hhSet).cols hMem) ∧
    (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
      = CommitmentId.vanishingH
  /-- **The whole constraint system is satisfied** — gates, permutation and lookup arguments — on
  the decoded member columns. -/
  satisfiesCircuit :
    circuitSatViaConstraints fixedCols
      (fun _ _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
        coeffsToPoly ((memberDecode (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
      (fun _ _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
        coeffsToPoly ((memberDecode (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
      gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg a

open Polynomial in
/-- The constraint-carrying member relation projects onto the plain `SnarkRelation` at
`circuitSat := circuitSatViaConstraints …` on the decoded member columns: its `opens` field is the
IPA opening and its `satisfiesCircuit` field is exactly the constraint identity. -/
theorem SnarkRelationWithMemberConstraints.toSnarkRelation [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {p : Fin shape.numProofs}
    {numAdvice numInstance np : ℕ}
    {adviceSet : Fin numAdvice → ℕ}
    {hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch}
    {adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length}
    {instanceSet : Fin numInstance → ℕ}
    {hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch}
    {instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length}
    {fixedCols : ℕ → Polynomial Fp} {gates : List (Expr Fp)}
    {sets : Fin np → List (PermSetEval (Polynomial Fp))}
    {chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp))}
    {lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp))}
    {beta gamma delta theta y : Fp} {chunkLen : ℕ} {l0 lLast lBlind : Polynomial Fp}
    {hpoly : Polynomial Fp} {deg : ℕ} {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hmem : SnarkRelationWithMemberConstraints urs hk vk instanceCommitment ps ch P b v p adviceSet hadviceSet
      adviceMem instanceSet hinstanceSet instanceMem fixedCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg pU pW a) :
    SnarkRelation urs P b v
      (circuitSatViaConstraints fixedCols
        (fun _ _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((hmem.memberDecode (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (fun _ _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((hmem.memberDecode (instanceSet j) (hinstanceSet j)).cols
            (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg) a :=
  ⟨hmem.opens, hmem.satisfiesCircuit⟩

open Polynomial in
/-- Turn a final opened relation, its batch family, and per-set member decodes into the
constraint-carrying member relation: the twin of `member_constraint_of_relation_and_batch` with the
whole constraint list in place of the gates. -/
theorem member_constraints_of_relation_and_batch [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numAdvice numInstance np : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a pU pW)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk instanceCommitment ps ch),
      OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (hquotC : quotientCheck
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind) hpoly deg x)
    (hgoodC :
      combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          ≠ hpoly * (X ^ deg - 1) →
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberConstraints urs hk vk instanceCommitment ps ch P b v p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg pU pW a → S) :
    S := by
  have hsat := circuitSatViaConstraints_of_check fixedCols
    (fun _ _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
    (fun _ _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
    gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg a x
    hquotC hgoodC
  exact hencodes a
    { opens := hrel
      batchOpenings := pbatch
      memberDecode := mdec
      adviceLayout := hadviceLayout
      instanceLayout := hinstanceLayout
      quotCommitted := hquotCommitted
      satisfiesCircuit := hsat }


open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed member capstone over the full constraint system.** The twin of
`orchard_verifier_vesta_member_constraint_deployed_x4`: same witness chain — the batch family's
opening and the constructed member decodes — with the constraint check in place of the gate check,
so the deployed endpoint now asserts the gates, permutation and lookup arguments together. -/
theorem orchard_verifier_vesta_member_constraints_deployed_x4 {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance np : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hquotC : quotientCheck
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind) hpoly deg x)
    (hgoodC :
      combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          ≠ hpoly * (X ^ deg - 1) →
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberConstraints urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  Or.inl (member_constraints_of_relation_and_batch urs hk vk instanceCommitment ps ch adviceSet hadviceSet
    adviceMem instanceSet hinstanceSet instanceMem fixedCols gates sets chunks lookups
    beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg x
    (pbatch.ipaRelation_of_x4Current hξcur) pbatch
    (fun i hi => openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch i hi (hlen i hi)
      (hprob1 i hi) hacc0)
    hquotC hgoodC p hadviceLayout hinstanceLayout hquotCommitted hencodes)

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The deployed terminal at the constraint predicate.** The capstone payload handed over is
`SnarkRelation` at `circuitSatViaConstraints` on the decoded member columns — the opening the
batch family already carries, paired with satisfaction of the whole constraint system. This is
the endpoint the circuit bridge composes with. -/
theorem orchard_verifier_vesta_member_constraints_terminal {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance np : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hquotC : quotientCheck
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind) hpoly deg x)
    (hgoodC :
      combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          ≠ hpoly * (X ^ deg - 1) →
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
        (circuitSatViaConstraints fixedCols
          (fun _ _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
              (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
                (adviceMem j))))
          (fun _ _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
              (hinstanceSet j) (hlen _ (hinstanceSet j))
              (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
          gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg)
        a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  Or.inl (hencodes a₀
    ⟨pbatch.ipaRelation_of_x4Current hξcur,
      circuitSatViaConstraints_of_check fixedCols _ _ gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg a₀ x hquotC hgoodC⟩)


open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The constraint terminal with `hquotC` and `hgoodC` derived.** The conditional split: given
the feed and carrier bindings at `ch.x` and a squeeze outside the constraint numerator's bad set,
the quotient check over the full constraint list follows from the vanishing-slot binding
(`hfold_of_constraint_polys`) and the good-challenge implication from `hgood_of_good_challenge` —
so the capstone hands over `SnarkRelation` at `circuitSatViaConstraints` with no assumed check.
Producing these bindings and the good squeeze from acceptance, with their failure probabilities
composed, is the computed-path re-instantiation. -/
theorem orchard_verifier_vesta_member_constraints_terminal_derived {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin shape.numProofs →
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP : Polynomial Fp) (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (i m : ℕ) (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hfixed : ∀ j, (fixedCols j).eval ch.x = finFn ps.fixedEvals j)
    (hadviceBind : ∀ (q : Fin shape.numProofs) j,
      ((rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))) j).eval ch.x)
        = finFn (ps.adviceEvals q) j)
    (hinstanceBind : ∀ (q : Fin shape.numProofs) j,
      ((rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))) j).eval ch.x)
        = finFn (ps.instanceEvals q) j)
    (hsets : ∀ q, (sets q).map (PermSetEval.map (fun r => r.eval ch.x)) = subProofPermSets ps q)
    (hchunks : ∀ q, (chunks q).map (fun c => (c.1.map (fun r => r.eval ch.x),
        c.2.map (fun r => (r.1.eval ch.x, r.2.eval ch.x)))) = subProofPermChunks vk ps q)
    (hlookups : ∀ q, (lookups q).map
        (fun lk => (lk.1.map (fun r => r.eval ch.x), lk.2.1, lk.2.2)) = subProofLookups vk ps q)
    (hl0 : l0P.eval ch.x = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1)
    (hlLast : lLastP.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1)
    (hlBlind : lBlindP.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
    (hxgood : ch.x ∉ szBadSet
      (combineConstraints fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        vk.gates sets chunks lookups ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
        l0P lLastP lBlindP - hpoly * (X ^ vk.n - 1)))
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
        (circuitSatViaConstraints fixedCols
          (fun _ _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
              (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
                (adviceMem j))))
          (fun _ _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
              (hinstanceSet j) (hlen _ (hinstanceSet j))
              (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
          vk.gates sets chunks lookups ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          l0P lLastP lBlindP hpoly vk.n)
        a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases hfold_of_constraint_polys urs hk vk instanceCommitment ps ch fixedCols
      (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
        coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
          (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
            (adviceMem j))))
      (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
        coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
          (hinstanceSet j) (hlen _ (hinstanceSet j))
          (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
      sets chunks lookups l0P lLastP lBlindP hpoly i m hm colPoly hbindAll hquot hroute hevals
      hacc0 hfixed hadviceBind hinstanceBind hsets hchunks hlookups hl0 hlLast hlBlind
    with hfold | hrel
  · exact orchard_verifier_vesta_member_constraints_terminal urs hk vk instanceCommitment ps ch pU pW adviceSet
      hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols vk.gates sets chunks
      lookups ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0P lLastP lBlindP hpoly vk.n
      ch.x pbatch hξcur hlen hprob1 hacc0 hfold
      (hgood_of_good_challenge _ hpoly vk.n hxgood) hencodes
  · exact Or.inr hrel

end Zcash.Snark
