import Zcash.Circuits.Integration.ActionPermutationCycle
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Snark.Soundness.ChallengePricing

/-!
# Action copy witness from verifier permutation semantics

This module is the final copy-family composition. Canonical constraint
satisfaction, the generated Action σ cycle, and bundle-wide good permutation
challenges give equal values on every keygen copy pair. Fixed-column provenance
handles allocated constants, after which `ActionCopyWitness` constructs the
complete Clean copy witness.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open ActionPermutationDomain
open Zcash.Circuits.Action (actionCircuit)

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

/--
Construct the complete Action copy witness for one proof from the accepted
canonical relation, or retain the shared augmented-commitment relation branch.
-/
def actionCopyReplayWitness_or_relation
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : (actionShape pp).k = urs.k)
    {instanceCommitment :
      Fin (actionShape pp).numProofs → ℕ → G}
    {ps : ProofString (actionShape pp) Fp G}
    {ch : Challenges (actionShape pp).k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk (actionVk pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          (actionVk pp urs) ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          (actionVk pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk (actionVk pp urs) ps ch batchOpenings i hi}
    {y : Fp} {hpoly : CPoly}
    (relation : CanonicalMemberConstraintRelation
      urs hk (actionVk pp urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (blindingFactors_lt pp urs) y hpoly (actionVk pp urs).n)
    (hgoodY : ∀ j,
      y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          (actionVk pp urs).n j))
    (fixedCoherence :
      TopLevelFixedCoherence actionCircuit pp urs)
    (exclusions : ResolverPermutationChallengeExclusions
      (actionVk pp urs) ch relation.polynomial actionActiveRows)
    (proofIndex : Fin (actionShape pp).numProofs) :
    CopyReplayWitness actionCircuit.placement
        (resolverEnvironment
          (actionVk pp urs) relation.polynomial proofIndex
            actionActiveRows)
        (actionCircuit.operations)
        (FlatCell actionNumPermCols actionDomainSize)
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hn : (actionVk pp urs).n ≠ 0 := by
    change 2 ^ actionCircuit.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY
  have hdomain : ResolverPermutationDomain
      (actionVk pp urs)
      relation.model.l0 relation.model.lLast relation.model.lBlind
      (actionVk pp urs).n actionActiveRows := by
    simpa only [actionActiveRows, TopLevelCircuit.usableRowsAt] using
      ActionPermutationDomain.domain
        pp urs ch relation.polynomial
  have hcycleResult :=
    actionResolverPermutationCycle_or_relation
      pp urs hk relation proofIndex
  rcases hcycleResult with hcycle | hbad
  swap
  · exact PSum.inr hbad
  · let cycle := hcycle.1
    have hcycleSigma := hcycle.2
    have hpairval :=
      actionCopyPairValue_of_resolverPermutation
        pp urs ch relation.polynomial
        relation.model.l0 relation.model.lLast relation.model.lBlind
        proofIndex hsatisfaction hdomain cycle hcycleSigma
        (exclusions.good proofIndex)
    have hdomainSize :
        (actionVk pp urs).n = 2 ^ urs.k := by
      change
        2 ^ actionCircuit.domainExponent = 2 ^ urs.k
      exact congrArg (2 ^ ·) hk
    have hfixedRead : ∀ {column row value : ℕ},
        (column, row, value) ∈
            topLevelRequiredFixedEntries actionCircuit →
          (resolverEnvironment
            (actionVk pp urs) relation.polynomial proofIndex
              actionActiveRows).fixed
              ⟨column⟩ (row : ℤ) = (value : Fp) ⊕'
            NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
      intro column row value hentry
      have source :=
        relation.topLevelFixedEntryRead_or_relation
          rfl fixedCoherence
          (actionRowsInjectiveAtUrs pp urs hk)
          hdomainSize proofIndex hentry
      simpa only [actionActiveRows] using source
    exact
      actionCopyReplayWitness_ofPairValues_or_bad
        (resolverEnvironment
          (actionVk pp urs) relation.polynomial proofIndex
            actionActiveRows)
        (fun pair hpair => PSum.inl (hpairval pair hpair))
        hfixedRead

end Zcash.Snark
