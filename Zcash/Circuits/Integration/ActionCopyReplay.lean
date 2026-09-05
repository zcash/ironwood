import Zcash.Circuits.Integration.ActionPermutationCycle
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Snark.Soundness.Pricing.ChallengePricing

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

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Construct the complete Action copy witness for one proof from the accepted
canonical relation, or retain the shared augmented-commitment relation branch.
-/
def actionCopyReplayWitness_or_relation
    (pp : ProofParams) (urs : URS G)
    (hk : actionCircuit.domainExponent = urs.k)
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (actionShape pp) Fp G}
    {ch : Challenges actionCircuit.domainExponent Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := actionShape pp)
          (instanceCommitment := instanceCommitment)
          urs hk (actionCircuit.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := actionShape pp)
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey urs) ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := actionShape pp)
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := actionShape pp)
        (instanceCommitment := instanceCommitment)
        urs hk (actionCircuit.toVerifierKey urs) ps ch batchOpenings i hi}
    {y : Fp} {hpoly : CPoly}
    (relation : CanonicalMemberConstraintRelation
      (shape := actionShape pp)
      urs hk (actionCircuit.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        y hpoly actionCircuit.n)
    (hgoodY : ∀ j,
      y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          actionCircuit.n j))
    (fixedCoherence :
      TopLevelFixedCoherence actionCircuit urs)
    (exclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey urs) ch relation.polynomial actionActiveRows)
    (proofIndex : Fin pp.numProofs) :
    CopyReplayWitness actionCircuit.placement
        (resolverEnvironment
          (actionCircuit.toVerifierKey urs) relation.polynomial proofIndex
            actionActiveRows)
        (actionCircuit.operations)
        (FlatCell actionNumPermCols actionDomainSize)
        (AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hn : actionCircuit.n ≠ 0 :=
    actionCircuit.n_ne_zero
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY
  have hmodel :
      relation.model =
        actionCircuit.constraintModel pp urs ch relation.polynomial := by
    simp only [CanonicalMemberConstraintRelation.model]
    exact
      (actionCircuit.constraintModel_eq_toVerifierKey_constraintModel
        pp urs ch relation.polynomial).symm
  rw [hmodel] at hsatisfaction
  have hdomain : ResolverPermutationDomain
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.constraintModel pp urs ch relation.polynomial).l0
      (actionCircuit.constraintModel pp urs ch relation.polynomial).lLast
      (actionCircuit.constraintModel pp urs ch relation.polynomial).lBlind
      actionCircuit.n actionActiveRows := by
    simpa only [actionActiveRows] using
      actionCircuit.resolverPermutationDomain
        pp urs ch relation.polynomial ActionConstraintBounds.domainExponent_lt
  have hcycleResult :=
    actionResolverPermutationCycle_or_relation
      pp urs hk relation proofIndex
  rcases hcycleResult with hcycle | hbad
  swap
  · exact PSum.inr hbad
  · let cycle := hcycle.cycle
    have hcycleSigma := hcycle.sigma_eq
    have hpairval :=
      actionCopyPairValue_of_resolverPermutation
        pp urs ch relation.polynomial
        proofIndex hsatisfaction hdomain cycle hcycleSigma
        (exclusions.good proofIndex)
    have hdomainSize :
        actionCircuit.n = 2 ^ urs.k := by
      rw [actionCircuit.n_eq_two_pow_domainExponent, hk]
    have hfixedRead : ∀ {column row : ℕ} {value : Fp},
        (column, row, value) ∈
            topLevelRequiredFixedEntries actionCircuit →
          (resolverEnvironment
            (actionCircuit.toVerifierKey urs) relation.polynomial proofIndex
              actionActiveRows).fixed
              ⟨column⟩ (row : ℤ) = value ⊕'
            AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
      intro column row value hentry
      have source :=
        relation.topLevelFixedEntryRead_or_relation
          (top := actionCircuit) (pp := pp) (urs := urs)
          fixedCoherence
          (TopLevelAssignment.domainRowsInjective_of_domainExponent_eq
            ActionConstraintBounds.domainExponent_lt hk)
          hdomainSize proofIndex hentry
      simpa only [actionActiveRows] using source
    exact
      actionCopyReplayWitness_ofPairValues_or_bad
        (resolverEnvironment
          (actionCircuit.toVerifierKey urs) relation.polynomial proofIndex
            actionActiveRows)
        (fun pair hpair => PSum.inl (hpairval pair hpair))
        hfixedRead

end Zcash.Snark
