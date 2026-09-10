import Zcash.Circuits.Integration.PermutationCycle
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.CopyConstraints
import Zcash.Snark.Soundness.Pricing.ChallengePricing

/-!
# circuit copy constraints from verifier permutation semantics

This module is the final copy-family composition. Canonical constraint
satisfaction, the generated circuit σ cycle, and bundle-wide good permutation
challenges give equal values on every keygen copy pair. The generic raw-pair
adapter combines these with fixed-column reads of allocated constants to prove
Clean's copy constraints.
-/


namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open TopLevelCopy

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top] [CircuitFieldSupport top]

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Prove the circuit copy constraints for one proof from the accepted
canonical relation, or retain the shared augmented-commitment relation branch.
-/
def CanonicalMemberConstraintRelation.topLevelCopyConstraints_or_relation
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.domainExponent Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          urs hk (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := instanceCommitment)
        urs hk (top.toVerifierKey urs) ps ch batchOpenings i hi}
    {y : Fp} {hpoly : CPoly}
    (relation : CanonicalMemberConstraintRelation
      (shape := top.shape.withProofParams pp)
      urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs)
        y hpoly top.n)
    (hgoodY : ∀ j,
      y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          top.n j))
    (exclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch relation.polynomial (top.usableRowsAt top.domainExponent))
    (proofIndex : Fin pp.numProofs) :
    CircuitConstraintFamily.constraints .copy top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) relation.polynomial proofIndex
            (top.usableRowsAt top.domainExponent))
        top.operations 0 ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hn : top.n ≠ 0 :=
    top.n_ne_zero
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY
  have hmodel :
      relation.model =
        top.constraintModel pp urs ch relation.polynomial := by
    simp only [CanonicalMemberConstraintRelation.model]
    exact
      (top.constraintModel_eq_toVerifierKey_constraintModel
        pp urs ch relation.polynomial).symm
  rw [hmodel] at hsatisfaction
  have hdomain : ResolverPermutationDomain
      (top.toVerifierKey urs)
      (top.constraintModel pp urs ch relation.polynomial).l0
      (top.constraintModel pp urs ch relation.polynomial).lLast
      (top.constraintModel pp urs ch relation.polynomial).lBlind
      top.n (top.usableRowsAt top.domainExponent) := by
    exact top.resolverPermutationDomain
        pp urs ch relation.polynomial
  have hcycleResult :=
    (resolverPermutationCycle_or_relation top)
      pp urs hk relation proofIndex
  rcases hcycleResult with hcycle | hbad
  swap
  · exact PSum.inr hbad
  · let cycle := hcycle.cycle
    have hcycleSigma := hcycle.sigma_eq
    have hpairval :=
      (copyPairValue_of_resolverPermutation top)
        pp urs ch relation.polynomial
        proofIndex hsatisfaction hdomain cycle hcycleSigma
        (exclusions.good proofIndex)
    have hfixedRead : ∀ {column row : ℕ} {value : Fp},
        (column, row, value) ∈
            topLevelRequiredFixedEntries top →
          (resolverEnvironment
            (top.toVerifierKey urs) relation.polynomial proofIndex
              (top.usableRowsAt top.domainExponent)).fixed
              ⟨column⟩ (row : ℤ) = value ⊕'
            AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
      intro column row value hentry
      have source :=
        relation.topLevelFixedEntryRead_or_relation
          (top := top) (pp := pp) (urs := urs)
          proofIndex hentry
      exact source
    apply topLevelCopyConstraints_of_rawPairValues_or_bad top _ ?_ hfixedRead
    intro tuple htuple
    apply PSum.inl
    obtain ⟨pair, hpair, hleft, hright⟩ := (exists_pair_of_raw top) htuple
    have heq := hpairval pair hpair
    simp only [FlatCell.pair, Prod.mk.injEq] at hleft hright
    simpa only [value, rawCopyValue, columns,
      hleft.1, hleft.2, hright.1, hright.2] using heq

end Zcash.Snark
