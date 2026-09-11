import Zcash.Circuits.Integration.PermutationCycle
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Halo2.CompiledCopies
import Zcash.Snark.Soundness.Pricing.ChallengePricing

/-! # Compiled copy equality from the verifier permutation argument

Commitment binding identifies the generated σ cycle. The permutation argument then
gives equal values on every resolved compiler copy pair.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open TopLevelCopy

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top] [CircuitFieldSupport top]

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/-- Recover compiled copy equality, or an augmented-commitment relation. -/
def CanonicalMemberConstraintRelation.copiesCompiled_or_relation
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
    (satisfaction : ConstraintSatisfaction
      (top.constraintModel pp urs ch relation.polynomial) top.n)
    (exclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch relation.polynomial (top.usableRowsAt top.domainExponent))
    (proofIndex : Fin pp.numProofs)
    (hencoding : top.FixedColumnEncoding relation.polynomial) :
    top.CopiesCompiled (resolverAssignment top.omega relation.polynomial proofIndex) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  rcases resolverPermutationCycle_or_relation top pp urs hk relation proofIndex with hcycle | hbad
  · have hvalues := permutationValues_of_constraintSatisfaction top
        pp urs ch relation.polynomial
        proofIndex satisfaction hcycle.cycle hcycle.sigma_eq
        (exclusions.good proofIndex)
    rw [top.resolverEnvironment_eq_environment urs relation.polynomial proofIndex hencoding] at hvalues
    exact PSum.inl (top.copiesCompiled_of_permutation _ hvalues)
  · exact PSum.inr hbad

end Zcash.Snark
