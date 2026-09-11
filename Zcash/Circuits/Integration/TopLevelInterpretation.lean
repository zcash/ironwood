import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Halo2.ConstraintsCompiled
import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Multiopen.InstanceColumns
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelWitness
import Zcash.Circuits.Integration.TopLevelCopyConstraints
import Zcash.Snark.Keygen.Pipeline
import Mathlib.Util.AssertNoSorry

/-! # Interpreting accepted polynomials in a top-level circuit

Commitment binding identifies fixed and permutation polynomials with the circuit's
compiler output. Together with the challenge exclusions, these identifications
recover Clean constraints and executable witnesses for any TLC.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open Keygen

set_option maxHeartbeats 20000

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top] [CircuitFieldSupport top]

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/-- Recover the circuit's witnesses from the canonical relation, or compute
an augmented-basis relation when fixed/permutation commitments have conflicting openings. -/
def CanonicalMemberConstraintRelation.topLevelWitnesses_or_relation
    (pp : ProofParams) (urs : URS G)
    (hk :
      top.domainExponent = urs.k)
    {instanceCommitment :
      Fin pp.numProofs →
        ℕ → G}
    {ps : ProofString
      (top.shape.withProofParams pp) Fp G}
    {ch : Challenges
      top.domainExponent Fp}
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
        urs hk (top.toVerifierKey urs)
        ps ch batchOpenings i hi}
    {hpoly : CPoly}
    (relation :
      CanonicalMemberConstraintRelation
        (shape := top.shape.withProofParams pp)
        urs hk (top.toVerifierKey urs)
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs)
        ch.y hpoly
        top.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          top.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        pp.numProofs (top.toVerifierKey urs)
        ch relation.polynomial (top.usableRowsAt top.domainExponent))
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        top pp urs ch relation.polynomial) :
    TopLevelBundleWitness top pp.numProofs relation.polynomial ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hdomainSize : top.n = 2 ^ urs.k := by
    rw [top.n_eq_two_pow_domainExponent, hk]
  have hsatisfaction := relation.constraintSatisfaction top.n_ne_zero hgoodY
  have hmodel : relation.model = top.constraintModel pp urs ch relation.polynomial := by
    simp only [CanonicalMemberConstraintRelation.model]
    exact (top.constraintModel_eq_toVerifierKey_constraintModel
      pp urs ch relation.polynomial).symm
  rw [hmodel] at hsatisfaction
  obtain hbinding | bad := relation.topLevelFixedColumns_eq_rowPolynomials_or_relation
  swap
  · exact PSum.inr bad
  have hencoding : top.FixedColumnEncoding relation.polynomial := by
    apply topLevelFixedColumnEncoding_of_binding relation.polynomial
    intro column
    simpa only [hdomainSize] using hbinding column
  refine finForallOrRelationWitness
    (A := fun proofIndex : Fin pp.numProofs =>
      TopLevelSemanticWitness top
        (top.extractPublicInput (top.environment
          (polynomialAssignment top.omega relation.polynomial proofIndex))))
    fun proofIndex => ?_
  let assignment := polynomialAssignment top.omega relation.polynomial proofIndex
  obtain hcopies | bad := relation.copiesCompiled_or_relation
    top pp urs hk hsatisfaction permutationExclusions proofIndex hencoding
  swap
  · exact PSum.inr bad
  exact PSum.inl
    { w := top.extractWitness assignment
      satisfied := top.soundness_compiled assignment
        { gates := top.gatesCompiled_of_constraintSatisfaction ch relation.polynomial
            proofIndex hsatisfaction hencoding
          copies := hcopies
          lookups := TopLevelLookup.lookupsCompiled_of_constraintSatisfaction ch relation.polynomial
            proofIndex hsatisfaction hencoding lookupExclusions } }

end Zcash.Snark
