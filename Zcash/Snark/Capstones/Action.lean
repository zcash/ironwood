import Zcash.Snark.Capstones.ActionBudgets

/-!
# Exact Action soundness and knowledge-soundness capstones

Captured checks and executable terminals yield knowledge-soundness bounds against an adversary
that chooses the public statement and proof together, for every consensus-valid Action bundle
size. Each is censused directly in `Fixtures/MultiAction/Honest/TrustBoundary.lean`.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark ComputedAdaptiveActionStatementFSFamily CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## Adaptive-statement knowledge endpoints -/


/-- Every adaptive-statement run's deployed pair count is below the scalar field order: the
`x₄` collapse groups at most the protocol-constant five multiopen point sets. -/
theorem adaptiveStatement_pairCount_lt (numProofs : ℕ)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs)) :
    ∀ basis O, deployedX4PairCount
      (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
      (adaptiveActionStatementInstanceCommitment (actionProofParamsFor numProofs) basis
        (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder := by
  intro basis O
  refine lt_of_le_of_lt (deployedX4PairCount_le_numPointSets _ _ _ _) ?_
  rw [CircuitShape.withProofParams_numPointSets]
  norm_num [actionProofParamsFor, scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- **Consensus-generic adaptive-statement Action knowledge soundness.**  The adversary outputs
the public inputs and proof together; the canonical VK and every selected instance commitment are
part of the transcript prefix before `theta`.  The knowledge-failure event uses the currently
executable witness projection defined by `AdaptiveStatementKnowledge`. -/
theorem orchard_action_knowledgeFailure_prob_le_adaptiveStatement_for
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family)) ≤
      (profile.advantage (adaptiveStatementDlogRandomOracleQueries family)
          (adaptiveStatementDlogGroupWork profile.proverGroupWork
            profile.reductionGroupWork) +
        1 / Fintype.card Fp) +
      (family.Q + 1 : ℕ) *
        (1 / Fintype.card Fp +
          actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal)) +
          algebraicRootBudget
            (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            actionCircuit.domainExponent +
          ∑ i : Fin 5,
            ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
                numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
              Fintype.card Fp) := by
  let epsilon : Fin 5 → ENNReal := fun i =>
    ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
        numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex actionCircuit.n → VestaG)
      (i : Fin 5)
      (instanceCommitment :
        Fin (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)).numProofs →
          Nat → VestaG)
      (ps : ProofString
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (i : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAtOf basis instanceCommitment i ps source earlier) ≤
        epsilon i := by
    intro basis i instanceCommitment ps source earlier
    exact orchard_adaptiveActionStatementSurface_measure_le_for
      numProofs basis instanceCommitment i ps source earlier
  have hevent := family.event_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family))
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon, CircuitShape.withProofParams_k] using
        (family.adaptiveStatementKnowledgeFailure_prob_le
          (adaptiveStatement_pairCount_lt numProofs family) B epsilon
            profile.finderAdvantageLE hsurface)

/-- **Adaptive-statement knowledge capstone.**  At `Q ≤ 2^123`, joint statement/proof
selection, the executable witness projection, and the shared relation finder fit a `2^126`
random-oracle/group-work envelope and `2^-83` statistical remainder; the finder and the
extractor consult the table only inside the certified read set.  Complete adversary and reduction
group work are explicit profile premises; the separately costed assembly/basis component fits its
derived formula at every table. -/
theorem orchard_action_knowledgeFailure_adaptiveStatement_2pow123_workFactor_generatorRO_for
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDirectDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family)) ≤
      profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 2 ^ 126 ∧
      adaptiveStatementKnowledgeExtractorGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤ 2 ^ 126 ∧
      adaptiveStatementCostedGroupOpsBudget (actionProofParamsFor numProofs) ≤ 2 ^ 123 ∧
      (∀ basis O, adaptiveStatementCostedGroupOpsAt family basis O ≤
        adaptiveStatementCostedGroupOpsBudget (actionProofParamsFor numProofs)) ∧
      (∀ basis O,
        adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
          adaptiveStatementDirectDecodeOps family basis O ≤ 2 ^ 123) ∧
      (∀ basis O,
        (family.relationFinderReads basis O).card ≤ 2 ^ 126) ∧
      (∀ basis O (O' : family.Coins),
        (∀ t ∈ family.relationFinderReads basis O, O' t = O t) →
        family.relationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O' =
          family.relationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O ∧
        (family.adaptiveStatementKnowledgeExtractor
            (adaptiveStatement_pairCount_lt numProofs family) basis O').isSome =
          (family.adaptiveStatementKnowledgeExtractor
            (adaptiveStatement_pairCount_lt numProofs family) basis O).isSome) ∧
      ∀ (actual : PMF ((↥(Set.range query) → VestaG) × family.Coins))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype family.Coins))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family)) ≤
          (profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.knowledgeExtractorCost_le
  have hqueries : adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤
      2 ^ 126 := by
    calc
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 8 * 2 ^ 123 :=
        hcost.1
      _ = 2 ^ 126 := by norm_num
  have hqueriesDlog : adaptiveStatementDlogRandomOracleQueries family ≤ 2 ^ 126 := by
    exact (adaptiveStatementDlogRandomOracleQueries_le_knowledgeExtractor family).trans hqueries
  have hgroup :
      adaptiveStatementKnowledgeExtractorGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤ 2 ^ 126 := by
    calc
      adaptiveStatementKnowledgeExtractorGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
          8 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 126 := by norm_num
  have hgroupDlog :
      adaptiveStatementDlogGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
        2 ^ 126 := by
    calc
      adaptiveStatementDlogGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
          8 * 2 ^ 123 := profile.solverCost_le.2.1
      _ = 2 ^ 126 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family)) ≤
        profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_knowledgeFailure_prob_le_adaptiveStatement_for
        numProofs B hB query hquery family profile.toAdaptiveStatementDlogProfile) ?_
    have hsum :
        (∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp) =
          (((numProofs * 992851621 + 20470 : ℕ) : ENNReal) /
            Fintype.card Fp) := by
      norm_num [Fin.sum_univ_succ]
      simp only [div_eq_mul_inv]
      ring
    rw [hsum]
    refine le_trans ?_
      (add_le_add (profile.advantage_mono hqueriesDlog hgroupDlog)
        (actionStatisticalModelFor_at_2pow123 hn profile.queryBound))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveStatementStatisticalModelFor_le_action numProofs family.Q))
    unfold adaptiveStatementStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, hgroup, profile.costedAssemblyWorkBound,
    fun basis O => adaptiveStatementCostedGroupOpsAt_le family basis O, hcost.2.2,
    fun basis O => le_trans
      (family.relationFinderReads_card_le_knowledgeExtractorQueries basis O) hqueries,
    fun basis O O' h =>
      ⟨family.relationFinder_eq_of_agree (adaptiveStatement_pairCount_lt numProofs family) h,
        family.adaptiveStatementKnowledgeExtractor_isSome_eq_of_agree
          (adaptiveStatement_pairCount_lt numProofs family) h⟩, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

end Zcash.Snark.Capstone
