import Zcash.Snark.Capstones.Action.Budgets
import Zcash.Snark.Soundness.Action.DeploymentRecord

/-!
# Exact Action knowledge-soundness capstones

Captured checks and executable terminals yield knowledge-soundness bounds against an adversary
that chooses the public statement and proof together, for every consensus-valid Action bundle
size. Four endpoints state them:

* `orchard_action_adaptiveStatement_knowledge_error_bound` — the consensus-generic compositional
  error formula: the adversary's discrete-log advantage at its query and group-work counts, plus
  `1/|F|`, plus the per-query Schwartz–Zippel budgets of each challenge surface, with prover and
  reduction group work declared as profile premises.
* `orchard_action_adaptiveStatement_certified_knowledge_error_bound` — the same formula with the
  group-work accounting checked: the adversary is a staged costed program and Lean composes the
  counters, conditional on the staging's fidelity.
* `orchard_action_adaptiveStatement_certified_2pow125_knowledge_finite_security` — the certified
  formula evaluated at `Q ≤ 2^123` queries and `2^125` adversary group work:
  `Adv_DLOG(2^124, 2^126) + 2^-83`.
* `orchard_action_adaptiveStatement_deployed_2pow123_knowledge_finite_security` — the deployed
  form: an `ActionDeploymentInstantiation` identifies each model floor with its deployed
  counterpart, and the declared-profile formula at the `2^123` work factor is transported to that
  record's failure observer with the Challenge255 conversion priced:
  `Adv_DLOG(2^126, 2^126) + 2^-83 + 2^-136`.

The declared-profile formula's own `2^123` evaluation,
`adaptiveStatementKnowledgeFailure_le_at_2pow123`, is the rung the deployed endpoint transports
and the source of the number the knowledge contract quotes; it is not advertised separately.  The
other rungs here are the pair-count bound the endpoints are stated under, the direct-decode
budgets, the parametric certified endpoint, and the deployed bound with its Challenge255 charge
left symbolic.

All four are stated in the generator random-oracle model, over the URS that
`orchard_uniformURSIdentification_of_generatorRO` identifies with the uniform one.  That model is
shared by every endpoint here rather than distinguishing between them, so it is recorded once in
this docstring instead of in each name.

Endpoint names read `orchard_action_<setting>_<qualifiers>_<property>_<form>`, where the form is
`error_bound` for a compositional error formula and `finite_security` for its evaluation at a
fixed work factor.  The failure event is not part of the name: it is
`adaptiveStatementKnowledgeFailureEvent`, defined with the layer that proves the bound.

Knowledge soundness is the only property advertised here.  Ordinary soundness is not stated
separately because it is the weaker consequence at the same error:
`ComputedAdaptiveActionStatementFSFamily.acceptFalseStatement_subset_knowledgeFailure` proves the
accepting-false-statement set is contained in the event these endpoints bound, so a soundness
bound is `measure_mono` away and carries no independent content.

## Model boundary

The endpoints are theorems inside a stated model; each floor below is accepted and disclosed
rather than proved, with its known strengthening named where one exists:

* *Adversary class* — adversaries are represented online-AGM programs: every output point
  carries coefficients over the enumerated augmented basis.  A byte-level prover that fills a
  proof slot with a fresh point (a hash-to-curve output, say) sits outside the class; the known
  extension models hash-to-curve as an adversary-queryable, basis-extending oracle
  (`Soundness/Action/AdaptiveStatementModel.lean`, *Trust boundary*).  Larger algebraic classes
  — AGM with oblivious sampling — exist and are not modeled here.
* *Work accounting* — the certified tiers cost a staged program: a manually staged, costed copy
  of the online-AGM adversary, proven to erase to it, with the finder/extractor/reduction staged
  around it.  Lean checks the arithmetic of the staged nodes; that the staging omitted no group
  work — host callbacks and pure continuations perform none — is `StagedGroupWorkFaithful`,
  assumed for both halves and re-exported in each certified conclusion.  The uncertified tier
  instead takes the caller-supplied `proverGroupWork`/`reductionGroupWork` values as premises.
* *URS basis* — the probability space samples the basis through the generator random oracle
  (`orchardGeneratorROSetup`); identifying the deployed fixed hash-to-curve derivation with that
  experiment is the GroupHash random-oracle idealization, not a Lean theorem.
* *Challenges* — squeezes are exactly uniform (`uniformChallenge`).  The deployed conversion
  reduces a 64-byte digest modulo `p`; its exact reduction bias is priced by
  `challenge255_weightedBias_le`, and `challenge255_joint_eventBias_le` composes it through an
  adaptive deduplicated query tree (`Soundness/Oracle/Challenge255.lean`). The byte layer beneath
  the schedule — halo2's transcript encoding and BLAKE2b itself — is modeled and checked against
  every capture (`Verifier/Transcript.lean`); idealizing that digest as uniform remains external.
* *DLOG hardness* — each profile takes a caller-supplied advantage bound for its exact relation
  finder (`AdaptiveStatementDlogProfile`, `CertifiedAdaptiveStatementDlogProfile`); relating that
  bound to a standard resource-bounded DLOG game and a concrete security estimate is external.
* *Key digest* — `vkHash` is opaque: one canonical key per basis, no cross-key binding claimed
  (`AdaptiveStatementModel.lean`, *Intended instantiation*). At the captures the digest is
  derived, not taken: `Fixtures/PinnedKey.lean` hashes the pinned key description and checks its
  fields against the derived key; cross-key binding would need BLAKE2b's collision resistance.
* *Acceptance* — `DeployedAccepts` is the typed core and prices one proof bundle;
  `DeployedAcceptsBytes` composes exact proof parsing, the derived key digest, and the BLAKE2b
  challenge schedule into it. Both honest captures witness this byte-level predicate. Universal
  refinement of Rust's reader to the Lean decoder and halo2's optional `BatchVerifier` remain
  outside the formalized verifier (`Fingerprint/Match.lean`, *What remains external*). The
  deployment record pins the
  call shape behind that boundary: exact ten-row instance columns — Lagrange commitment
  zero-padding makes a shorter column verify as its zero-padding
  (`assembleNonInteractiveInstances?_padColumns`), aliasing a missing trailing row to
  `disableCrossAddress = 0` — and a positive per-bundle action count
  (`instanceColumnsExact`, `numProofs_pos`).

The bounds these endpoints prove are exact inside that model. The machine-readable shape for a
deployed interpretation is `ActionDeploymentInstantiation`
(`Soundness/Action/DeploymentRecord.lean`), one identification field per floor; the deployed
endpoint below consumes it, charges the joint Challenge255 bias once for the whole adaptive
transcript, and prices that charge at `2^-136` against the record's certified query ceiling.

Each is censused directly in `Fixtures/MultiAction/Honest/TrustBoundary.lean`.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture Zcash.Common

open Zcash.Snark ComputedAdaptiveActionStatementFSFamily CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## Adaptive-statement knowledge endpoints

The staged-certified endpoints below quantify over a costed adversary program and re-export its
obligations as conclusion conjuncts.  Read `Zcash/Snark/Soundness/AGM/CostedOracle.lean` first: it
defines the cost language, its erasure, the per-node cost rules, and the `StagedGroupWorkFaithful`
judgment those conjuncts name.
-/


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
theorem orchard_action_adaptiveStatement_knowledge_error_bound
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

/-- Consensus-generic adaptive-statement knowledge soundness with conditional staged work
accounting.  Two halves meet here, and only one is checked.

Lean checks the accounting: each node's cost is read off its own syntax rather than a caller's tag
(an MSM costs its term-list length), composition across `bind` is proved, the program erases to the
original algebraic adversary, and the cached route is pointwise equal to the original finder.

Staging the computation through those nodes is manual, and nothing in Lean measures an arbitrary
host term.  `CostedLabeledOracleComp.StagedGroupWorkFaithful` carries that half, as a premiss and
a conclusion conjunct.  “Certified” names checked accounting over a hand-staged program, not an
assumption-free theorem. -/
theorem orchard_action_adaptiveStatement_certified_knowledge_error_bound
    (numProofs workLimit : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (certificate :
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementAdversaryCostCertificate
        family workLimit)
    (profile : ComputedAdaptiveActionStatementFSFamily.CertifiedAdaptiveStatementDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B workLimit certificate) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        family.adaptiveStatementKnowledgeFailureEvent
          (adaptiveStatement_pairCount_lt numProofs family)) ≤
      (profile.advantage (adaptiveStatementCachedRandomOracleQueries family)
          (workLimit + adaptiveStatementReductionGroupWork
            (actionProofParamsFor numProofs)) +
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
    (family.adaptiveStatementKnowledgeFailureEvent
      (adaptiveStatement_pairCount_lt numProofs family))
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon, CircuitShape.withProofParams_k] using
        (family.adaptiveStatementKnowledgeFailure_prob_le
          (adaptiveStatement_pairCount_lt numProofs family) B epsilon
            profile.finderAdvantageLE_current hsurface)

/-- The declared-profile formula at the `2^123` work factor, the input the deployed endpoint
transports.  At `Q ≤ 2^123`, joint statement/proof selection, the executable witness projection,
and the shared relation finder fit a `2^126` random-oracle/group-work envelope and `2^-83`
statistical remainder; the finder and the extractor consult the table only inside the certified
read set.  Complete adversary and reduction group work are explicit profile premises; the
separately costed assembly/basis component fits its derived formula at every table.  The final
conjunct also records a generic whole-distribution `ε_bias` transport.  The deployed endpoint
instead consumes the first conjunct and proves its dedicated joint Challenge255 observer hybrid
below. -/
theorem adaptiveStatementKnowledgeFailure_le_at_2pow123
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
        (ε_bias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype family.Coins))
          ε_bias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              family.adaptiveStatementKnowledgeFailureEvent (adaptiveStatement_pairCount_lt numProofs family)) ≤
          (profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) + ε_bias := by
  have hcost := profile.knowledgeExtractorCost_le
  have hqueries : adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤
      2 ^ 126 := by
    calc
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 8 * 2 ^ 123 :=
        hcost.1
      _ = 2 ^ 126 := by norm_num
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
      (orchard_action_adaptiveStatement_knowledge_error_bound
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
      (add_le_add (profile.advantage_mono
          ((adaptiveStatementDlogRandomOracleQueries_le_knowledgeExtractor family).trans hqueries)
          hgroupDlog)
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
  intro actual ε_bias hbias
  exact event_measure_le_of_bias hbias _ hprob

/-- The deployed knowledge-failure bound with the joint Challenge255 charge left symbolic.  A
complete deployment record instantiates the basis, typed verifier, concrete DLOG profile, and a
deduplicated finite failure observer.  The proved joint Challenge255 hybrid transports the ideal
`2^123` work-factor bound to that observer, charging `challengeQueryBound * challenge255Bias`
once for the whole adaptive transcript rather than assuming an unjustified one-squeeze event
bound.  The charge is a free multiple of the record's budget here — `OracleComp.QueryBound` is
upward-closed, so nothing in this statement keeps it small; the endpoint below prices it. -/
theorem adaptiveStatementDeployedKnowledgeFailure_le_jointCharge
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (deployment : ActionDeploymentInstantiation (actionProofParamsFor numProofs) family query
      (adaptiveStatement_pairCount_lt numProofs family) (2 ^ 123)) :
    deployment.deployedFailurePMF.toOuterMeasure {true} ≤
      (deployment.dlogAdvantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) +
        deployment.challengeQueryBound * challenge255Bias := by
  have hcapstone :=
    adaptiveStatementKnowledgeFailure_le_at_2pow123
      numProofs hn deployment.basisGenerator deployment.basisGenerator_ne_zero query
      deployment.queryInjective family deployment.profile
  have hideal :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure
          ((fun p ↦ (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.adaptiveStatementKnowledgeFailureEvent
              (adaptiveStatement_pairCount_lt numProofs family)) ≤
        deployment.profile.advantage (2 ^ 126) (2 ^ 126) +
          1 / (2 ^ 83 : ENNReal) :=
    hcapstone.1
  have hpointwise : ∀ basis,
      PMFEventBiasLE
        ((OracleComp.dedup [] (deployment.failureObserver basis)).runFreshPMF
          deployment.deployedChallengeLaw)
        ((OracleComp.dedup [] (deployment.failureObserver basis)).runFreshPMF uniformChallenge)
        (deployment.challengeQueryBound * challenge255Bias) := by
    intro basis
    rw [deployment.challengeLawIsChallenge255]
    exact challenge255_joint_eventBias_le (deployment.failureObserverQueryBound basis)
  let idealObserver : PMF Bool :=
    ((orchardGeneratorROSetup query).map (orchardGeneratorROBasis query)).bind fun basis ↦
      (OracleComp.dedup [] (deployment.failureObserver basis)).runFreshPMF uniformChallenge
  have hjoint :
      PMFEventBiasLE deployment.deployedFailurePMF
        idealObserver
        (deployment.challengeQueryBound * challenge255Bias) := by
    unfold idealObserver
    unfold ActionDeploymentInstantiation.deployedFailurePMF
    rw [deployment.basisIsGeneratorRO]
    exact PMFEventBiasLE.bind_same hpointwise
  have hidealObserver :
      idealObserver.toOuterMeasure {true} ≤
        deployment.profile.advantage (2 ^ 126) (2 ^ 126) +
          1 / (2 ^ 83 : ENNReal) := by
    unfold idealObserver
    exact deployment.idealFailureMeasure_eq.trans_le hideal
  rw [deployment.dlogAdvantageAgrees]
  exact event_measure_le_of_bias hjoint {true} hidealObserver

/-- **Deployed adaptive-statement knowledge capstone.** The joint Challenge255 charge of
`adaptiveStatementDeployedKnowledgeFailure_le_jointCharge`, priced: the record certifies its
observer's query budget no looser than one adversary run plus the verifier's squeezes
(`challengeQueryBound_le`), the profile bounds the adversary's budget by `2^123`, and the exact
bias is below `2^-260` (`challenge255Bias_le`), so the charge is below `2^-136`
(`challenge255_joint_charge_le_at_2pow123`).  The deployed knowledge-failure probability is
therefore within `2^-136` of the ideal `2^123` work-factor bound — a closed number, not a bound
that a loose-but-valid budget could push past `1`. -/
theorem orchard_action_adaptiveStatement_deployed_2pow123_knowledge_finite_security
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (deployment : ActionDeploymentInstantiation (actionProofParamsFor numProofs) family query
      (adaptiveStatement_pairCount_lt numProofs family) (2 ^ 123)) :
    deployment.deployedFailurePMF.toOuterMeasure {true} ≤
      deployment.dlogAdvantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal) +
        1 / (2 ^ 136 : ENNReal) := by
  refine le_trans
    (adaptiveStatementDeployedKnowledgeFailure_le_jointCharge numProofs hn query family
      deployment)
    (add_le_add le_rfl ?_)
  refine challenge255_joint_charge_le_at_2pow123 deployment.profile.queryBound ?_
    deployment.challengeQueryBound_le
  rw [CircuitShape.withProofParams_k, actionCircuit.shape_k]
  exact ActionConstraintBounds.domainExponent_lt

/-- The selected proof's direct-decode source fits the `2^90` endpoint envelope.  All
proof-controlled and instance entries have shape-indexed lengths; the sole list-valued input is
bounded by the required `fixedRepresentations_length_le` family invariant.  Thus this theorem is
uniform for every conforming family, but does not itself construct or validate a concrete deployed
family's representation table. -/
theorem adaptiveStatementDirectDecodeSourceLength_le_two_pow_90
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (basis) (O : family.Coins) :
    adaptiveStatementDirectDecodeSourceLength family basis O ≤ 2 ^ 90 := by
  have hfixed := family.fixedRepresentations_length_le basis
  unfold adaptiveStatementFixedRepresentationLimit at hfixed
  unfold adaptiveStatementDirectDecodeSourceLength
  dsimp only
  rw [AlgebraicProofString.preX1AssemblySource_length,
    AlgebraicProofString.preX1Points_length]
  simp only [List.length_append, adaptiveStatementInstanceRepresentationList_length]
  simp only [AdaptiveActionStatementShape]
  have hshape := actionProofShape_eq_maxShape numProofs
  have hproofs := congrArg (fun shape : Shape => shape.numProofs) hshape
  have hadvice := congrArg (fun shape : Shape => shape.numAdviceColumns) hshape
  have hlookups := congrArg (fun shape : Shape => shape.numLookups) hshape
  have hpermutation := congrArg (fun shape : Shape => shape.numPermutationSets) hshape
  have hquotient := congrArg (fun shape : Shape => shape.numQuotientPieces) hshape
  have hinstance := congrArg (fun shape : Shape => shape.numInstanceColumns) hshape
  dsimp only [Zcash.Snark.FixtureMax.shape] at hproofs hadvice hlookups hpermutation hquotient hinstance
  rw [hproofs, hadvice, hlookups, hpermutation, hquotient, hinstance]
  have hn' : numProofs ≤ 2 ^ 16 - 1 := hn
  omega

/-- Three executions of the actual direct decoder fit the `2^123` endpoint budget.  This is
derived from the required family source-length invariant and the captured-shape cost formula, not
supplied as a free numeric field of the DLOG profile. -/
theorem adaptiveStatementThreeDirectDecodes_le_two_pow_123
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (basis) (O : family.Coins) :
    adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
        adaptiveStatementDirectDecodeOps family basis O ≤ 2 ^ 123 := by
  have hsource := adaptiveStatementDirectDecodeSourceLength_le_two_pow_90
    numProofs hn family basis O
  unfold adaptiveStatementKnowledgeExtractorDirectDecodeSlots
  unfold adaptiveStatementDirectDecodeOps
  dsimp only
  have hdecode := deployedDirectDecodeOps_le
    (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
    (adaptiveActionStatementInstanceCommitment (actionProofParamsFor numProofs) basis
      (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O)
    (adaptiveStatementDirectDecodeSourceLength family basis O)
  have hdecode' :
      deployedDirectDecodeOps
          (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
          (adaptiveActionStatementInstanceCommitment (actionProofParamsFor numProofs) basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 (family.runRecord basis O)
          (adaptiveStatementDirectDecodeSourceLength family basis O) ≤
        6 * ((50 * numProofs + 46) *
          (adaptiveStatementDirectDecodeSourceLength family basis O + 4101) + 2050) := by
    refine hdecode.trans ?_
    have hquery : queryBudget
        (AdaptiveActionStatementShape (actionProofParamsFor numProofs)) =
          50 * numProofs + 46 := by
      change queryBudget
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) = _
      rw [actionProofShape_eq_maxShape]
      exact Zcash.Snark.FixtureMax.queryBudget_at_captured_shape numProofs
    have hshape := actionProofShape_eq_maxShape numProofs
    have hpointSets := congrArg (fun shape : Shape => shape.numPointSets) hshape
    have hk := congrArg (fun shape : Shape => shape.k) hshape
    dsimp only [Zcash.Snark.FixtureMax.shape] at hpointSets hk
    rw [hquery, hpointSets, hk]
    norm_num
  refine le_trans (Nat.mul_le_mul_left 3 hdecode') ?_
  have hn' : numProofs ≤ 2 ^ 16 - 1 := hn
  calc
    3 * (6 * ((50 * numProofs + 46) *
          (adaptiveStatementDirectDecodeSourceLength family basis O + 4101) + 2050)) ≤
        3 * (6 * ((50 * (2 ^ 16 - 1) + 46) * (2 ^ 90 + 4101) + 2050)) := by
      gcongr
    _ ≤ 2 ^ 123 := by norm_num

/-- Arithmetic and transfer proof for the certified endpoint below, stated for any adversary work
ceiling between `2^123` and `2^125`; the endpoint is its instance at `2^125`. -/
private theorem adaptiveStatementCertifiedEndpoint
    (numProofs workLimit : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    (hworkLower : 2 ^ 123 ≤ workLimit) (hworkUpper : workLimit ≤ 2 ^ 125)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (hQ : family.Q ≤ 2 ^ 123)
    (certificate :
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementAdversaryCostCertificate
        family workLimit)
    (profile : ComputedAdaptiveActionStatementFSFamily.CertifiedAdaptiveStatementDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B workLimit certificate) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.adaptiveStatementKnowledgeFailureEvent
            (adaptiveStatement_pairCount_lt numProofs family)) ≤
      profile.advantage (2 ^ 124) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveStatementCachedRandomOracleQueries family ≤ 2 ^ 124 ∧
      (∀ basis O, (family.relationFinderReads basis O).card ≤ 2 ^ 124) ∧
      adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤ 2 ^ 123 ∧
      (∀ basis, (certificate.program basis).erase = family.adversary basis) ∧
      (∀ basis, (certificate.program basis).StagedGroupWorkFaithful) ∧
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementExecutionStagingCoverage
        family (adaptiveStatement_pairCount_lt numProofs family) B workLimit certificate ∧
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementProgrammedReductionCoverage
        family (adaptiveStatement_pairCount_lt numProofs family) B workLimit certificate ∧
      (∀ basis O, certificate.proverGroupWork basis O ≤ workLimit) ∧
      (∀ basis O,
        adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
          adaptiveStatementDirectDecodeOps family basis O ≤ workLimit) ∧
      ∀ basis O,
        (family.costedCachedKnowledgeExtractor
          (adaptiveStatement_pairCount_lt numProofs family) certificate basis O).groupWork ≤
            2 * workLimit ∧
        (family.costedCachedKnowledgeExtractor
          (adaptiveStatement_pairCount_lt numProofs family) certificate basis O).value.isSome =
            (family.adaptiveStatementKnowledgeExtractor
              (adaptiveStatement_pairCount_lt numProofs family) basis O).isSome ∧
        family.cachedRelationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O =
          family.relationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O := by
  have hk :
      (AdaptiveActionStatementShape (actionProofParamsFor numProofs)).k = 11 := by
    unfold AdaptiveActionStatementShape
    rw [actionShapeFor_eq_fixtureShape]
    rfl
  have hqueries : adaptiveStatementCachedRandomOracleQueries family ≤ 2 ^ 124 := by
    rw [adaptiveStatementCachedRandomOracleQueries, hk]
    calc
      family.Q + 11 + 11 ≤ 2 ^ 123 + 22 := by omega
      _ ≤ 2 ^ 124 := by norm_num
  have hreduction := adaptiveStatementReductionGroupWork_at_consensus numProofs hn
  have hreductionLimit :
      adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤ workLimit :=
    hreduction.trans hworkLower
  have hgroupDlog :
      workLimit + adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤
        2 ^ 126 := by
    calc
      workLimit + adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤
          2 ^ 125 + 2 ^ 123 := Nat.add_le_add hworkUpper hreduction
      _ ≤ 2 ^ 126 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.adaptiveStatementKnowledgeFailureEvent
              (adaptiveStatement_pairCount_lt numProofs family)) ≤
        profile.advantage (2 ^ 124) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_adaptiveStatement_certified_knowledge_error_bound
        numProofs workLimit B hB query hquery family certificate profile) ?_
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
      (add_le_add (profile.advantage_mono hqueries hgroupDlog)
        (actionStatisticalModelFor_at_2pow123 hn hQ))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveStatementStatisticalModelFor_le_action numProofs family.Q))
    unfold adaptiveStatementStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, ?_, hreduction, certificate.erase_eq, certificate.staged,
    profile.executionStaging, profile.programmedReductionCoverage, certificate.proverGroupWork_le,
    (fun basis O ↦
      (adaptiveStatementThreeDirectDecodes_le_two_pow_123
        numProofs hn family basis O).trans hworkLower), ?_⟩
  · intro basis O
    exact (profile.queryCoverage basis O).trans hqueries
  intro basis O
  refine ⟨family.costedCachedKnowledgeExtractor_two_mul_bound
      (adaptiveStatement_pairCount_lt numProofs family) certificate hreductionLimit basis O,
    ?_, family.cachedRelationFinder_eq
      (adaptiveStatement_pairCount_lt numProofs family) basis O⟩
  rw [family.costedCachedKnowledgeExtractor_value
    (adaptiveStatement_pairCount_lt numProofs family) certificate basis O]
  exact family.cachedKnowledgeExtractor_isSome_eq
    (adaptiveStatement_pairCount_lt numProofs family) basis O

/-- **Conditionally staged-certified `2^125` adaptive-statement endpoint.** Faithfully staged
adversary and complete execution programs, with mechanically composed data flow and counters, fit
a `2^126` DLOG group-work envelope when adversary work is bounded by `2^125`. The random-oracle
budget remains independently bounded by `Q ≤ 2^123`, and direct-decode coverage is derived from
the required family cap. -/
theorem orchard_action_adaptiveStatement_certified_2pow125_knowledge_finite_security
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (hQ : family.Q ≤ 2 ^ 123)
    (certificate :
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementAdversaryCostCertificate
        family (2 ^ 125))
    (profile : ComputedAdaptiveActionStatementFSFamily.CertifiedAdaptiveStatementDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B (2 ^ 125) certificate) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.adaptiveStatementKnowledgeFailureEvent
            (adaptiveStatement_pairCount_lt numProofs family)) ≤
      profile.advantage (2 ^ 124) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveStatementCachedRandomOracleQueries family ≤ 2 ^ 124 ∧
      (∀ basis O, (family.relationFinderReads basis O).card ≤ 2 ^ 124) ∧
      adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤ 2 ^ 123 ∧
      (∀ basis, (certificate.program basis).erase = family.adversary basis) ∧
      (∀ basis, (certificate.program basis).StagedGroupWorkFaithful) ∧
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementExecutionStagingCoverage
        family (adaptiveStatement_pairCount_lt numProofs family) B (2 ^ 125) certificate ∧
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementProgrammedReductionCoverage
        family (adaptiveStatement_pairCount_lt numProofs family) B (2 ^ 125) certificate ∧
      (∀ basis O, certificate.proverGroupWork basis O ≤ 2 ^ 125) ∧
      (∀ basis O,
        adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
          adaptiveStatementDirectDecodeOps family basis O ≤ 2 ^ 125) ∧
      ∀ basis O,
        (family.costedCachedKnowledgeExtractor
          (adaptiveStatement_pairCount_lt numProofs family) certificate basis O).groupWork ≤
            2 ^ 126 ∧
        (family.costedCachedKnowledgeExtractor
          (adaptiveStatement_pairCount_lt numProofs family) certificate basis O).value.isSome =
            (family.adaptiveStatementKnowledgeExtractor
              (adaptiveStatement_pairCount_lt numProofs family) basis O).isSome ∧
        family.cachedRelationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O =
          family.relationFinder (adaptiveStatement_pairCount_lt numProofs family) basis O := by
  simpa only [show 2 * 2 ^ 125 = 2 ^ 126 by norm_num] using
    (adaptiveStatementCertifiedEndpoint numProofs (2 ^ 125) hn (by norm_num) le_rfl
      B hB query hquery family hQ certificate profile)

end Zcash.Snark.Capstone
