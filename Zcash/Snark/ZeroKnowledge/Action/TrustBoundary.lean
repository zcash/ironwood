import Zcash.Snark.ZeroKnowledge.ActionReductionClass
import Zcash.Snark.ZeroKnowledge.ActionReductionData
import Zcash.Snark.ZeroKnowledge.ActionReductionProgram
import Zcash.Snark.ZeroKnowledge.ActionReductionSource
import Zcash.Snark.ZeroKnowledge.CostedActionGeneratorStream
import Zcash.Snark.ZeroKnowledge.CostedActionPrng
import Zcash.Snark.ZeroKnowledge.CostedInteractivePrng
import Zcash.Snark.ZeroKnowledge.InteractiveBitsView
import Zcash.Snark.ZeroKnowledge.InteractiveReductionClass
import Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram
import Zcash.Snark.ZeroKnowledge.InteractiveReductionSource
import Zcash.Snark.ZeroKnowledge.InteractiveTestCost
import Zcash.Snark.ZeroKnowledge.InteractiveViewBound
import Zcash.Snark.ZeroKnowledge.InteractiveViewCost
import Zcash.Snark.ZeroKnowledge.ObservedReductionCost
import Zcash.Snark.ZeroKnowledge.StoredActionRawStepCost
import Zcash.Snark.ZeroKnowledge.StoredActionRawStepBound
import Zcash.Snark.ZeroKnowledge.StoredActionRecordedCost
import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBound
import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBits
import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBitsLaw
import Zcash.Snark.ZeroKnowledge.SourceGateCompleteness
import Zcash.Snark.ZeroKnowledge.ScalarWitnessRouting
import Zcash.Snark.ZeroKnowledge.ScalarWitnessExtraction
import Zcash.Snark.ZeroKnowledge.AdvicePlacementBounds
import Zcash.Snark.ZeroKnowledge.ActionWitnessReadings
import Zcash.Snark.ZeroKnowledge.ActionWitnessObservation
import Zcash.Snark.ZeroKnowledge.ActionWitnessExtraction
import Zcash.Snark.ZeroKnowledge.ActionWitnessCompleteness
import Zcash.Snark.ZeroKnowledge.ActionValueWitnessCertificate
import Zcash.Snark.ZeroKnowledge.ActionScalarHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionRowRelations
import Zcash.Snark.ZeroKnowledge.ActionQueryValuation
import Zcash.Snark.ZeroKnowledge.ActionQueryRows
import Zcash.Snark.ZeroKnowledge.ActionMerkleHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionLookupValues
import Zcash.Snark.ZeroKnowledge.ActionLookupFallback
import Zcash.Snark.ZeroKnowledge.ActionGateValues
import Zcash.Snark.ZeroKnowledge.ActionDirectHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionCopyValues
import Zcash.Snark.ZeroKnowledge.ActionConstraintsRelation
import Zcash.Snark.ZeroKnowledge.StoredActionCachedFields
import Zcash.Snark.ZeroKnowledge.StoredActionCachedFieldsBound
import Zcash.Snark.ZeroKnowledge.StoredActionCachedRawBound
import Zcash.Snark.ZeroKnowledge.StoredActionCachedRawCost
import Zcash.Snark.ZeroKnowledge.StoredActionHistoryOracleBound
import Zcash.Snark.ZeroKnowledge.StoredActionHistoryOracleCost
import Zcash.Snark.ZeroKnowledge.StoredActionHistoryTrace
import Zcash.Snark.ZeroKnowledge.StoredActionHonestFieldTrace
import Zcash.Snark.ZeroKnowledge.StoredActionHonestJointCost
import Zcash.Snark.ZeroKnowledge.StoredActionHonestTapeJoint
import Zcash.Snark.ZeroKnowledge.StoredActionHonestTraceCost
import Zcash.Snark.ZeroKnowledge.StoredActionHonestOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredActionHonestOracleViewBound
import Zcash.Snark.ZeroKnowledge.ActionNumeratorCoefficientsCost
import Zcash.Snark.ZeroKnowledge.ActionQuotientRowsCost
import Zcash.Snark.ZeroKnowledge.ActionWitnessSimulation
import Zcash.Snark.ZeroKnowledge.ActionProverCompleteness
import Zcash.Snark.ZeroKnowledge.ActionGateActivationCoverage
import Zcash.Snark.ZeroKnowledge.ActionLookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.StoredActionInstanceCost
import Zcash.Snark.ZeroKnowledge.StoredActionInitialCost
import Zcash.Snark.ZeroKnowledge.StoredActionOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredActionOracleViewBound
import Zcash.Snark.ZeroKnowledge.StoredActionOracleSimulatorCost
import Zcash.Snark.ZeroKnowledge.StoredActionOracleSimulatorBound
import Zcash.Snark.ZeroKnowledge.StoredActionOracleRuntime
import Zcash.Snark.ZeroKnowledge.StoredActionTapeTraceCost
import Zcash.Snark.ZeroKnowledge.StoredActionJointSize
import Zcash.Snark.ZeroKnowledge.StoredActionTapeTraceBound
import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceData
import Zcash.Snark.ZeroKnowledge.ActionGateSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionLookupSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionLookupTraceAgreement
import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointCost
import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointBound
import Zcash.Snark.ZeroKnowledge.StoredActionJointCostBound
import Zcash.Snark.ZeroKnowledge.StoredActionJointCost
import Zcash.Snark.ZeroKnowledge.ActionPublicInputCost
import Zcash.Snark.ZeroKnowledge.ActionCacheCost
import Zcash.Snark.ZeroKnowledge.ActionNativeRouting
import Zcash.Snark.ZeroKnowledge.ActionSelectorReplacement
import Zcash.Snark.ZeroKnowledge.ActionTracePlacement
import Zcash.Snark.ZeroKnowledge.ActionCommitments
import Zcash.Snark.ZeroKnowledge.ActionCompilerSimulation
import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes
import Zcash.Snark.ZeroKnowledge.ActionCompressionInput
import Zcash.Snark.ZeroKnowledge.ActionOrderedPlacement
import Zcash.Snark.ZeroKnowledge.ActionOrderedSort
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate
import Zcash.Snark.ZeroKnowledge.ActionInstantiation
import Zcash.Snark.ZeroKnowledge.ActionPrng
import Zcash.Snark.ZeroKnowledge.ActionRetryLimit
import Zcash.Snark.ZeroKnowledge.ActionDigest
import Zcash.Snark.ZeroKnowledge.ActionFiatShamir
import Zcash.Snark.ZeroKnowledge.ActionFiatShamirBits
import Zcash.Snark.ZeroKnowledge.ActionFiatShamirRetry
import Zcash.Snark.ZeroKnowledge.ActionPrngSecurity
import Zcash.Snark.ZeroKnowledge.ActionGeneratorPrng
import Zcash.Snark.ZeroKnowledge.ActionPrivateRetryBits
import Zcash.Snark.ZeroKnowledge.ActionOracleStreamTermination
import Zcash.Snark.ZeroKnowledge.ActionGeneratorStreamTermination
import Zcash.Meta.AxiomCheck
import Zcash.Snark.ZeroKnowledge.ActionWitnessRows

import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasPlan
import Zcash.Snark.ZeroKnowledge.ActionBaseCopySources
import Zcash.Snark.ZeroKnowledge.ActionMulBaseConfig
import Zcash.Snark.ZeroKnowledge.ActionMulNativeCopies
import Zcash.Snark.ZeroKnowledge.ActionNativeCopies
import Zcash.Snark.ZeroKnowledge.ActionNativeCopyIntervals
import Zcash.Snark.ZeroKnowledge.NativeBaseCopySupport
import Zcash.Snark.ZeroKnowledge.NativeBaseGadgetSupport
import Zcash.Snark.ZeroKnowledge.NativeBaseLoopSupport
import Zcash.Snark.ZeroKnowledge.NativeMulCopySupport

/-!
# The actual Action circuit boundary of the zero-knowledge development

The general selector-padding argument remains in the standard-tier parent census.
Action's public-input layout and compiler data are reached through the existing
opaque circuit package and its proved API. That package carries the named Pallas
point-order dependency. The encoded Vesta comparison additionally carries the
existing Vesta point-order dependency. No new native certificate is introduced.

The actual compiler's masking profile follows from the source classifications,
activation trace, evaluated replacement polynomials, and checked compression count.
The actual configure program supplies the query order and all key dimensions.
The exact legacy sort, V1 placement, complete activation fold, and greedy packing
calculation certify fifteen packed columns. The derived
key supplies the domain, sigma naming, exact copy layout, and complete opening
connection. These facts also instantiate the encoded simulation bound. The
entire compiled degree profile follows from the source and the packer's degree
invariant. Structural source mask certificates survive selector replacement,
query resolution, and verifier-expression translation. No native root or
circuit-computation certificate is added.

The complete source trace proves that all nine previous-row selectors are
inactive at global row zero. The ordered synthesis summary also supplies exactly
the compiler's V1 starts and absolute activation list. These source refinements
also prove that the inactive guards' replacement polynomials vanish after
compression, including at another active selector's nonzero root. These actual
boundary values supply the main simulation's complete masking profile.
-/

assert_computable Zcash.Snark.ZeroKnowledge.actionInstanceRows +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionInstanceRows_eq_elements +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionPublicPolynomials +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_instances_eval +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_eq_compiler +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionInstanceCommitment_eq_reference +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionSigmaCommitment_eq_reference +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCompilerPublicCommitmentsMatch +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCompilerOpening_eq_public +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_chunkLen_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationSetCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_quotientPieceCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_instanceQueryLayout_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_adviceQueryLayout_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_recordedFixedQueries_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_fixedQueryLayout_of_selectorCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationColumns_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_shape_of_fixedQueryCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_referenceShape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionReferencePermutationChunks
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationChunks_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionReferenceKey +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_queryLayout +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_permutationChunks +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_domain +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_sigmaNaming +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copyChunkWidths +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copySigmaIndices +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copyQueries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_productShape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_publicCommitmentsMatch +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_opening_eq_public +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionCompilerReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.ActionZkRelation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkRelation_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.capturedActionURS +choice
assert_axioms Zcash.Snark.ZeroKnowledge.capturedActionURS_rounds
assert_axioms Zcash.Snark.ZeroKnowledge.capturedActionURS_blinding_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wideCapturedActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionZkRunFromRawTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProverFromSource +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProverFromSource_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.sourceActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrngReduction +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.seededActionZk_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZk_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkSimulator_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProver_retry_lt_one +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkSimulator_retry_lt_one +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetryProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetrySimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetryProver_truncate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_expected_attempts_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_length_tail_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_simulation_capstone +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorDegrees
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorMaxDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupInputDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupTableDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupInput_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupTable_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupInput_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupTable_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_lookupDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_degreeProfile_of_gates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorDegreeCost
assert_axioms Zcash.Snark.ZeroKnowledge.actionSelectorDegrees_le
assert_axioms Zcash.Snark.ZeroKnowledge.actionSelectorDegreeCost_pos
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_weightedGateDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorReplacement_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_substitutedGate_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierGate_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_gateDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_degreeProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionPreviousRowSelectors
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceMaskZero
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGateMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupInputMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupTableMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGateMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupInputMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupTableMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateQueryState_advice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateQueryState_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_fixIdx_packedColumn +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_advIdx_initial_retained +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_packedSelectorBounds +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Exact source selector traces and their connection to compiler placement.
assert_axioms Zcash.Snark.ZeroKnowledge.witnessPoint_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessNonIdPoint_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeAdd_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaLoad_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.loadPrivate_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthWitness_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.runningSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortRangeCheck_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheck_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckAt_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckAtDecomposed_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.copyCheck_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.incompleteRoundsSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.incompleteSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteRound_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteLoop_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.incomplete_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.completeRoundsSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeStartCopy_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.complete_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.variableBaseMainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.variableBaseMain_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.overflowGate_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.overflow_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.variableBaseSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.variableBase_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_trace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.variableBaseMainSelectorTrace_initial
assert_axioms Zcash.Snark.ZeroKnowledge.actionVariableBaseMain_initial_selector +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The complete source trace, composed from all Action subcircuits.
assert_computable Zcash.Snark.ZeroKnowledge.shortSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessShortCheck_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCheck_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCheckDecomposed_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaRoundsSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaPieceSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaPiece_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaSlot_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaChainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaChain_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaHashSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaHash_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaHash_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessMessagePiece_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.condSwap_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleDecomposition_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.merkleHashSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleHash_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.merkleLayerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleLayer_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleRoot_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteAdd_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.decomposeEnable_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.decomposeAssign_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.copyDecompose_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedConstantsWindow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedConstantsLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedWindow_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.fixedWindowChainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedWindowChain_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthWindow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthScalar_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.fullWidthInnerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthInner_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidth_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.runningFixedInnerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortInner_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortSign_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortFixed_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldInner_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldCheck13_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldFixed_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonFullRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonPartialRound_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.poseidonPermutationSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonPermutation_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonInit_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonInput_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonHash_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.addChip_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.valueCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.valueCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.spendAuthoritySelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.spendAuthority_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.addressIntegritySelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.addressIntegrity_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.nullifierSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.nullifier_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkGate_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkCanonicity_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.commitIvkPiecesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkPieces_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.commitIvkSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeB_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeD_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeE_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeG_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeH_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteGdCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePkdCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteValueCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteRhoCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePsiCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteYCanonicity_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteYSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteY_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.notePiecesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePieces_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteChecksSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteChecks_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.noteGatesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteGates_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionChecksSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthChecks_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrchardChecks_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionNotesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthNotes_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionBaseSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthesizeBase_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBaseCall_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddressRow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddress_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionMainPost_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorTrace_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_sourceTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Initial source inactivity and exact summary-derived placement.
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceSelectorTrace_initialCheck
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_previousSelector_initial_inactive +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceRegionStarts +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceRegionStarts_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_source +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceSelectorActivations +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceSelectorActivations_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_source +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_previousSelector_replacement_zero +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Actual compiler values discharge masking without initial-column or routing premises.
assert_computable Zcash.Snark.ZeroKnowledge.actionBoundaryFixedKnown +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_selector +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_initial_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_later_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_substitutedPartialMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_compiledExpressionMaskSafe_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierGate_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupInput_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupTable_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The exact ordered source shapes, with kernel-checked stage certificates.
assert_computable Zcash.Snark.ZeroKnowledge.actionRegionShapeTable
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionChecksRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionChecksRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionNotesRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionNotesRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionCrossAddressRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddressRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_eq_source
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_wellFormed

-- The actual compiler count is the finite calculation on those certified inputs.
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_ordered +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_ordered +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedSelectorCount +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_newFixedCols_eq_orderedCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Exact starts for every block in the concrete ordered placement certificate.
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementTrace_lawful
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementShapes
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementStarts
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementStarts_eq_slot
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementShapes_length

-- The source's exact legacy-sort order and the corresponding source-indexed starts.
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedRegionIndices
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_indices
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_length
assert_computable Zcash.Snark.ZeroKnowledge.actionRegionStartsCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_summaries
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts_eq_certificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_certificate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The complete activation table and the closed fifteen-column compiler count.
assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorBitsCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations_bits
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorCount_eq_fifteen
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_newFixedCols_eq_fifteen +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The same Action comparison before encoding and with exact raw hash responses.
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionCompilerTypedReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkTyped_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver_encoded +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedSimulator_encoded +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver_digest_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkDigest_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Single-attempt classical oracle simulation, executable tapes, and resource bounds.
-- ActionFiatShamir
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_challengeSchedule +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_prover_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_program_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleAdversary
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleRequest
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleSelection +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleAdversary +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOraclePreprocessing +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOraclePreprocessing_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOraclePublicContext +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleAdversary_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleConflicts
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_failure_anchor
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_firstAdvice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_programming_failure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_cached_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleModel
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleInitial +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.ActionOracleTape
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleTapeLaw
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleDigestView +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleDigestView_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleTypedTape_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleComp +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleComp_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRunTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRunTape_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleProgramView +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProgramView_empty_ne_none +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRunTape_eq_programmed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleResources
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleSimulator
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestSimulator_raw_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorProgram +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorProgram_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_field_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Fixed uniform bit tapes and the complete oracle simulator reduction budget.
-- ActionFiatShamirBits
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirBits_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirBits_binary_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleBits
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorBitCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorBitCount_eleven
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBit_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromTapes_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleWide
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorWordCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorWordCount_eleven
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromRawTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator_program +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWide_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Finite retained retries with shared oracle state and exact tape laws.
-- ActionFiatShamirRetry
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleRetryAdversary +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPreprocessing +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPreprocessing_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirRetry_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirRetry_binary_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetry
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleBitRetriesFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_fromTape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_fromTape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetryResources
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_tape_bits

-- Uniform-seed PRNG game and exact test-dependent reduction.
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrngSecurity_game_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedActionZk_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Continuous generator state, exact private-prefix replay, and the finite PRNG reduction.
-- ActionOracleRetrySource
assert_computable Zcash.Snark.ZeroKnowledge.RawPrivateRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.OracleReplyRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.actionRawOracleTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionRawOracleTape_law
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromRawTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromSource +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromSource_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionGeneratorRetry
assert_computable Zcash.Snark.ZeroKnowledge.actionGeneratorRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_replay +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_state +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratorRetryTape_at
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_source_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_word_budget +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetryPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceExperiment_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPrngReduction +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPrng_game_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedActionFiatShamirRetry_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionGeneratorPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryExperiment_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.generatedActionFiatShamirRetry_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionPrivateRetryBits
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitCount_eq
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryRawEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitsEquiv +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformActionPrivateRetryBits

-- Complete shared-oracle streams, uniform retry potentials, and retained nontermination.

-- ActionOracleRetryGeometric
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRate_le_twice_error
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRate_lt_half
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_uniform_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_exhaustion_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionOracleRetryTail
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRate
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestSimulator_observed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_exhaustion_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionOracleStream
assert_computable Zcash.Snark.ZeroKnowledge.ActionRetryOracleState
assert_computable Zcash.Snark.ZeroKnowledge.ActionRetryStreamEntry
assert_axioms Zcash.Snark.ZeroKnowledge.actionRetryStreamEntry_measurableSpace
assert_axioms Zcash.Snark.ZeroKnowledge.actionRetryStreamEntry_discreteMeasurableSpace
assert_computable Zcash.Snark.ZeroKnowledge.ActionRetryRawTape
assert_computable Zcash.Snark.ZeroKnowledge.actionRawOracleStep +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionBitOracleStep +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionRawOracleStep_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBitOracleStep_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryStream +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetryStream +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryStream_isProbabilityMeasure +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetryStream_isProbabilityMeasure +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionOracleStreamSimulation
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRecorded_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryStream_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionOracle_simulation_capstone +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionOracleStreamTermination
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetryStream_nontermination_eq_zero +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryStream_nontermination_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetryStream_truncation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryStream_truncation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Complete seeded retry histories, exact finite replay, and explicit computational truncation.

-- ActionGeneratorStream
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream_isProbabilityMeasure +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream_truncate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream_truncation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionGeneratorStreamPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream_test_truncate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetryStream_test_truncate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecord_uniform_test_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.generatedUnlimitedActionOracle_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.generatedUnlimitedActionOracle_simulation_capstone +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionGeneratorStreamTermination
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryStream_nontermination_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRate_pow_le_half

-- ActionOracleRecordedPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrngReduction +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrngReduction_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrng_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrng_exhaustion_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionOracleRecordedSource
assert_computable Zcash.Snark.ZeroKnowledge.ActionRetryRecordedView
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRecordFromRawTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordFromSource +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordFromRawTapes_forget +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordFromSource_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordFromSource_generated +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordFromSource_exhaustion_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Application witness normalization, actual hint decoding, and placed advice execution.

-- ActionWitnessNormalization
assert_computable Zcash.Snark.ZeroKnowledge.canonicalActionScalarWindows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalActionScalarWindows_val
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalActionScalarWindows_lt
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalActionScalarWindows_reconstruct
assert_computable Zcash.Snark.ZeroKnowledge.canonicalActionMerklePath +choice
assert_computable Zcash.Snark.ZeroKnowledge.normalizeActionWitness +choice
assert_axioms Zcash.Snark.ZeroKnowledge.normalizeActionWitness_spec_iff +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- CanonicalMerklePath
assert_computable Zcash.Snark.ZeroKnowledge.canonicalMerkleReadings +choice
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalMerkleReadings_chunks
assert_axioms Zcash.Snark.ZeroKnowledge.exactCanonicalMerklePath_pathNode
assert_axioms Zcash.Snark.ZeroKnowledge.pathNode_append

-- ActionWitnessConditions
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessLeftEncoding
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessRightEncoding
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessSide
assert_axioms Zcash.Snark.ZeroKnowledge.ActionWitnessConstructionConditions +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalActionMerklePath_eq_readings
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessConditions_merkleRoot +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessConditions_merkleHalves +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessConditions_proverAssumptions +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- ActionWitnessHints
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessHintData +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionScalarHintValues +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarHintValues_decode
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessHints +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessHintEnvironment +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessHints_sibling_read
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessHints_swap_read
assert_axioms Zcash.Snark.ZeroKnowledge.actionPointHint_eval
assert_axioms Zcash.Snark.ZeroKnowledge.actionMerkleSibling_eval
assert_axioms Zcash.Snark.ZeroKnowledge.actionMerkleSwap_eval
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessHints_decode

-- ActionWitnessHintWindows
assert_computable Zcash.Snark.ZeroKnowledge.actionScalarWindowValues +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarWindowValues_digit
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarWindowValues_canonical
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarWindowValues_reconstruct
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessHintWindows_canonical

-- ActionWitnessRows
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessAssignment +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessRows +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessRowBundle +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_environment +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_publicInput +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_hintData +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_hintWindows +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Repeated advice writes, original copy semantics, and checked source support.

-- ActionAdviceAliasPlan
assert_computable Zcash.Snark.ZeroKnowledge.actionNativeAdviceCopySource
assert_computable Zcash.Snark.ZeroKnowledge.actionAdviceAliasPrograms +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceAliasPrograms_erase +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- ActionBaseCopySources
assert_axioms Zcash.Snark.ZeroKnowledge.actionNativeAdviceCopySource_otherRegion
assert_axioms Zcash.Snark.ZeroKnowledge.actionNativeAdviceCopySource_previous
assert_axioms Zcash.Snark.ZeroKnowledge.actionNativeAdviceCopySource_outsideRows

-- ActionMulBaseConfig
assert_axioms Zcash.Snark.ZeroKnowledge.actionMul_hiBaseConfig
assert_axioms Zcash.Snark.ZeroKnowledge.actionMul_loBaseConfig

-- ActionMulNativeCopies
assert_axioms Zcash.Snark.ZeroKnowledge.actionMul_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- ActionNativeCopies
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_stepWit_baseX_copy
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_stepWit_baseY_copy
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_baseX_copySemantics
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_baseY_copySemantics

-- ActionNativeCopyIntervals
assert_axioms Zcash.Snark.ZeroKnowledge.actionNativeCopiesSound_before
assert_axioms Zcash.Snark.ZeroKnowledge.actionNativeCopiesSound_after

-- NativeBaseCopySupport
assert_computable Zcash.Snark.ZeroKnowledge.PreviousBaseCopySources
assert_computable Zcash.Snark.ZeroKnowledge.MulIncompleteBaseSeparated
assert_axioms Zcash.Snark.ZeroKnowledge.previousBaseCopySources_nonbase
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_round_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- NativeBaseGadgetSupport
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_doubleAndAdd_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- NativeBaseLoopSupport
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_loop_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- NativeMulCopySupport
assert_axioms Zcash.Snark.ZeroKnowledge.mul_main_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Complete original Action copy-source routing.
assert_axioms Zcash.Snark.ZeroKnowledge.actionMulCall_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAddressIntegrity_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionChecks_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBase_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_nativeCopiesSound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceAliasPrograms_sources +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Structural byte-cache costs and actual protocol size bounds.

-- ActionCacheCost
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleInitial_length +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionQueryAddress_bytes_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleView_programming_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- ActionPublicInputCost
assert_computable Zcash.Snark.ZeroKnowledge.actionPublicInputElementsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputElementsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputElementsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputElementsCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted_rowLength
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicInputRowsCosted_instanceRows +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionStoredInstanceRowCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionStoredInstanceRowCosted_result +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionStoredInstanceRowCosted_cost_le

-- StoredActionJointCost
assert_computable Zcash.Snark.ZeroKnowledge.storedActionJointSimulatorCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionJointSimulatorCosted_result +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionJointInputBudget

-- StoredActionJointCostBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionJointSimulatorCosted_cost_le

/-! ## Complete algebraic simulation from stored bits -/

assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkJointOutput
assert_computable Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_raw
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointInputBudget_eleven
assert_computable Zcash.Snark.ZeroKnowledge.storedActionTapeJointCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_cost_le_fixed

/-! ## Complete original Action sources -/

assert_computable Zcash.Snark.ZeroKnowledge.actionAdviceSourcePrograms +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourcePrograms_eq +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourceCertificateRaw +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourceCertificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionGateSourceLabels +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateSourceLabels_eq +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateSourceCertificateRaw +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateActivationSourceCertificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateLabels_nodup +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionLookupSourceLabels +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionLookupSourceLabels_eq +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionLookupSourceCertificateRaw +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionLookupActivationSourceCertificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupMasters_nodup +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceLookupTrace_placed_eq_certificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Complete stored-bit transcript, canonical observation, and raw reply prefixes.
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkTraceOutput
assert_computable Zcash.Snark.ZeroKnowledge.storedActionTapeTraceCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeTraceCosted_challenge_repricing
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeTraceCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeJointCosted_shape +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionTapeTraceCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionTapeTraceCosted_cost_le_fixed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Complete stored-input oracle simulator, its total bound, and exact statistical law.
assert_computable Zcash.Snark.ZeroKnowledge.storedActionInstanceCommitmentCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionInstanceCommitmentCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionInstanceCommitmentBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionInstanceCommitmentCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedActionInitialCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionInitialCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionInitialCosted_length +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionInitialCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionOracleViewCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleViewCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionOracleViewCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleViewCosted_cost_le_fixed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionOracleSimulatorCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleSimulatorCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionOracleSimulatorCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleSimulatorCosted_cost_le_fixed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleBitSimulator +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleBitSimulator_law +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleBit_simulation_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Complete original Action gate and lookup activation coverage.
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateActivationCoverage_certificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateActivationCoverage +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupActivationCoverage +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Complete source execution and application witness simulation.
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSource_readPlan +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSource_aliasPlan +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_extendsWitnesses +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_constraints_capstone +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_relation_capstone +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionWitness_simulation_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideCapturedActionWitness_simulation_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Prover completeness: actual emission status and full typed-verifier acceptance.
assert_axioms Zcash.Snark.ZeroKnowledge.actionAcceptedAttemptSet +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAcceptedAttemptSet_mem_iff +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAcceptedAttemptSet_not_mem_of_zero_x +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver_failure_pos +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkRelation_completeness_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionWitness_completeness_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionWitness_acceptance_probability_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionWitness_completeness_binary_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideCapturedActionWitness_completeness_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitWitness_simulation_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionOracleBitWitness_simulation_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/- Complete real private-tape construction, stored inputs, and canonical observed view. -/
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestJointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestJointCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestTapeJointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestTapeJointCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestTraceCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestTraceCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestOracleViewCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestOracleViewCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestOracleViewCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestOracleViewCosted_cost_le_fixed +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionNumeratorCoefficientsCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionQuotientPiecesFromRowsCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

/- Complete real cached attempt from stored raw tapes. -/
assert_computable Zcash.Snark.ZeroKnowledge.storedActionCachedFieldsCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedFieldsCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionCachedFieldsCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedFieldsCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedFieldsCosted_cache_length_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionCachedRawCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedRawCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedRawCostBudget_mono_cache
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedRawCosted_cache_length_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionCachedRawCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionCachedRawCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryReportCostBudget +choice
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryQueryCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryReportCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryQueryCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryQueryCosted_bytes_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryReportCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryQueryCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryReportCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryQueryCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCosted_length_le

/- Original Action witness and compiler specializations retain named curve dependencies. -/
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessObservation +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_merklePath
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_firstHalf
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_secondHalf
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_spec_iff
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_proverAssumptions_iff
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessObservation_normalize
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessConditions_proverAssumptions_of_observation
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionValueSourceCertificate
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionValueSource_annotationCount
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionDirectHintCells_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidth_windowCells_of_witnessScalarLoop
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidth_extract_windows_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidth_extract_scalar_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionWitnessReadAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.ActionWitnessReadAgreement.proverAssumptions_iff
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessConditions_proverAssumptions_of_readAgreement
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.valueCommit_fullWidth_witnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.spendAuthority_fullWidth_witnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaCommit_fullWidth_witnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_fullWidth_witnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.noteCommit_fullWidth_witnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarWindowReadings_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionMerkleHintCells_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_base_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_readAgreement_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_constraints_of_readAgreement
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_constraints_of_extendsWitnesses
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.sourceSelectorDegree
assert_computable Zcash.Snark.ZeroKnowledge.sourceSelectorGated
assert_axioms Zcash.Snark.ZeroKnowledge.sourceSelectorDegree_eval
assert_axioms Zcash.Snark.ZeroKnowledge.sourceSelectorGated_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGateHomogeneous
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGate_complete
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.mem_regionAdvicePrograms_iff
assert_axioms Zcash.Snark.ZeroKnowledge.mem_circuitAdvicePrograms_iff
assert_axioms Zcash.Snark.ZeroKnowledge.circuitAdvicePrograms_row_lt_placementEnd
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_advice_zero_of_outside
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessAssignment_advice_zero_of_outside
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_fixed
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_advice
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_instance
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRowFeeds_interpret_of_wrap
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRowFeeds_interpret
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceRotation_read_eq
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_fixed_resolves
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_advice_resolves
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateQuery_instance_resolves
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionResolvedQueryValuation
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionResolvedQueryValuation_interprets
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionResolvedQueryValuation_packed
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selector_inactive_after_placement
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.sourceCopyQuery
assert_computable Zcash.Snark.ZeroKnowledge.copyReferenceResolves
assert_axioms Zcash.Snark.ZeroKnowledge.copyReferenceResolves_value
assert_axioms Zcash.Snark.ZeroKnowledge.sourceCopyQuery_eval
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permCols_eq
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_copyReferences_resolve
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCopyCellPair_sourceValue
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_copies_of_constraints
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_loadedTable_value
assert_axioms Zcash.Snark.ZeroKnowledge.actionInitialGeneratorLoad_mem
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupArguments_eq
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckLookup_inactive
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaLookup_inactive
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_generatorTable_zero
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_inactiveGates
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_gates_of_constraints
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.verifyingKey_cast_constraintRelations
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_rows_of_verifierCS
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionLookup_inactive_input
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionLookup_tuple_of_constraints
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_lookups_of_constraints
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRows_relation_of_constraints
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

/- Complete counted real retries and their exact verifier-bit law. -/
assert_axioms Zcash.Snark.ZeroKnowledge.StoredActionRetryTape
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRawStepCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRawStepCosted_cache_length_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRawStepCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedStepCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionRecordedRetryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedRetryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedRetryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionRecordedCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedBitsCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.storedActionRecordedBitsCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedBitsCosted_cost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionRecordedBitsCosted_law +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/- Complete executable PRNG reductions, full-view tests, and resource admissibility. -/
assert_computable Zcash.Snark.ZeroKnowledge.ActionReductionProgram.constant
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.kernel_constant +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.constant_costBudget
assert_axioms Zcash.Snark.ZeroKnowledge.actionReductionAdmissible_constants +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.kernel_negate +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionPrices
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionData
assert_computable Zcash.Snark.ZeroKnowledge.ActionReductionData.ofReference +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionData.WellFormed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionData.ofReference_wellFormed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram
assert_computable Zcash.Snark.ZeroKnowledge.ActionReductionProgram.evalCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.ActionReductionProgram.costBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.evalCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.kernel +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReductionAdmissible +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReductionAdmissible_runtime +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReductionAdmissible_mono +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.recordedPrngTimeBound +choice
assert_computable Zcash.Snark.ZeroKnowledge.recordedPrngViewAndTailTimeBound +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ActionReductionProgram.kernel_observed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrngReduction_mem_costed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRecordPrngReduction_mem_ownBudget +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.costedGeneratedUnlimitedActionOracle_simulation_capstone +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.costedActionOracleRecordPrng_test_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.costedActionOracleRecordPrng_exhaustion_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.costedUniformSeedActionZk_test_error_bound +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveBitsViewCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveBitsViewCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveBitsViewCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveBitsViewCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.constant
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.kernel_constant +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.constant_costBudget
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveReductionAdmissible_constants +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.kernel_negate +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram
assert_computable Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.evalCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.costBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.evalCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.kernel +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveReductionAdmissible +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveReductionAdmissible_runtime +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactivePrngTimeBound +choice
assert_axioms Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram.kernel_observed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrngReduction_mem_costed +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveViewTest
assert_computable Zcash.Snark.ZeroKnowledge.interactiveTestCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveTestCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveTestCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveTestCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveHistoryViewCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveHistoryViewCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.interactiveViewFrames
assert_computable Zcash.Snark.ZeroKnowledge.interactiveRecordedView
assert_computable Zcash.Snark.ZeroKnowledge.interactiveHistoryViewCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveHistoryViewCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.observedReductionCosted +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.observedReductionCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.observedReductionCosted_cost_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.observedReductionCosted_result +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
