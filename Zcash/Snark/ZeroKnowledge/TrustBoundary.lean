import Zcash.Snark.ZeroKnowledge.BooleanTestBound
import Zcash.Snark.ZeroKnowledge.BooleanTestCost
import Zcash.Snark.ZeroKnowledge.BooleanTestMap
import Zcash.Snark.ZeroKnowledge.BooleanTestMeasurable
import Zcash.Snark.ZeroKnowledge.IndexedTestReadCost
import Zcash.Snark.ZeroKnowledge.InteractiveChallengeBits
import Zcash.Snark.ZeroKnowledge.InteractiveViewEncoding
import Zcash.Snark.ZeroKnowledge.RawTapeTestProgram
import Zcash.Snark.ZeroKnowledge.RecordedTestProgram
import Zcash.Snark.ZeroKnowledge.RecordedTestRead
import Zcash.Snark.ZeroKnowledge.RecordedTestReadBound
import Zcash.Snark.ZeroKnowledge.RecordedTestRegression
import Zcash.Snark.ZeroKnowledge.StreamTestProgram
import Zcash.Snark.ZeroKnowledge.StreamTestRead
import Zcash.Snark.ZeroKnowledge.StatefulRetryCost
import Zcash.Snark.ZeroKnowledge.StatefulRetryCostBound
import Zcash.Snark.ZeroKnowledge.OracleRetryCost
import Zcash.Snark.ZeroKnowledge.StoredRawMatrixCost
import Zcash.Snark.ZeroKnowledge.StoredRetryTapePairing
import Zcash.Snark.ZeroKnowledge.HintCellExtraction
import Zcash.Snark.ZeroKnowledge.CachedPrefixBound
import Zcash.Snark.ZeroKnowledge.CachedPrefixCost
import Zcash.Snark.ZeroKnowledge.CachedPrefixSource
import Zcash.Snark.ZeroKnowledge.StoredActionHistoryTraceBound
import Zcash.Snark.ZeroKnowledge.StoredActionHonestFieldTraceBound
import Zcash.Snark.ZeroKnowledge.StoredHistoryChallengeCost
import Zcash.Snark.ZeroKnowledge.StoredRawFieldCost
import Zcash.Snark.ZeroKnowledge.HonestProverDimensions
import Zcash.Snark.ZeroKnowledge.HonestProverPriceBudget
import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialBound
import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialCost
import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialSource
import Zcash.Snark.ZeroKnowledge.HonestTapeJointBound
import Zcash.Snark.ZeroKnowledge.HonestTapeJointCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialDimensions
import Zcash.Snark.ZeroKnowledge.StoredActionHonestJointBound
import Zcash.Snark.ZeroKnowledge.StoredActionHonestShape
import Zcash.Snark.ZeroKnowledge.StoredActionHonestTapeBound
import Zcash.Snark.ZeroKnowledge.StoredActionHonestTraceBound
import Zcash.Snark.ZeroKnowledge.StoredActionWitnessCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapeBound
import Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapes
import Zcash.Snark.ZeroKnowledge.StoredPrivateMaterialSource
import Zcash.Snark.ZeroKnowledge.StoredProverDigestCost
import Zcash.Snark.ZeroKnowledge.CommitmentCoefficientRoutingBound
import Zcash.Snark.ZeroKnowledge.CommitmentCoefficientRoutingCost
import Zcash.Snark.ZeroKnowledge.DenseCommitmentCost
import Zcash.Snark.ZeroKnowledge.FiniteListReadCost
import Zcash.Snark.ZeroKnowledge.HonestJointRowsBound
import Zcash.Snark.ZeroKnowledge.HonestJointRowsCost
import Zcash.Snark.ZeroKnowledge.HonestJointRowsDimensions
import Zcash.Snark.ZeroKnowledge.HonestJointRowsSource
import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskBound
import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskCost
import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskSource
import Zcash.Snark.ZeroKnowledge.MaterializeRowsCost
import Zcash.Snark.ZeroKnowledge.PlonkCommitmentPointsCost
import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaBound
import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaCost
import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaSource
import Zcash.Snark.ZeroKnowledge.PrivateColumnAtCost
import Zcash.Snark.ZeroKnowledge.StoredFirstOpeningCost
import Zcash.Snark.ZeroKnowledge.StoredMultiopenBlindCost
import Zcash.Snark.ZeroKnowledge.StoredMultiopenDataBound
import Zcash.Snark.ZeroKnowledge.StoredMultiopenDataCost
import Zcash.Snark.ZeroKnowledge.HonestIpaBound
import Zcash.Snark.ZeroKnowledge.HonestIpaCost
import Zcash.Snark.ZeroKnowledge.HonestIpaRoundBound
import Zcash.Snark.ZeroKnowledge.HonestIpaTapeCost
import Zcash.Snark.ZeroKnowledge.IpaCoreMessagesBound
import Zcash.Snark.ZeroKnowledge.IpaCoreMessagesCost
import Zcash.Snark.ZeroKnowledge.IpaCrossTermCost
import Zcash.Snark.ZeroKnowledge.IpaCrossTermsCost
import Zcash.Snark.ZeroKnowledge.IpaFinalBlindCost
import Zcash.Snark.ZeroKnowledge.IpaFoldReaderCost
import Zcash.Snark.ZeroKnowledge.IpaTapeCost
import Zcash.Snark.ZeroKnowledge.IpaWitnessInputsBound
import Zcash.Snark.ZeroKnowledge.IpaWitnessInputsCost
import Zcash.Snark.ZeroKnowledge.SparseIpaCoefficientCost
import Zcash.Snark.ZeroKnowledge.VectorCommitmentCost
import Zcash.Snark.ZeroKnowledge.DenseLagrangeCost
import Zcash.Snark.ZeroKnowledge.DenseMultiopenFinalBound
import Zcash.Snark.ZeroKnowledge.DenseMultiopenFinalCost
import Zcash.Snark.ZeroKnowledge.DenseMultiopenQuotientCost
import Zcash.Snark.ZeroKnowledge.DenseOpeningQuotientBounds
import Zcash.Snark.ZeroKnowledge.DenseOpeningQuotientCost
import Zcash.Snark.ZeroKnowledge.DensePolynomialEvaluation
import Zcash.Snark.ZeroKnowledge.LagrangePolynomialTotal
import Zcash.Snark.ZeroKnowledge.OpeningBlindMembersBound
import Zcash.Snark.ZeroKnowledge.OpeningBlindMembersCost
import Zcash.Snark.ZeroKnowledge.OpeningGroupBlindCost
import Zcash.Snark.ZeroKnowledge.OpeningRowProviderBounds
import Zcash.Snark.ZeroKnowledge.PlonkOpeningMaterialBound
import Zcash.Snark.ZeroKnowledge.PlonkOpeningMaterialCost
import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsBound
import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsCapacity
import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsCost
import Zcash.Snark.ZeroKnowledge.ScalarHornerCost
import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
import Zcash.Snark.ZeroKnowledge.StoredPlonkOpeningGroupCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkOpeningGroupsCost
import Zcash.Snark.ZeroKnowledge.DenseCollapsedQuotientCost
import Zcash.Snark.ZeroKnowledge.DenseDomainPieces
import Zcash.Snark.ZeroKnowledge.DenseOpeningGroupCost
import Zcash.Snark.ZeroKnowledge.DenseOpeningPolynomialCost
import Zcash.Snark.ZeroKnowledge.DensePolynomialFold
import Zcash.Snark.ZeroKnowledge.DensePolynomialSum
import Zcash.Snark.ZeroKnowledge.DenseQuotientPieces
import Zcash.Snark.ZeroKnowledge.DenseWeightedSum
import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutProperties
import Zcash.Snark.ZeroKnowledge.PlonkQuotientRowsBound
import Zcash.Snark.ZeroKnowledge.PlonkQuotientRowsCost
import Zcash.Snark.ZeroKnowledge.PrivateCoefficientRoutingCost
import Zcash.Snark.ZeroKnowledge.PrivatePolynomialCoefficientsCost
import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.DensePolynomialScale
import Zcash.Snark.ZeroKnowledge.DensePolynomialMultiply
import Zcash.Snark.ZeroKnowledge.DensePolynomialDivision
import Zcash.Snark.ZeroKnowledge.MonicQuotientComposition
import Zcash.Snark.ZeroKnowledge.DistinctListCost
import Zcash.Snark.ZeroKnowledge.DenseRootDivision
import Zcash.Snark.ZeroKnowledge.DenseVanishingDivision
import Zcash.Snark.ZeroKnowledge.DenseRowPolynomial
import Zcash.Snark.ZeroKnowledge.DenseDomainDivision
import Zcash.Snark.ZeroKnowledge.DenseCoefficientBlocks
import Zcash.Snark.ZeroKnowledge.DensePolynomialRotate
import Zcash.Snark.ZeroKnowledge.CosetPolynomial
import Zcash.Snark.ZeroKnowledge.CosetCoefficientCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkHxCost
import Zcash.Snark.ZeroKnowledge.PlonkNumeratorEvalCost
import Zcash.Snark.ZeroKnowledge.PlonkNumeratorEvalBound
import Zcash.Snark.ZeroKnowledge.PlonkNumeratorSampleCost
import Zcash.Snark.ZeroKnowledge.PlonkNumeratorCoefficientsCost
import Zcash.Snark.ZeroKnowledge.PlonkNumeratorCoefficientsBound
import Zcash.Snark.ZeroKnowledge.BatchedTapeCost
import Zcash.Snark.ZeroKnowledge.BatchedTapeLists
import Zcash.Snark.ZeroKnowledge.ColumnTapeLists
import Zcash.Snark.ZeroKnowledge.PlonkBatchPreparationCost
import Zcash.Snark.ZeroKnowledge.PlonkCoinLayoutCost
import Zcash.Snark.ZeroKnowledge.PlonkPreIpaCoinsCost
import Zcash.Snark.ZeroKnowledge.PlonkPreIpaCoinsCostBound
import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCostBound
import Zcash.Snark.ZeroKnowledge.PreIpaTapeLists
import Zcash.Snark.ZeroKnowledge.PrivateColumnBatchesCost
import Zcash.Snark.ZeroKnowledge.TapeList
import Zcash.Snark.ZeroKnowledge.TapeSplitCost
import Zcash.Snark.ZeroKnowledge.OptionalRowCost
import Zcash.Snark.ZeroKnowledge.PlonkColumnConstructorCost
import Zcash.Snark.ZeroKnowledge.PlonkColumnCostBudget
import Zcash.Snark.ZeroKnowledge.PlonkColumnMaterializeCost
import Zcash.Snark.ZeroKnowledge.PlonkColumnReaderCost
import Zcash.Snark.ZeroKnowledge.PlonkColumnRecipesCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupStoredRowsCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnBudgetMono
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnCostBound
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnsCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnsCostBound
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceCost
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceCostBound
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceResult
import Zcash.Snark.ZeroKnowledge.StoredRowMaskCost
import Zcash.Snark.ZeroKnowledge.TotalRowCost
import Zcash.Snark.ZeroKnowledge.FiniteProductCost
import Zcash.Snark.ZeroKnowledge.PermutationFactorCost
import Zcash.Snark.ZeroKnowledge.PermutationRowProductCost
import Zcash.Snark.ZeroKnowledge.PermutationRowProductCostBound
import Zcash.Snark.ZeroKnowledge.PermutationRowProductCostMono
import Zcash.Snark.ZeroKnowledge.PlonkPermutationPairCost
import Zcash.Snark.ZeroKnowledge.PlonkPermutationPairCostBound
import Zcash.Snark.ZeroKnowledge.PlonkPermutationFactorsCost
import Zcash.Snark.ZeroKnowledge.PlonkPermutationFactorsCostBound
import Zcash.Snark.ZeroKnowledge.PlonkPermutationProductCost
import Zcash.Snark.ZeroKnowledge.PlonkPermutationProductCostBound
import Zcash.Snark.ZeroKnowledge.RowObservationCost
import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCost
import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCostBound
import Zcash.Snark.ZeroKnowledge.PlonkLookupCompressionCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupCompressionCostBound
import Zcash.Snark.ZeroKnowledge.PlonkLookupSortCost
import Zcash.Snark.ZeroKnowledge.PrivatePolynomialEvalCost
import Zcash.Snark.ZeroKnowledge.PrivateRowValueCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupProductCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupProductCostBound
import Zcash.Snark.ZeroKnowledge.ListTraversalCost
import Zcash.Snark.ZeroKnowledge.LookupPlanCost
import Zcash.Snark.ZeroKnowledge.LookupSortCost
import Zcash.Snark.ZeroKnowledge.LookupSortCostBound
import Zcash.Snark.ZeroKnowledge.LookupSortRowsCost
import Zcash.Snark.ZeroKnowledge.RunningProductCost
import Zcash.Snark.ZeroKnowledge.ActivationCoverageScan
import Zcash.Snark.ZeroKnowledge.ActivationCoverageData
import Zcash.Snark.ZeroKnowledge.GateIndexedCoverage
import Zcash.Snark.ZeroKnowledge.CanonicalOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredJointTraceSize
import Zcash.Snark.ZeroKnowledge.ProtocolObserverCost
import Zcash.Snark.ZeroKnowledge.StoredIpaReadCost
import Zcash.Snark.ZeroKnowledge.StoredJointProofCost
import Zcash.Snark.ZeroKnowledge.StoredJointProofBound
import Zcash.Snark.ZeroKnowledge.StoredJointTraceCost
import Zcash.Snark.ZeroKnowledge.ChallengeScheduleCost
import Zcash.Snark.ZeroKnowledge.OracleReplayCost
import Zcash.Snark.ZeroKnowledge.ProtocolPrefixCost
import Zcash.Snark.ZeroKnowledge.QueryAddressCost
import Zcash.Snark.ZeroKnowledge.CanonicalObserverCost
import Zcash.Snark.ZeroKnowledge.JointViewSize
import Zcash.Snark.ZeroKnowledge.CanonicalOracleReportCost
import Zcash.Snark.ZeroKnowledge.StoredDigestPrefixCost
import Zcash.Snark.ZeroKnowledge.ScalarEncodingCost
import Zcash.Snark.ZeroKnowledge.PointEncodingCost
import Zcash.Snark.ZeroKnowledge.TranscriptEncodingCost
import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost
import Zcash.Snark.ZeroKnowledge.TranscriptArgumentBlocksCost
import Zcash.Snark.ZeroKnowledge.ProofFieldReadCost
import Zcash.Snark.ZeroKnowledge.TranscriptScheduleCost
import Zcash.Snark.ZeroKnowledge.TranscriptScheduleSize
import Zcash.Snark.ZeroKnowledge.TranscriptScheduleBound
import Zcash.Snark.ZeroKnowledge.ProofRecordProducerCost
import Zcash.Snark.ZeroKnowledge.RoutedProofCost
import Zcash.Snark.ZeroKnowledge.RoutedProofBound
import Zcash.Snark.ZeroKnowledge.StoredChallengePrices
import Zcash.Snark.ZeroKnowledge.PlonkJointPriceBudget
import Zcash.Snark.ZeroKnowledge.PlonkCoinReadCost
import Zcash.Snark.ZeroKnowledge.PlonkCoinReadBound
import Zcash.Snark.ZeroKnowledge.PlonkChallengeReadCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeBound
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCostBound
import Zcash.Snark.ZeroKnowledge.PlonkJointStoredBounds
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorBudget
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCost
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost
import Zcash.Snark.ZeroKnowledge.IpaPreparedInputCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkKeyCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkSetupCost
import Zcash.Snark.ZeroKnowledge.StoredBitTapeCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimInputsCost
import Zcash.Snark.ZeroKnowledge.PermutationQueryPreparationCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupInputsCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimQueriesCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimInputBounds
import Zcash.Snark.ZeroKnowledge.PlonkPreparedConstraintBudget
import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCostBound
import Zcash.Snark.ZeroKnowledge.PlonkConstraintListLength
import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCost
import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCostBound
import Zcash.Snark.ZeroKnowledge.PublicOpeningCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningCostBound
import Zcash.Snark.ZeroKnowledge.PrivateOpeningPointCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningPointsCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningCommitmentCost
import Zcash.Snark.ZeroKnowledge.OpeningCommitmentVectorCost
import Zcash.Snark.ZeroKnowledge.PrivateOpeningNodesCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningValueCost
import Zcash.Snark.ZeroKnowledge.OpeningScalarVectorsCost
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.OpeningEvaluationSetsCost
import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost
import Zcash.Snark.ZeroKnowledge.CollapsedQuotientPointCost
import Zcash.Snark.ZeroKnowledge.PlonkMaskSimulatorCost
import Zcash.Snark.ZeroKnowledge.PrivateOpeningEvaluationCost
import Zcash.Snark.ZeroKnowledge.QueryOrderCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningClaimsCost
import Zcash.Snark.ZeroKnowledge.RowCoefficientCost
import Zcash.Snark.ZeroKnowledge.RowPolynomialCost
import Zcash.Snark.ZeroKnowledge.InterpolationWeightCost
import Zcash.Snark.ZeroKnowledge.LagrangeEvaluationCost
import Zcash.Snark.ZeroKnowledge.MultiopenEvaluationCost
import Zcash.Snark.ZeroKnowledge.MultiopenCombinationCost
import Zcash.Snark.ZeroKnowledge.ListIndexCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.CommitmentEntryCost
import Zcash.Snark.ZeroKnowledge.FieldExponentCost
import Zcash.Snark.ZeroKnowledge.LagrangeBasisCost
import Zcash.Snark.ZeroKnowledge.ListRoutingCost
import Zcash.Snark.ZeroKnowledge.PermutationBoundaryCost
import Zcash.Snark.ZeroKnowledge.PermutationExpressionsCost
import Zcash.Snark.ZeroKnowledge.QuotientEvaluationCost
import Zcash.Snark.ZeroKnowledge.ListCollectedCost
import Zcash.Snark.ZeroKnowledge.ConstraintAssemblyCost
import Zcash.Snark.ZeroKnowledge.ConstraintCollectionCost
import Zcash.Snark.ZeroKnowledge.QueryRoutingCost
import Zcash.Snark.ZeroKnowledge.IpaScalarCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaSimulatorCost
import Zcash.Snark.ZeroKnowledge.ExpressionCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.ZeroKnowledge.PolynomialArithmeticCost
import Zcash.Snark.ZeroKnowledge.CommitmentArithmeticCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ExpressionCompressionCost
import Zcash.Snark.ZeroKnowledge.LookupExpressionsCost
import Zcash.Snark.ZeroKnowledge.PermutationChunkCost
import Zcash.Snark.ZeroKnowledge.PublicFoldCost
import Zcash.Snark.ZeroKnowledge.PlonkCopyValues
import Zcash.Snark.ZeroKnowledge.CompiledLookupCompleteness
import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.SourcePartialValue
import Zcash.Snark.ZeroKnowledge.CopySourceCompleteness
import Zcash.Snark.ZeroKnowledge.ActionWitnessLoadCertificate
import Zcash.Snark.ZeroKnowledge.MerkleHintExtraction
import Zcash.Snark.ZeroKnowledge.InactiveSelectorReplacement
import Zcash.Snark.ZeroKnowledge.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.GateActivationCoverage
import Zcash.Snark.ZeroKnowledge.CompiledGateCompleteness
import Zcash.Snark.ZeroKnowledge.InactiveGateCompleteness
import Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate
import Zcash.Snark.ZeroKnowledge.WideBitReductionCost
import Zcash.Snark.ZeroKnowledge.AdviceAliasAddressPlan
import Zcash.Snark.ZeroKnowledge.AdviceAliasMap
import Zcash.Snark.ZeroKnowledge.AdviceAliasMapPlan
import Zcash.Snark.ZeroKnowledge.AdviceSupportMapPlan
import Zcash.Snark.ZeroKnowledge.AdviceMapScan
import Zcash.Snark.ZeroKnowledge.AdviceReadAddressScan
import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Snark.ZeroKnowledge.PoseidonWitnessSupport
import Zcash.Snark.ZeroKnowledge.MulIncompleteWitnessSupport
import Zcash.Snark.ZeroKnowledge.MulCompleteWitnessSupport
import Zcash.Snark.ZeroKnowledge.FixedBaseWitnessSupport
import Zcash.Snark.ZeroKnowledge.FixedCanonicityWitnessSupport
import Zcash.Snark.ZeroKnowledge.NoteWitnessSupport
import Zcash.Snark.ZeroKnowledge.NoteCanonicityWitnessSupport
import Zcash.Snark.ZeroKnowledge.CommitIvkWitnessSupport
import Zcash.Snark.ZeroKnowledge.SinsemillaWitnessSupport
import Zcash.Snark.ZeroKnowledge.MerkleWitnessSupport
import Zcash.Snark.ZeroKnowledge.NativeScalarWitnessSupport
import Zcash.Snark.ZeroKnowledge.AdviceSupportPlan
import Zcash.Snark.ZeroKnowledge.ActionHintReadSupport
import Zcash.Snark.ZeroKnowledge.ProtocolCacheCost
import Zcash.Snark.ZeroKnowledge.SelectorInitialTrace
import Zcash.Snark.ZeroKnowledge.SelectorTracePlacement
import Zcash.Snark.ZeroKnowledge.SelectorReplacementSupport
import Zcash.Snark.ZeroKnowledge.Sampling
import Zcash.Snark.ZeroKnowledge.MaskPolynomials
import Zcash.Snark.ZeroKnowledge.MaskSampling
import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaAttempt
import Zcash.Snark.ZeroKnowledge.IpaRetry
import Zcash.Snark.ZeroKnowledge.IpaSimulator
import Zcash.Snark.ZeroKnowledge.IpaVerifier
import Zcash.Snark.ZeroKnowledge.LinearMaskTranscript
import Zcash.Snark.ZeroKnowledge.RowMaskTranscript
import Zcash.Snark.ZeroKnowledge.PlonkTranscript
import Zcash.Snark.ZeroKnowledge.PlonkMultiopen
import Zcash.Snark.ZeroKnowledge.PlonkSampling
import Zcash.Snark.ZeroKnowledge.PlonkSimulator
import Zcash.Snark.ZeroKnowledge.PlonkQuotientSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCapacitySimulation
import Zcash.Snark.ZeroKnowledge.PlonkDegreeCertificate
import Zcash.Snark.ZeroKnowledge.PlonkRowSimulation
import Zcash.Snark.ZeroKnowledge.PlonkConsistency
import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkFreshBounds
import Zcash.Snark.ZeroKnowledge.RunningProductRows
import Zcash.Snark.ZeroKnowledge.ProductDenominators
import Zcash.Snark.ZeroKnowledge.PlonkLookupRows
import Zcash.Snark.ZeroKnowledge.PlonkPermutationRows
import Zcash.Snark.ZeroKnowledge.LookupSortRows
import Zcash.Snark.ZeroKnowledge.LookupSortExamples
import Zcash.Snark.ZeroKnowledge.PlonkConstruction
import Zcash.Snark.ZeroKnowledge.PlonkConstructedConstraints
import Zcash.Snark.ZeroKnowledge.PlonkProductBounds
import Zcash.Snark.ZeroKnowledge.PlonkProductCertificate
import Zcash.Snark.ZeroKnowledge.PlonkConstructedSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCopySimulation
import Zcash.Snark.ZeroKnowledge.PlonkCopyCertificate
import Zcash.Snark.ZeroKnowledge.PlonkOriginalSimulation
import Zcash.Snark.ZeroKnowledge.PlonkMaskCertificate
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSimulation
import Zcash.Snark.ZeroKnowledge.PlonkSelectorSimulation
import Zcash.Snark.ZeroKnowledge.Observation
import Zcash.Snark.ZeroKnowledge.PlonkDisclosure
import Zcash.Snark.ZeroKnowledge.PlonkUnusedCertificate
import Zcash.Snark.ZeroKnowledge.PlonkUnusedKeygen
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSimulation
import Zcash.Snark.ZeroKnowledge.PlonkAttemptSimulation
import Zcash.Snark.ZeroKnowledge.PlonkFailures
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSuccess
import Zcash.Snark.ZeroKnowledge.PlonkCompilerRetry
import Zcash.Snark.ZeroKnowledge.PlonkCausality
import Zcash.Snark.ZeroKnowledge.IpaCausality
import Zcash.Snark.ZeroKnowledge.PlonkSigmaCertificate
import Zcash.Snark.ZeroKnowledge.PlonkEncoding
import Zcash.Snark.ZeroKnowledge.PlonkBinaryBounds
import Zcash.Snark.ZeroKnowledge.PlonkCompleteness
import Zcash.Snark.ZeroKnowledge.PlonkCommitmentRouting
import Zcash.Snark.ZeroKnowledge.PlonkQueryBlocks
import Zcash.Snark.ZeroKnowledge.GroupingSlots
import Zcash.Snark.ZeroKnowledge.PlonkVerifierGrouping
import Zcash.Snark.ZeroKnowledge.PlonkQueryCertificate
import Zcash.Snark.ZeroKnowledge.PlonkEvaluationCompression
import Zcash.Snark.ZeroKnowledge.PlonkVerifierOpening
import Zcash.Snark.ZeroKnowledge.PlonkDerivedKey
import Zcash.Snark.ZeroKnowledge.SelectorReplacementDegree
import Zcash.Snark.ZeroKnowledge.KeygenExpressionMasking
import Zcash.Snark.ZeroKnowledge.KeygenPartialMasking
import Zcash.Snark.ZeroKnowledge.PlannerStarts
import Zcash.Snark.ZeroKnowledge.SelectorCompressionCount
import Zcash.Snark.ZeroKnowledge.SelectorBitPacking
import Zcash.Snark.ZeroKnowledge.RandomTapeSource
import Zcash.Snark.ZeroKnowledge.PrngReduction
import Zcash.Snark.ZeroKnowledge.RetryLimit
import Zcash.Snark.ZeroKnowledge.RetryExpectation
import Zcash.Snark.ZeroKnowledge.ByteFiatShamir
import Zcash.Snark.ZeroKnowledge.PlonkDigest
import Zcash.Snark.ZeroKnowledge.OracleProgrammingBias
import Zcash.Snark.ZeroKnowledge.OracleResources
import Zcash.Snark.ZeroKnowledge.PlonkOracle
import Zcash.Snark.ZeroKnowledge.PlonkAnchor
import Zcash.Snark.ZeroKnowledge.PlonkQuerySchedule
import Zcash.Snark.ZeroKnowledge.PlonkSimulatorTape
import Zcash.Snark.ZeroKnowledge.OracleContinuationResources
import Zcash.Snark.ZeroKnowledge.AnchorProbability
import Zcash.Snark.ZeroKnowledge.RawBits
import Zcash.Snark.ZeroKnowledge.OracleBitBounds
import Zcash.Snark.ZeroKnowledge.OracleRetryBounds
import Zcash.Snark.ZeroKnowledge.OracleRetryTape
import Zcash.Snark.ZeroKnowledge.OracleRetrySimulation
import Zcash.Snark.ZeroKnowledge.OracleRetryResources
import Zcash.Snark.ZeroKnowledge.PrngSecurityReduction
import Zcash.Snark.ZeroKnowledge.GeneratedRetryCoins
import Zcash.Snark.ZeroKnowledge.RetryTapeSource
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamLimit
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamTail
import Zcash.Snark.ZeroKnowledge.OracleRetryPotential
import Zcash.Snark.ZeroKnowledge.PlonkRawObservation
import Zcash.Snark.ZeroKnowledge.OracleRetryTail
import Zcash.Snark.ZeroKnowledge.RetryRecordedSource
import Zcash.Snark.ZeroKnowledge.GeneratedRetryStreamTail
import Zcash.Snark.ZeroKnowledge.MeasureBiasComposition
import Zcash.Snark.ZeroKnowledge.RetryStreamNontermination
import Zcash.Meta.AxiomCheck
import Zcash.Snark.ZeroKnowledge.WindowDigits
import Zcash.Snark.ZeroKnowledge.AdviceWitnessAssignment
import Zcash.Snark.ZeroKnowledge.CompiledFixedWitnesses
import Zcash.Snark.ZeroKnowledge.WitnessProgramSupport

import Zcash.Snark.ZeroKnowledge.AdviceAliasCollection
import Zcash.Snark.ZeroKnowledge.AdviceAliasInvariant
import Zcash.Snark.ZeroKnowledge.AdviceAliasPlan
import Zcash.Snark.ZeroKnowledge.AdviceReadPlan
import Zcash.Snark.ZeroKnowledge.AdviceWitnessTrace
import Zcash.Snark.ZeroKnowledge.NativeArithmeticCopySupport
import Zcash.Snark.ZeroKnowledge.NativeCopyComposition
import Zcash.Snark.ZeroKnowledge.NativeCopyLift
import Zcash.Snark.ZeroKnowledge.NativeCopyLoops
import Zcash.Snark.ZeroKnowledge.NativeCopyRegions
import Zcash.Snark.ZeroKnowledge.WitnessBuilderSupport
import Zcash.Snark.ZeroKnowledge.WitnessCopySemantics

/-!
# Checked trust boundary of the zero-knowledge development

These pins bound the transitive proof dependencies to Lean's standard axioms. No native-code
axiom or admitted lemma is permitted. Probability distributions are intentionally noncomputable;
the finite sampling program and its declared tape sizes are checked as computable definitions.
`+choice` permits classical choice only in erased proof fields of a plain computable definition;
the checker still rejects noncomputable algorithmic content. No `+native` exemption is used
in this census. `Vesta/TrustBoundary` and `Action/TrustBoundary` separately name the
existing curve-order dependencies of those concrete specializations.

The pinned results establish the field-sampling law, both masking constructions, joint
simulation of the IPA stage with supplied or fresh interactive challenges, and joint hiding
of masked columns. The interactive IPA comparison retains errors and emitted prefixes under
supplied codecs; an identity-rejecting codec also gives a checked successful-attempt law and
independent-retry limit. The pre-IPA comparison retains the joint column dependencies, exact
opening groups and emitted scalar order, with supplied challenges and total private constructors.
The computed multi-opening polynomial and folded blind supply a valid IPA input. The joint
pre-IPA/IPA simulation reconstructs that input from the enriched public view, given a public
quotient-evaluation function that agrees with the actual quotient on every reachable row state.
The full batched prover tape is connected to this joint law, and the joint simulator has a
field-coin implementation. The verifier-typed construction computes the constraint numerator
and quotient pieces, and derives quotient agreement using the existing verifier's constraint
function. A public circuit-degree profile supplies the numerator capacity, with
kernel-checked certificates for the one- and two-Action captured keys. Row-wise constraint
satisfaction supplies exact quotient divisibility. The newer consistency bound retains
the ideal probability of row states that fail division as an explicit error term, so it
does not assume correctness on every random state. The fresh-challenge comparison retains
the entire verifier tape, adding its exceptional-challenge probability and the average
invalid-row probability to the prover's sampling bias. With independent wide-reduced
verifier coins, the challenge term is bounded by `4113/p + 22 × bias`. The later
original-row theorem bounds the remaining row contribution using explicit witness
and public-key conditions. The later compiler and verifier-grouping connectors derive
the public commitment and routing matches under explicit shape and query-layout conditions.
The product-row scan has checked recurrence and terminal-value lemmas that retain
zero-denominator cases. Separate factor-family bounds permit a random private prefix
independent of the two product challenges. The actual reference factor lists and their
pre-product challenge independence apply that bound to the computed denominators;
their contribution to the joint invalid-row event is derived under the complete
independent challenge law.
The computed lookup scan supplies all five of the existing row constraints from
the compression, permutation, and run-structure facts outside zero denominators.
The actual polynomial selectors and rotations carry this result to domain division.
The specified canonical sorter supplies the permutation and run-structure facts,
and succeeds for equal-length prefixes whenever each input value occurs in the table.
Its field-specific adapter feeds those facts directly to the existing lookup constraints.
The concrete retained-row constructor evaluates lookup expressions and packed
permutation factors through the existing polynomial query layout, then calls those
sorts and scans. Its partial schedule preserves sorting failures and the private
prefix. Completed attempts agree on the same tape with the total constructor used
by the joint simulation, and every constructed column retains its computed usable
rows with the actual preceding masked history. Lookup construction uses only theta;
all row construction uses only theta, beta, and gamma. The phase bounds identify
every construction-time read with the final column state, including rotated queries.
Completed attempts supply one common lookup-sort result and every product scan through
the terminal row. These computed rows give all fifteen lookup and seven permutation
constraint polynomials per Action, outside zero denominator factors and given the packed
copy-product identity. Gate correctness then gives domain division for every constraint
and for the actual numerator. The retained-row correspondence also covers produced
columns in failed prefixes, without conditioning a probability law on success.
The first sixteen columns per Action are pointwise independent of beta, gamma, and
later challenges on a fixed tape. Every actual product denominator factor occurs in
the computed lists. With fifteen packed key references, fresh independent wide-reduced
product coins give a zero-denominator bound of `42882m/p + 2 × bias`, also under any
independent prior private-state law. Both captured keys have kernel-checked three-chunk,
fifteen-reference certificates. Completed partial attempts inherit the event
bound without conditioning on success. The fixed-size uniform row tape realizes the
sequential law already used by the joint simulation.
Exact reordering of independent challenge draws separates beta and gamma from the
other wide-reduced coins without charging the whole verifier tape's bias again.
The averaged invalid-row event is exactly the computed row-tape experiment; it is
covered by failed construction, gate or copy-product prerequisites, and zero
denominators. The resulting concrete joint comparison has error at most
`prerequisiteFailureMass + (42882m + 4113)/p + (148m + 70) × bias`.
Usable advice rows are preserved on every total-construction tape. Both captured
permutation layouts use only unrotated advice queries, so their computed usable factors
equal the original witness factors. Original copy equations propagate through the
replayed copy permutation; public sigma coherence then gives the exact packed product
identity for every challenge and tape. Under these explicit witness and key premises,
the prerequisite mass equals `gateConstructionFailureMass`, and the joint bound carries
only that remaining row error. A public expression checker proves invariance under
changes to unretained advice, including products killed by fixed zero selectors.
The exact modular rotation rules identify every retained query. Original gate validity
and lookup tuple membership then give masked gate division and compressed lookup
membership on every tape. The successful sorts make the actual partial column runner
complete on that same tape, so `gateConstructionFailureMass` is zero. The resulting
joint reference bound is `(42882m + 4113)/p + (148m + 70) × bias`, given those original
witness conditions and the public masking/copy profiles. All interior rows pass the
mask check automatically; both captured keys have kernel certificates for the eight
remaining boundary rows with the stated captured fixed-query values. Matching those
values to the supplied public polynomials and connecting the concrete key's shape,
layout, and expression conditions remain explicit obligations. The ordered compiler
copy-list, sigma-row, and public commitment adapters are checked below. The
public-row constructor supplies all public polynomial degree bounds. For fixed
rows produced by the circuit compiler, a structural proof derives zero throughout
the masked suffix from the bounds on table, constant, selector, and region writes.
This connects six boundary rows to actual keygen and leaves a finite mask check that
reads only rows 0 and 2041 from the compiler. The keygen reference endpoint uses these
constructed polynomials. The selector-only certificates further leave all fourteen
original fixed columns unknown, and a compiler support theorem makes packed selectors
zero from the V1 placement endpoint onward. Given the public column/placement bounds,
only four initial packed-selector zeros remain to be established for the Action circuit.
Relating the supplied instance/sigma rows and public commitments to the deployed key
also remains open. The
sampling comparison alone is not a simulator for failed attempts. The proof string's
terminal rotations use the kernel root certificate.
The complete typed reference proof exposes each usable advice cell at its domain
challenge on every private tape. The exact mass of this joint challenge/scalar event
separates the full reference laws of row vectors with different usable cells. Under
wide-reduced challenges the lower bound is positive. A common exact simulator for
those two laws is impossible. The inactive-expression certificates for both captured
keys allow a second valid reference witness to be constructed from any first one:
add one to an advice cell in row 2000, assuming placement ends by row 1999 and copies
avoid the changed row. The gate, lookup, and copy relation is preserved for the same
public statement. The compiler refinement computes the complete ordered V1 copy list,
including deferred constants, and packs its endpoint coordinates into the prover's cell
type. Re-encoding is the identity on the source list. With fifteen permutation columns,
the checked seven/seven/one widths, and an operation footprint ending by row 1999, the
compiler supplies both placement and the unused-row copy condition. The later sigma
refinement embeds usable packed cells into the full rectangular table and transports
the exact ordered replay through that injection. The existing array/union-find theorem
then identifies every compiler sigma row with its replayed-cell name. Both captured
keys have kernel certificates for the sigma indices, delta, and chunk stride. The newest
joint statistical theorem and unused-row counterexample construct the fixed and sigma
polynomials and copies from keygen; sigma coherence is derived. Original gate, lookup,
and copy-value validity, public size bounds, and initial selector zeros for the positive
theorem remain premises. The Action public-input layout and compiler public-commitment
correspondence are derived below; concrete key shape and query-layout checks remain.
The full attempt observer reuses the existing verifier's message schedule and
retains encoded prefixes, received challenges, the full verifier tape, and a distinct
status for completion, identity failure, coincident opening queries, or the zero-IPA
panic. Its success criterion is
exact: every point encodes, x is nonzero, and all round challenges are nonzero. The
x check is equivalent to distinctness of the actual interpolation node lists. No
condition on xi or evaluation-domain membership is added. The same numerical joint
bound holds after this observation, without conditioning on success. The generic
interpreter also proves that appending messages after a failed prefix changes nothing.
The full failure bound is `(22m+45)/p + (148m+68) bias`. The pre-IPA points
are jointly uniform with ideal blinds, and the IPA identity bound is applied
conditionally on the entire private prefix. The actual proof's point slots are
covered by these families. Wide reduction and the `k+1` actual stopping challenges
supply the stated bound, even at exceptional challenges and without row-correctness
premises. Completion means that the emission schedule finishes, not verifier
acceptance. The successful-view capstone derives positive normalizers from these
failure and simulation bounds and proves the two-sided conditional budget
`2 epsilon / (1 - B)`, where `B = (42904m+4158)/p + (296m+138) bias`.
The numerical inequality `B < 1` is kernel-certified for `m <= 65535`, including
both captured Action counts; the general endpoint takes that inequality explicitly.
Support certificates are proofs, not witness inputs to the simulator. Independent
selection of completed attempts converges to this conditioned law, also for view
types without a Fintype instance. Separately, an auxiliary caller with a finite
independent retry budget retains all earlier failed observations. It stops on
completion or a coincident-opening error and elects to repeat point failures and
handled IPA panics. This caller is absent from the Zakura release model. Its two-sided joint
budget is `epsilon / (1 - F)`, where `F` is the honest single-attempt failure bound.
The real and simulated exhaustion probabilities are at most `F^n` and `B^n` and
tend to zero for `B < 1`. The probability recursion is proved equal to the observable
retry program on an independent attempt tape. The witness and statement stay fixed;
fresh private and verifier tapes are required for each attempt. No unlimited-run
history distribution or state-carrying caller equivalence is asserted here.
The deterministic causality interface proves that a causal message producer stays
causal under the actual observation and failure checks. The checks use only received
challenges. The IPA mask commitment ignores xi, z, and every round challenge; a round
pair depends only on strictly earlier rounds. These facts hold on every private tape,
including zero challenges and invalid openings. The complete staged schedule is
proved equal to the existing attempt trace, including empty blocks between consecutive
receives. Per-stage dependency facts suffice for causality of that complete trace and
its encoding; the final scalars require no further premise once all challenges agree.
The complete batched decoder preserves masks, coefficients, blinds, and the IPA
suffix independently of retained-row callbacks. The corresponding full-tape proof
fields satisfy their stage dependencies: advice ignores all challenges, lookup
permutation points use only theta, product points use theta, beta, gamma, the linear
mask ignores all challenges, and quotient pieces add only y. These facts establish
the entire existing attempt prefix before x on the actual complete prover tape.
The evaluation, multi-opening, and IPA stages satisfy their dependencies on that
same complete tape. The eleven-round adapter uses a challenge-independent `148m+46`
sample count and has exactly the existing wide-reduced reference-prover law. Its
entire message schedule is causal, including the encoded prefixes and actual abort
checks, for every fixed tape and every challenge value. The canonical scalar and point
codecs instantiate that observer. Each successful item has 32 bytes, and the complete
reference attempt has exactly `2720+2272m` bytes. Its fresh encoded tape law is proved
equal to the existing fresh reference distribution followed by that same observer.
The abstract blinding lemma reduces the hiding bijection to nonidentity in a field
module whose group and scalar field have equal finite cardinalities. The concrete
Vesta instantiation and captured nonidentity checks are pinned separately. The generic
results retain explicit circuit and key conditions. The readable budget `epsilon(m) < m*2^-238`
for positive Action counts follows from the sampling bound and kernel integer arithmetic.
The selector-support theorem covers zero padding outside the compiler's dimensions.
The actual
Action specialization supplies canonical public-input rows and compiler fixed/sigma
polynomials and copies. Its prefix, permutation count, and operation-footprint bounds
follow from the existing Action compilation API. Its fixed-value boundary profile
and compiler-derived key supply the masking and correspondence conditions. The actual query assembly, five
opening groups, and both compression projections feed the final opening assembly.
Under the stated query layout, distinct rotation points, domain, and public commitment
conditions, its evaluated commitment and scalar equal the reference reconstruction.
The dynamic group-count check also succeeds. For compiler-derived keys, public commitment
agreement follows from the existing FFT and Lagrange commitment theorems, with the
kernel-checked domain root shared from the arithmetic layer. Shape and query layout
supply all fixed and sigma column coverage and the reference domain values. The Action
specialization derives its instance and sigma commitment equalities from the concrete
compiler. Its configure program determines the advice and instance queries,
permutation columns, and degree-derived dimensions. Given fifteen compressed selector
columns, it supplies the full reference key shape, fixed-query order, domain, sigma
naming, and copy-query conditions to the opening and encoded simulation theorems.
The full Action degree profile is derived: the greedy packer preserves each
selector's source-degree budget, the replacements fit their combination lengths,
and source expression bounds survive compilation. Structural source certificates
also survive selector substitution and the complete expression compiler. The checked
sort, placement, activation trace, and greedy packing establish the compression count.
Every previous-row guard is inactive at row zero, and its replacement polynomial
vanishes there even when another selector shares its column. ActionBoundaryProfile
derives the full compiled masking check from these actual fixed values.
These equalities do not assert verifier acceptance. The concrete Action results have a
separate census for their inherited Pallas order dependency.
ActionFiatShamir supplies the separate programmable classical random-oracle argument;
Rust execution correspondence is a separate claim, outside the protocol theorem's target.
-/

assert_computable Zcash.Snark.ZeroKnowledge.fieldSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.wordSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.sampleFieldsWith
assert_computable Zcash.Snark.ZeroKnowledge.splitTapeEquiv +choice

assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.idealFieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_apply
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_weightedBias
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_bias_le
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_remainder_pos
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_zero_gt_light
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_ideal
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_one
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_two
assert_axioms Zcash.Snark.ZeroKnowledge.weightedBias_symm
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_map
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_const
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_coordinate
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_error_bound

assert_axioms Zcash.Snark.ZeroKnowledge.independentTapeLaw
assert_axioms Zcash.Snark.ZeroKnowledge.independentTapeLaw_map
assert_axioms Zcash.Snark.ZeroKnowledge.independentTapeLaw_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_eq_independentTape
assert_axioms Zcash.Snark.ZeroKnowledge.RawPrivateTape
assert_computable Zcash.Snark.ZeroKnowledge.reducePrivateTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRawPrivateTape_reduce
assert_axioms Zcash.Snark.ZeroKnowledge.sourceTapeExperiment
assert_axioms Zcash.Snark.ZeroKnowledge.sourceTapeExperiment_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sourceTapeExperiment_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.seededTapeSource
assert_axioms Zcash.Snark.ZeroKnowledge.tapeReduction
assert_axioms Zcash.Snark.ZeroKnowledge.tapeReduction_law
assert_axioms Zcash.Snark.ZeroKnowledge.seededTape_test_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledAttempt_error_bound

-- Common #225: derive the sparse polynomial and the full scalar from the recursive fold.
assert_computable Zcash.Snark.ZeroKnowledge.coefficientFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.foldByRounds +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaCoefficients +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedIpaScalar +choice
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_coefficientFold
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_powerIndex
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.coeffsToPoly_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial_eval_root
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientEvaluation_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq_zero_of_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_simulates
assert_axioms Zcash.Snark.ZeroKnowledge.actualSparseIpaScalar_error_bound

-- Common #267: retain the already disclosed evaluation and the unit-weight contribution.
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPair
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskView
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPolynomial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPolynomial_evaluations
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPair_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskView_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_unit_weight
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_at_zero
assert_axioms Zcash.Snark.ZeroKnowledge.actualLinearMaskView_error_bound

-- Joint Common #267 projection: R, r(x), the Q' commitment, and the later group evaluation.
assert_computable Zcash.Snark.ZeroKnowledge.blindedCommitments
assert_computable Zcash.Snark.ZeroKnowledge.LinearMaskTranscript.ofParts
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskCommitmentCores
assert_computable Zcash.Snark.ZeroKnowledge.honestLinearMaskTranscript
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskTranscriptFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskSimulatorFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.blindedCommitments_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.commitmentView_eq
assert_axioms Zcash.Snark.ZeroKnowledge.idealLinearMask_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskTapeEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeLinearMask_eq_idealProver
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskSimulatorFromTape_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledLinearMask_simulation_error_bound

-- The joint IPA view includes the actual cross terms and the aggregate blind, not just `c`.
assert_computable Zcash.Snark.ZeroKnowledge.publicFold
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTerms +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaCoreMessages +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMessageSum +choice
assert_computable Zcash.Snark.ZeroKnowledge.blindIpaMessages
assert_computable Zcash.Snark.ZeroKnowledge.ipaFinalBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskedVector +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.completeIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.chooseIpaScalar +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.ipaTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTerms_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessages_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_blind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskedVector_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.completeIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.IpaTranscript.eq_complete_of_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.ipaBlindsEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_fixed_mask
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpa_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.blinding_bijective_of_card_eq
assert_axioms Zcash.Snark.ZeroKnowledge.chooseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaSimulatorFromFieldCoins_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eleven
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_alphas
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_maskBlind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_roundBlinds
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeIpa_eq_idealProver
assert_axioms Zcash.Snark.ZeroKnowledge.sampledIpaProver_ideal_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledIpa_simulation_error_bound

-- Fresh interactive challenges, including zero challenges and partial output on errors.
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublic.withChallenges
assert_computable Zcash.Snark.ZeroKnowledge.ipaNonzeroChallengeIndex
assert_computable Zcash.Snark.ZeroKnowledge.observeIpaRounds +choice
assert_computable Zcash.Snark.ZeroKnowledge.observeIpaAttempt +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaAttemptObservation +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.uniformIpaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshIpa_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaAttempt_mask_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_right_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_zero_challenge
assert_axioms Zcash.Snark.ZeroKnowledge.observedIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideObservedIpa_simulation_error_bound

-- Success normalization is derived from the actual observer's failures and retry semantics.
assert_computable Zcash.Snark.ZeroKnowledge.ipaPointFamily
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.pointFamily
assert_computable Zcash.Snark.ZeroKnowledge.ipaPointBlindsIndex
assert_computable Zcash.Snark.ZeroKnowledge.ipaSuccessSet +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaTranscriptEquiv
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaPoints_fixed_mask
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaPoints_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaPoint_identity_mass
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSuccess_iff
assert_axioms Zcash.Snark.ZeroKnowledge.uniformIpaRounds_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaRounds_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshIpa_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRetryFailureBound_eleven_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.successfulIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpa_retry_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpa_eleven_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.IpaPublic.exists_opening
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaSimulator_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.wideSuccessfulIpa_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.encodedIpa_retries_tendsto

-- The simulated raw equation is the existing verifier's final IPA assembly.
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublic.ofMsm +choice
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.ofProofString
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_eq_foldAll
assert_axioms Zcash.Snark.ZeroKnowledge.computeS_gterm_publicFold
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_evalVector
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_eq_roundSum
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_verifier_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_assembleFinalMsm

-- Joint replacement-row rank, with the real domain constant certified without native axioms.
assert_axioms Zcash.Arithmetic.rootOfUnityFp_primitiveRoot
assert_axioms Zcash.Arithmetic.omegaOf_isPrimitiveRoot
assert_axioms Zcash.Snark.ZeroKnowledge.rootOfUnityFp_primitiveRoot
assert_axioms Zcash.Snark.ZeroKnowledge.omegaOf_primitiveRoot
assert_axioms Zcash.Snark.ZeroKnowledge.omegaOf_rows_injective
assert_computable Zcash.Snark.ZeroKnowledge.maskedRows
assert_computable Zcash.Snark.ZeroKnowledge.maskedRowPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.advicePolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskRowsLinearMap +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowMaskIndexEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowMaskTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowEvaluationsFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedColumnCommitmentCore +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedColumnFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowMask_interpolationNodes_injective
assert_axioms Zcash.Snark.ZeroKnowledge.rowMask_evaluations_surjective
assert_axioms Zcash.Snark.ZeroKnowledge.rowEvaluationLinearMap_apply
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRows_decompose
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRowPolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.rowMaskTapeEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.sampledRowEvaluations_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.advicePolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.productRowPolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeEquiv_blind
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeMaskedColumn
assert_axioms Zcash.Snark.ZeroKnowledge.maskedColumn_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledMaskedColumn_error_bound

-- Successive private columns and the source's batched field tape.
assert_computable Zcash.Snark.ZeroKnowledge.columnRowSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.columnRowsFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnRowsFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.observeColumnRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.firstTapeEquiv
assert_computable Zcash.Snark.ZeroKnowledge.columnFullSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.columnCoinEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnMaterialFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchToColumnTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedColumnSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.batchedToColumnTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedPreIpaTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnOrder
assert_computable Zcash.Snark.ZeroKnowledge.PrivateColumnId.firstMasked
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnSteps
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnBatches
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnBatches
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowSampleCount_eq_sum
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_length
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnRows
assert_axioms Zcash.Snark.ZeroKnowledge.idealColumnRows_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledColumnRows_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.columnFullSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_cons_apply
assert_axioms Zcash.Snark.ZeroKnowledge.columnMaterialFromTape_eq
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnMaterial
assert_axioms Zcash.Snark.ZeroKnowledge.columnFullSampleCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.batchToColumnTape_fields
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrder_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_row_samples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumns_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkColumns_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnBatches_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_sample_count
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_and_ipa_sample_count

-- Joint pre-IPA hiding, retaining all points and correlations among scalar disclosures.
assert_computable Zcash.Snark.ZeroKnowledge.preIpaSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.preIpaCoinEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPreIpaMaskView +choice
assert_computable Zcash.Snark.ZeroKnowledge.preIpaMaskViewFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedPreIpaViewFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaMaskViewFromTape_factor
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePreIpaMaskView
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaScalarView_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealPreIpaMask_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPreIpaMask_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeBatchedPreIpa
assert_axioms Zcash.Snark.ZeroKnowledge.sampledBatchedPreIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkPreIpa_simulation_error_bound

-- The pinned opening-polynomial groups and actual step-5/step-6 scalar computations.
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservationPoints +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFixedQueryOrder
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceQueryOrder
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFixedQueryOrder_eq_vecCons
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryOrder_eq_vecCons
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupPrefix +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateGroupMembers
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningGroups +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupOffset +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateGroupValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkEvaluationScalars +choice
assert_computable Zcash.Snark.ZeroKnowledge.PlonkPreIpaTranscript.messages
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaProjection +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkPreIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscriptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnView_observe
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFirstGroup_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFirstGroup_linearMaskView
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPrivateGroupValues_observe
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkPreIpaTranscript_projection
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscriptFromTape_factor
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkPreIpaTranscript_simulation

-- Computed multi-opening quotients, polynomial commitments, and the actual incoming IPA blind.
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCoefficients +choice
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCommitment +choice
assert_computable Zcash.Snark.ZeroKnowledge.commitmentHornerFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.values +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.interpolant +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.forVerifier +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenFinalPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenFinalBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenGroupMsm +choice
assert_computable Zcash.Snark.ZeroKnowledge.computedMultiopenOpening +choice
assert_computable Zcash.Snark.ZeroKnowledge.computedMultiopenIpaPublic +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotientBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPairs +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroup +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroups +choice
assert_axioms Zcash.Snark.ZeroKnowledge.coeffsToPoly_polynomialCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientEvaluation_polynomialCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficients_horner
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_zero
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_horner
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_sum
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_fold
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.residual_eval
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing_monic
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.opening_denominator_fold
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_eval
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial_eval
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenOpening_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenOpening_value
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenFinalPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenIpaPublic_validOpening
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenIpaPublic_eq_verifier
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_away
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPairs_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroup_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningGroups_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomials_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMultiopenIpa_validOpening
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMultiopenIpa_simulation
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkMultiopenIpa_simulation

-- Actual commitment cores and public reconstruction of the IPA input.
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnIndex
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnAt
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPointIndices
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialOpeningGroups +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkLinearEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkPieceEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPrimeEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentBlindsFromVector
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentCores +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkMaskView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotientPoint +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicCommitmentMembers +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicGroupCommitments +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupClaims +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicNodeValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicOpening +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicIpaInput +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrder_mem
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnAt_index
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_eq_map
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroups_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_column
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_linear
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_piece
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_quotientPrime
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_points
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_columns
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_groupValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicCommitmentMembers_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicGroupCommitments_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicNodeValues_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicOpening_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicIpaInput_honest

-- Joint simulation through the actual private state and complete batched field tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkIpaData +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointViewFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskSimulatorFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSimulatorFromCoins +choice
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_rows_mem
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_maskView
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_maskView_simulation
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkMaterial
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkJoint
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.uniformColumnViews_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaskSimulatorFromFieldCoins_eq
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJointSimulatorFromFieldCoins_program
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJointSimulatorFromFieldCoins_eq

-- The actual constraint calculation, computed quotient, and existing proof-string output.
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofShape
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofString
assert_computable Zcash.Snark.ZeroKnowledge.plonkClaimProof
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofFromJointView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierHx +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryFactors +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkRotatedColumn +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkSelectors +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstraintModel +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator +choice
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlock +choice
assert_computable Zcash.Snark.ZeroKnowledge.domainQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPieces +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkHonestQuotientPieces +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofShape_eleven
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_allExpressions
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierHx_proof
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eq_fold
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eval_div
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlock_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlocks_recombine
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlocks_eval
assert_axioms Zcash.Snark.ZeroKnowledge.domainQuotient_natDegree
assert_axioms Zcash.Snark.ZeroKnowledge.domainQuotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPieces_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_natDegree
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPieces_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkHonestQuotient_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_simulation_error_bound

-- Quotient capacity follows from public syntax rather than a private-state degree premise.
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLagrangePolynomials_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.constraintModel_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkDegreeProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkDegreeProfile
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_capacity_simulation_error_bound

-- Row-wise constraint satisfaction supplies exact domain division.
assert_axioms Zcash.Snark.ZeroKnowledge.rowDomain_product
assert_axioms Zcash.Snark.ZeroKnowledge.domainPolynomial_dvd_of_rows
assert_axioms Zcash.Snark.ZeroKnowledge.rows_zero_of_domainPolynomial_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.domainPolynomial_dvd_iff_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_dvd_of_rows
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_rows_simulation_error_bound

-- Private exceptional states contribute their probability to the joint comparison.
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_rows
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_exceptional_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_exceptional_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInvalidRowMass_le_row_violation
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_consistency_error_bound

-- The complete public tape is retained; exceptional challenges are charged, not excluded.
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengesFromTape
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifier_simulation_error_bound

-- Concrete exceptional-challenge count for the full interactive tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkRotationExponent
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotationExponent_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_snoc
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_away
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesGood_of_simple
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallenges_bad_cover
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallengeBadEvent_le
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshPlonkVerifier_simulation_error_bound

-- Computed product rows, with zero-preserving division and explicit exceptional factors.
assert_computable Zcash.Snark.ZeroKnowledge.runningProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_zero
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_succ
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_eq_ratio
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_violation_iff
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_zero_after_den_zero
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_end
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_end_one
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_terminal_constraint
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductInitial
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_start
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_chain
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductInitial_eq_running
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_terminal_constraint
assert_axioms Zcash.Snark.ZeroKnowledge.prefixPerm_prod_shift_eq
assert_computable Zcash.Snark.ZeroKnowledge.lookupProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_product_identity
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_terminal_constraint
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.uniformProductDenominator_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominator_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominator_mixture_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePinnedProductDenominator_bad_le

-- The computed lookup scan satisfies the actual row and polynomial constraints.
assert_computable Zcash.Snark.ZeroKnowledge.rowSelectorValues
assert_computable Zcash.Snark.ZeroKnowledge.lookupRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.rowSelectorValues_active
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLagrangePolynomials_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_polynomial_eval
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_eval_row_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_dvd_domain_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_lookupEvals
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_lookups

-- The three permutation scans, their actual constraints, and terminal rotations.
assert_axioms Zcash.Snark.ZeroKnowledge.copyPermutation_product_identity
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowNumerator +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowDenominator +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationScanRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.permChunkExpression_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_zero_of_scan
assert_computable Zcash.Snark.ZeroKnowledge.permutationTerminalPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationPairRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_eval_row_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_dvd_domain_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTerminalFactor
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_permutationSetEvals

-- The specified lookup sorter succeeds on valid prefixes and supplies the row premises.
assert_computable Zcash.Snark.ZeroKnowledge.lookupRunPlan
assert_computable Zcash.Snark.ZeroKnowledge.reserveLookupValues
assert_computable Zcash.Snark.ZeroKnowledge.fillLookupPlan
assert_computable Zcash.Snark.ZeroKnowledge.canonicalLookupSort
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortColumns
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_length
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_perm
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_ordered
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_eq_of_ordered
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_getElem
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_matches
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValues_perm
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlan_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_first
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_run
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_getD_eq
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValues_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupPlan_reserved_le_length
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlan_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_reservations
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_zero_of_sort
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_reverse_fill_example
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_duplicate_table_example
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_missing_value_example

-- Partial column construction, exact earlier histories, and the concrete schedule.
assert_computable Zcash.Snark.ZeroKnowledge.ColumnAttemptStep.totalize +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnAttemptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_eq_take
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_eq_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.ColumnAttemptStep.retained
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_retained
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupBaseRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_eq_model
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials_eq_model
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows_exists
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_advice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_eq_none
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_lookup_challenges
assert_computable Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnAttempt +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_totalize
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_row_samples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_eq_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_sampling_error_bound

-- The actual schedule's prefix reads, retained rows, and product constraints.
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnIndex_bounds
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupBaseRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_eval_row_of_present
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_at_index
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_retained_of_present
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_retained
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_advice_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookup_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookup_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_permutation_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookupConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_permutation_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_permutationConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_domain_division

-- Concrete pre-product causality and zero-denominator probabilities.
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_take_congr
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnRows_cast
assert_computable Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_length
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkTotalColumnRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_eq_totalRows_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_take_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_take_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_polynomial_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_permutation_factors
assert_axioms Zcash.Snark.ZeroKnowledge.productDenominatorListBad
assert_axioms Zcash.Snark.ZeroKnowledge.productDenominatorListBad_iff
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominatorList_bad_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkProductGammaForms +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductDenominatorsNonzero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_lookup_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_permutation_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductDenominatorsNonzero_of_not_listBad
assert_computable Zcash.Snark.ZeroKnowledge.withProductChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkProductDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePinnedPlonkProductDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkProductDenominators_mixture_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkColumnAttempt_productDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkProductShape
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkProductShape

-- The full challenge law and concrete row exceptions inside the joint simulation.
assert_computable Zcash.Snark.ZeroKnowledge.plonkOtherChallengesFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOtherChallengesFromTape_products
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkOtherChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_products
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkRowPrerequisites
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_domain_division
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_invalid_cover
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw_denominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkInvalidRowMass_referenceRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkInvalidRowMass_le_prerequisites
assert_axioms Zcash.Snark.ZeroKnowledge.wideConstructedPlonkVerifier_simulation_error_bound

-- Original copy equations survive masking and supply the computed product identity.
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromCoins_retained
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_retained
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows_polynomial
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_advice_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryOrder_current
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_current
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationRefUnrotated
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationQueriesUnrotated
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationRef_usable
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_masked
assert_axioms Zcash.Snark.ZeroKnowledge.copyValues_replay
assert_axioms Zcash.Snark.ZeroKnowledge.prod_chunk_cells
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkCopyCell
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellPair +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellName +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellSigma +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_sigma
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationNumerator_prod_cells
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationDenominator_prod_cells
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkCopyWitness
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyWitness_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_copyProduct
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisites_iff_of_copy
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionFailureMass
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass_eq_of_copy
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopyQueries
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopyQueries
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopyChunkWidths
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopyChunkWidths
assert_axioms Zcash.Snark.ZeroKnowledge.wideCopyValidPlonkVerifier_simulation_error_bound

-- Original gate and lookup validity, public mask safety, and completion of the actual row attempt.
assert_computable Zcash.Snark.ZeroKnowledge.exprPublicValue
assert_axioms Zcash.Snark.ZeroKnowledge.exprPublicValue_sound
assert_computable Zcash.Snark.ZeroKnowledge.exprMaskInvariant
assert_axioms Zcash.Snark.ZeroKnowledge.exprMaskInvariant_of_retained_all
assert_axioms Zcash.Snark.ZeroKnowledge.exprMaskInvariant_sound
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRotationOffsets
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRotationRow
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceQueryRetained
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryFactor_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_eval_row
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRowValues +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_adviceRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceRowValues_masked
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_complete_of_total
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_cast_eq
assert_computable Zcash.Snark.ZeroKnowledge.plonkFixedRowValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkInstanceRowValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkExpressionRowValue +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkExpressionMaskCheck +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_fixedRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_instanceRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkExpressionRowValue_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGatePolynomial_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_eq_values
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkOriginalRowsValid
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_gateConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_lookupTuples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_lookupMembership
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_ne_none_of_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_of_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionReady_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionFailureMass_eq_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisites_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass_eq_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wideOriginalValidPlonkVerifier_simulation_error_bound
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupMaskBoundaryRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows_lookup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryRetained_interior
assert_axioms Zcash.Snark.ZeroKnowledge.plonkExpressionMaskCheck_interior
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskingProfile_of_boundaries
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryCheck
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryCheck_sound
assert_computable Zcash.Snark.ZeroKnowledge.capturedPlonkMaskBoundaryFixed +choice
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkMaskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkMaskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkMaskingProfile

-- Structural keygen support and public row-polynomial provenance.
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelRawFixed_row_lt_usable
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelFixed_row_lt_usable
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelFixedRows_zero_of_usable_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_instances_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_fixed_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_sigma_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_degree
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_fixedRowValues
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygen_domainRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows_zero
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenMaskBoundaryFixed +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_maskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_maskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.wideKeygenPlonkVerifier_simulation_error_bound

-- Partial public information and selector placement reduce the concrete mask check to row zero.
assert_computable Zcash.Snark.ZeroKnowledge.exprPartialPublicValue
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialPublicValue_refines
assert_computable Zcash.Snark.ZeroKnowledge.exprPartialMaskInvariant
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialMaskInvariant_refines
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorRows_zero_of_no_activation
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelRawSelector_row_lt_placementEnd
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorRows_zero_of_placementEnd_le
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorRows_zero_after_placement
assert_computable Zcash.Snark.ZeroKnowledge.plonkPartialMaskBoundaryCheck
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPartialMaskBoundaryCheck_sound
assert_computable Zcash.Snark.ZeroKnowledge.plonkInitialMaskColumns
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInitialMaskColumns_bounds
assert_computable Zcash.Snark.ZeroKnowledge.plonkSelectorBoundaryKnown +choice
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkSelectorBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkSelectorBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFixedQueryOrder_selector
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows_after_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows_selector_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_selectorBoundary_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_selectorMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkKeygenSelectorProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkKeygenSelectorProfile
assert_axioms Zcash.Snark.ZeroKnowledge.wideSelectorKeygenPlonkVerifier_simulation_error_bound

-- At an unmasked row the disclosed evaluation is the original cell, for every mask law.
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRowPolynomial_eval_before
assert_axioms Zcash.Snark.ZeroKnowledge.advicePolynomial_eval_usable
assert_axioms Zcash.Snark.ZeroKnowledge.evaluationView_apply_at_point
assert_axioms Zcash.Snark.ZeroKnowledge.evaluationView_ne_of_disclosed_cell
assert_axioms Zcash.Snark.ZeroKnowledge.adviceEvaluationView_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.adviceEvaluationView_ne_under_wide_reduction

-- The same disclosure is retained by the complete typed reference proof and challenge tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.projectedKernelView_apply_at_point
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_x
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallenges_x
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_current
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_usable
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_advice_usable
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_ne_of_usable_cell
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceObservation
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_advice_mass
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_advice_separation
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_advice_separation
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_no_common_exact_simulator

-- A second valid reference witness follows from inactive selectors and a copy footprint.
assert_computable Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionsCheck +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionsCheck_sound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_inactive_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionRowValue_eq
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkInactiveExpressions
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkInactiveExpressions
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnusedAdviceRow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedAdviceRow_usable
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnusedWitness
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_at
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_other_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceRotationRow_ne_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_advice_before
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_expression_before
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenExpressionRowValue_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOriginalRowsValid_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyWitness_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygen_exists_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.keygenPlonkReference_no_perfect_simulator
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkKeygen_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkKeygen_distinct_valid_witness

-- The compiler's complete ordered copy stream is packed without dropping any endpoint.
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenConstantCopies_fit
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_rows_lt_usedRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_columns_lt
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyChunkWidths
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellRaw
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellOfFlat
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellOfFlat_raw
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_bounds
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenFlatCopies +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenCopies +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_encode
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_rows_lt_usedRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_avoid_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerCopies_exists_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.compilerCopiesPlonkReference_no_perfect_simulator

-- Compiler sigma entries agree with the exact packed replay, not only its cycle classes.
assert_axioms Zcash.Snark.ZeroKnowledge.replayKeygenPermutation_map_apply
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_pair
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_copies_encode
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerSigmaRow_eq_replay
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaRows_eq_replay
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaCoherent
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyWitness_of_values
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkSigmaNaming
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkSigmaNaming
assert_axioms Zcash.Snark.ZeroKnowledge.wideCompilerKeygenPlonkVerifier_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.compilerSigmaPlonkReference_no_perfect_simulator

-- Complete protocol attempts: existing schedule, partial encoding, and explicit failure outcomes.
assert_computable Zcash.Snark.ZeroKnowledge.protocolChallengeCount
assert_computable Zcash.Snark.ZeroKnowledge.protocolMessageCount
assert_computable Zcash.Snark.ZeroKnowledge.callerRetryAfterFailure
assert_axioms Zcash.Snark.ZeroKnowledge.callerRetryAfterFailure_complete
assert_axioms Zcash.Snark.ZeroKnowledge.callerRetryAfterFailure_coincident
assert_axioms Zcash.Snark.ZeroKnowledge.callerRetryAfterFailure_ne_complete
assert_computable Zcash.Snark.ZeroKnowledge.observeProtocolTrace
assert_computable Zcash.Snark.ZeroKnowledge.protocolTraceBytes
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptTrace
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengeSequence
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkAfterChallenge +choice
assert_computable Zcash.Snark.ZeroKnowledge.observePlonkAttempt +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptObservation +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_eq_zero_iff
assert_axioms Zcash.Snark.ZeroKnowledge.protocolMessageCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_append_of_failed
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_received_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_received_length
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscript_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeSequence_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_round
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_opening
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_nodup_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_opening_points
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_round
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_all
assert_axioms Zcash.Snark.ZeroKnowledge.observePlonkAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.wideObservedCompilerKeygenPlonk_simulation_error_bound

-- Full-attempt failure probabilities, including the specified wide-reduced private and verifier tapes.
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointPointFailure
assert_computable Zcash.Snark.ZeroKnowledge.PlonkFailureChallenges +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFailureChallengeIndex
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptSuccessSet +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPointFamily_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_preIpa_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_ipa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_no_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_identity_imp
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshSampledPlonkVerifier_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFailureChallenges_cover
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkFailureChallenges_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkFailureChallenges_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttempt_failure_subset
assert_axioms Zcash.Snark.ZeroKnowledge.freshSampledPlonkVerifier_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkAttempt_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkAttempt_failure_le

-- Complete typed-verifier acceptance and the conservative one-attempt completeness bound.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_wellFormed
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_assemble
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_deployedAccepts
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaSimulator_verifies_of_mem_support
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkVerifierSimulator_deployedAccepts
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierSimulator_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierSimulator_rejection_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierSimulator_rejection_prob_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierRejectionBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompletenessErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompletenessErrorBound_eq
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompletenessErrorBound_le_actions_mul_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompletenessErrorBound_one_lt_two_pow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompletenessErrorBound_lt_actions_mul_two_pow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAcceptedAttemptSet
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonk_completeness_error_bound

-- Successful full observations: explicit normalizers and the compiler-derived comparison.
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptSuccessDecidable +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptFailureBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSuccessfulErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonkView
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_eq
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_mono
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSuccessLowerBound_pos
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_common_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonk_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonk_selection_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.wideSuccessfulCompilerKeygenPlonk_simulation_capstone

-- Auxiliary caller composition retains every prefix and selects which terminal failures to repeat.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFinitePermSetEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteLookupEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteProofString
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteChallenges
assert_computable Zcash.Snark.ZeroKnowledge.plonkRetrySet +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkRetryDecidable +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservedRetrySet
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservedRetryDecidable
assert_computable Zcash.Snark.ZeroKnowledge.runPlonkRetries +choice
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_fromObserved
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_terminal
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRetry_subset_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_uniform_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_exhausted
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_both_exhausted_le
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_exhausted_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptFailureBound_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.wideRetriedCompilerKeygenPlonk_simulation_capstone

-- Normalized unlimited histories, their exact finite projections, and the limiting comparison.
assert_axioms Zcash.Snark.ZeroKnowledge.event_mass_compl_eq_sub
assert_axioms Zcash.Snark.ZeroKnowledge.retryTapeWeight
assert_axioms Zcash.Snark.ZeroKnowledge.retryTapeWeight_tsum
assert_computable Zcash.Snark.ZeroKnowledge.StoppedRetryTape
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryWeight
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryWeight_tsum
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryTapes
assert_computable Zcash.Snark.ZeroKnowledge.stoppedRetryTapeHistory
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries
assert_computable Zcash.Snark.ZeroKnowledge.stoppedRetryTapePrepend
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryTapeHistory_prepend
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryWeight_renewal
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_map_apply
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_renewal
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_idempotent
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_append_terminal
assert_computable Zcash.Snark.ZeroKnowledge.truncateRetryHistory
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryHistory_zero
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryHistory_succ_prepend
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryHistory_succ_stopped
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryHistory_of_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryHistory_eq_of_stopped
assert_axioms Zcash.Snark.ZeroKnowledge.retryTapeWeight_mem
assert_axioms Zcash.Snark.ZeroKnowledge.stoppedRetryTapes_replay
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_supported
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_truncate
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_truncate_exhausted_iff
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_length_tail
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_truncation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.natExpectation_eq_tsum_tail
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_expected_attempts
assert_axioms Zcash.Snark.ZeroKnowledge.unlimitedRetainedRetries_expected_attempts_le

-- Causality is pointwise on fixed tapes, without excluding failures or zero challenges.
assert_computable Zcash.Snark.ZeroKnowledge.protocolPrefix
assert_computable Zcash.Snark.ZeroKnowledge.ProtocolCausal
assert_computable Zcash.Snark.ZeroKnowledge.ProtocolChecksCausal
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_isPrefix
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_eq_of_count_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_append_of_count_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_append_of_lt_count
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_congr_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.protocolCausal_observation
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProtocolCausal_observation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_maskCommitment_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_messages_agree
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_maskCommitment_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_withChallenges_messages_agree

-- The exact schedule reduces the full causality theorem to dependencies of its message stages.
assert_computable Zcash.Snark.ZeroKnowledge.protocolStagesTrace
assert_computable Zcash.Snark.ZeroKnowledge.plonkEvaluationStage
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaStages
assert_computable Zcash.Snark.ZeroKnowledge.plonkStageMessages
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_eq_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_prefix_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_prefix_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkEvaluationStage_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStageMessages_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_eq_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_causal_of_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservedPrefix_causal_of_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_take_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_take_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_advice_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkHonestQuotientPieces_challenges

-- The actual full-tape decoder and all emitted commitments before the evaluation challenge.
assert_axioms Zcash.Snark.ZeroKnowledge.TapeAgrees
assert_axioms Zcash.Snark.ZeroKnowledge.TapeAgrees.eq
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeCounts_shape
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_symm_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedTapeCounts_shape
assert_axioms Zcash.Snark.ZeroKnowledge.batchedToColumnTape_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedPreIpaTapeEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaCoinEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedPreIpaCoins_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_shape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsEquiv_constructor_irrel
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_coins_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_rows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointTape_split_congr
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_coins_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_rows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_congr
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofColumnPoint
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_columnPoint
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_column
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_column_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_column_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_lookup_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_products_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_linear
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_piece
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_linear_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_quotient_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_prefix_before_x

-- Complete reference-prover causality, with the exact existing sampling law and observation.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_evaluations_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_early_columns
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_linearEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_points_q
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_groupValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_evaluations_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_qPrime_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_groupValues_causal
assert_computable Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointViewFromTape_ipa
assert_axioms Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial_mask_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_mask_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_round_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_stage_causal
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_observation_causal

-- Canonical encodings, complete reference proof size, and the exact observed tape law.
assert_axioms Zcash.Snark.ZeroKnowledge.scalarRepresentative_lt_two_pow_256
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarCodec +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarCodec_length
assert_computable Zcash.Snark.ZeroKnowledge.plonkPointCodec +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_none_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_of_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_length
assert_axioms Zcash.Snark.ZeroKnowledge.protocolMessageCount_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_messageCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_messageCount
assert_computable Zcash.Snark.ZeroKnowledge.encodedPlonkAttempt +choice
assert_axioms Zcash.Snark.ZeroKnowledge.encodedPlonkAttempt_complete_iff
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.freshEncodedPlonkReferenceAttempt
assert_axioms Zcash.Snark.ZeroKnowledge.freshEncodedPlonkReferenceAttempt_law
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_messageCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_proof_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_prefix_causal

-- The group argument is abstract here; the concrete Vesta cardinality has its own census.

-- The readable bound in the PR follows from the checked numerical budget.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_le_actions_mul_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_one_lt_two_pow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_lt_actions_mul_two_pow

-- The actual verifier's slot resolution and compression, with grouping order still explicit.
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateCommitmentId
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningCommitmentIds
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkPublicCommitmentsMatch
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_privateCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_quotientCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningCommitmentIds_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompressSet_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_commitmentMembers
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_commitment

-- Query-pattern transport and structural first-appearance ordering for arbitrary bundle sizes.
assert_axioms Zcash.Snark.ZeroKnowledge.groupingPattern_points
assert_axioms Zcash.Snark.ZeroKnowledge.groupingPattern_reference
assert_axioms Zcash.Snark.ZeroKnowledge.groupingPattern_ids
assert_axioms Zcash.Snark.ZeroKnowledge.groupingPattern_nodes
assert_axioms Zcash.Snark.ZeroKnowledge.groupingPattern_duplicates
assert_axioms Zcash.Snark.ZeroKnowledge.groupingDedup_reverse
assert_axioms Zcash.Snark.ZeroKnowledge.groupingDedup_append_disjoint
assert_axioms Zcash.Snark.ZeroKnowledge.groupingDedup_append_subset
assert_axioms Zcash.Snark.ZeroKnowledge.groupingDedup_flatMap
assert_axioms Zcash.Snark.ZeroKnowledge.groupingSlots_commitments
assert_computable Zcash.Snark.ZeroKnowledge.groupingSlotIndices
assert_axioms Zcash.Snark.ZeroKnowledge.groupingSlots_data
assert_axioms Zcash.Snark.ZeroKnowledge.groupingSlots_setList
assert_axioms Zcash.Snark.ZeroKnowledge.groupingSlots_routed
assert_axioms Zcash.Snark.ZeroKnowledge.groupingSlots_ids
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryRotation
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryPoint +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPoint_eq_observation
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPoint_injective
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkQueryLayout
assert_computable Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuerySpine
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryPattern
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_querySpine
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_queryPattern
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_groupingIds
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_groupingNodes
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_duplicateQueries
assert_computable Zcash.Snark.ZeroKnowledge.plonkShiftCommitmentId
assert_axioms Zcash.Snark.ZeroKnowledge.plonkShiftCommitmentId_injective
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentAction
assert_computable Zcash.Snark.ZeroKnowledge.plonkPerActionCommitmentOrder
assert_computable Zcash.Snark.ZeroKnowledge.plonkSharedCommitmentOrder
assert_computable Zcash.Snark.ZeroKnowledge.plonkSharedQuerySpine
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentOrder
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_eq_blocks
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_shift
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionCommitmentOrder_shift
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionCommitmentOrder_action
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_action
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSharedCommitmentOrder_action
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_disjoint
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSharedCommitmentOrder_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_points
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_head
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_points
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_points
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_pointIndex

-- The five groups, node order, and compressed commitments follow from the query layout.
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentGroup
assert_computable Zcash.Snark.ZeroKnowledge.plonkGroupPointIndices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointIndices_eq_opening
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentPointIndices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentGroup_shift
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_pointMembership
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSharedCommitmentOrder_group
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSharedQuerySpine_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointIndices_filter
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_slotIndices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentOrder_head
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentOrder_pointSets
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_setList
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointIndices_findIdx
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentOrder_filter
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_groupIds
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_groupNodes
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_ids
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_nodes
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_commitment_from_layout
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkQueryLayout
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkQueryLayout

-- The duplicate guard, every routed claim, and complete compressed evaluation vectors.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPerActionQuerySpine_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSharedQuerySpine_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuerySpine_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPattern_noDuplicates
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_noDuplicates
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_duplicateGuard
assert_computable Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels_indices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels_observations
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels_nodes
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGroupPointLabels_mem
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryClaim +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryClaim_private
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_queryClaims
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_queryClaim_exists
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryClaim_firstGroup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryClaims_nodeValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_memberClaim
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarFold_reverse
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_compressedClaim
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompressSet_evaluationLength
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_evaluations_from_layout

-- The complete compressed table feeds the existing final opening assembly.
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierCompressedGroups +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_lengths
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierCompressedGroups_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierCompressedGroups_getD
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierCompressedGroups_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierCompressedGroups_evaluations
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenCombine_evaluated
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenCombine_evaluated_congr
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierOpening +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierOpening_shape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierOpening_eq_public

-- Actual compiler key generation supplies the public commitment and domain conditions.
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeCommitInstance_eq_polynomialCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenFixedCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenInstanceCommitment
assert_computable Zcash.Snark.ZeroKnowledge.plonkCompilerPublicPolynomials +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerFixedColumnCoverage
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerPublicCommitmentsMatch
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerKey_domain
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerOpening_eq_public

assert_axioms Zcash.Snark.ZeroKnowledge.eraseExpr_toExpr_degree_le
assert_axioms Zcash.Snark.ZeroKnowledge.substSelectorMap_degree_singleton
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_gate_degree_le
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_lookupInput_substitution_degree
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_lookupInput_degree_le
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_lookupTable_degree_le
assert_axioms Zcash.Snark.ZeroKnowledge.extendCombination_degree_budget
assert_axioms Zcash.Snark.ZeroKnowledge.buildCombinations_degree_budget
assert_axioms Zcash.Snark.ZeroKnowledge.process_entry_degree_budget
assert_computable Zcash.Snark.ZeroKnowledge.selectorCompressionDegreeBudget
assert_axioms Zcash.Snark.ZeroKnowledge.deriveSelCompressMap_lookup_degree_budget
assert_axioms Zcash.Snark.ZeroKnowledge.selReplacement_degree_le
assert_computable Zcash.Snark.ZeroKnowledge.selectorWeightedDegree
assert_axioms Zcash.Snark.ZeroKnowledge.substSelectorMap_degree_le_weighted

-- Structural masking certificates survive both selector substitution and expression erasure.
assert_computable Zcash.Snark.ZeroKnowledge.sourceExpressionZero
assert_computable Zcash.Snark.ZeroKnowledge.sourceExpressionMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.sourceExpressionMaskSafe_of_zero
assert_axioms Zcash.Snark.ZeroKnowledge.selReplacement_sourceExpressionZero
assert_axioms Zcash.Snark.ZeroKnowledge.selReplacement_sourceExpressionMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.substSelectorMap_sourceMaskCertificates
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialMaskInvariant_of_publicValue
assert_axioms Zcash.Snark.ZeroKnowledge.eraseExpr_decidableEq_irrel
assert_axioms Zcash.Snark.ZeroKnowledge.derivePinnedCS_decidableEq_irrel
assert_axioms Zcash.Snark.ZeroKnowledge.eraseExpr_sourceMaskCertificates

-- Exact source selector traces and their connection to compiler placement.
assert_computable Zcash.Snark.ZeroKnowledge.placeSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.activations_eq_placeSelectorTrace

assert_computable Zcash.Snark.ZeroKnowledge.initialSelectorCheck
assert_axioms Zcash.Snark.ZeroKnowledge.initialSelectorCheck_not_mem_local
assert_axioms Zcash.Snark.ZeroKnowledge.mem_placeSelectorTrace_initial
assert_axioms Zcash.Snark.ZeroKnowledge.initialSelectorCheck_not_mem_placed
assert_computable Zcash.Snark.ZeroKnowledge.regionStartsFromSummary
assert_axioms Zcash.Snark.ZeroKnowledge.regionStartsFromSummary_def
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_regionStarts_eq_planSummary

assert_axioms Zcash.Snark.ZeroKnowledge.process_entry_root_coordinates
assert_axioms Zcash.Snark.ZeroKnowledge.deriveSelCompressMap_lookup_root_coordinates
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelActiveSelector_fixedValue
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorReplacement_zero_of_inactive

-- Evaluated public factors survive source substitution and expression compilation.
assert_computable Zcash.Snark.ZeroKnowledge.partialProductValue
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_some
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_zero_left
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_zero_right
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_scalar_right
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_neg_one
assert_computable Zcash.Snark.ZeroKnowledge.sourcePartialValue
assert_computable Zcash.Snark.ZeroKnowledge.sourcePartialMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.substSelectorMap_partialMaskCertificates
assert_axioms Zcash.Snark.ZeroKnowledge.selReplacement_sourcePartialMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.selReplacement_sourcePartialValue
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialPublicValue_product
assert_axioms Zcash.Snark.ZeroKnowledge.eraseExpr_partialMaskCertificates

-- Complete start lists from declaratively certified V1 placement blocks.
assert_computable Zcash.Snark.ZeroKnowledge.plannerRunStarts
assert_axioms Zcash.Snark.ZeroKnowledge.slotShapeSummariesFrom_replicate_starts
assert_computable Zcash.Snark.ZeroKnowledge.plannerTraceStarts
assert_axioms Zcash.Snark.ZeroKnowledge.slotShapeSummariesFrom_trace_starts
assert_axioms Zcash.Snark.ZeroKnowledge.slotShapeSummariesFrom_replicate_empty_starts
assert_axioms Zcash.Snark.ZeroKnowledge.slotIn_pairs_eq_zip

assert_computable Zcash.Snark.ZeroKnowledge.selectorPackingCount
assert_axioms Zcash.Snark.ZeroKnowledge.selectorPackingCount_def
assert_axioms Zcash.Snark.ZeroKnowledge.deriveSelCompressMap_newFixedCols_eq_count

-- Bit-vector certificates preserve the actual activation table and greedy count.
assert_computable Zcash.Snark.ZeroKnowledge.selectorBitsRows
assert_axioms Zcash.Snark.ZeroKnowledge.selectorBitsRows_size
assert_axioms Zcash.Snark.ZeroKnowledge.selectorBitsRows_zero
assert_axioms Zcash.Snark.ZeroKnowledge.selectorBitsRows_or_row
assert_computable Zcash.Snark.ZeroKnowledge.selectorActivationBits
assert_axioms Zcash.Snark.ZeroKnowledge.selectorActivationBits_size
assert_axioms Zcash.Snark.ZeroKnowledge.activationTable_eq_selectorBitsRows
assert_axioms Zcash.Snark.ZeroKnowledge.selectorBitsRows_conflicts
assert_computable Zcash.Snark.ZeroKnowledge.selectorBitPackingCount
assert_axioms Zcash.Snark.ZeroKnowledge.selectorBitPackingCount_def
assert_axioms Zcash.Snark.ZeroKnowledge.selectorPackingCount_eq_bits

-- Raw digest recovery and the lossless Fiat–Shamir byte boundary.
assert_computable Zcash.Snark.ZeroKnowledge.digestFiberSize
assert_axioms Zcash.Snark.ZeroKnowledge.digestFiberSize_pos
assert_axioms Zcash.Snark.ZeroKnowledge.digestFromQuotient_lt
assert_computable Zcash.Snark.ZeroKnowledge.digestFromQuotient +choice
assert_axioms Zcash.Snark.ZeroKnowledge.digestFromQuotient_reduce
assert_axioms Zcash.Snark.ZeroKnowledge.digestFromQuotient_injective
assert_axioms Zcash.Snark.ZeroKnowledge.digestFromQuotient_range
assert_axioms Zcash.Snark.ZeroKnowledge.digestFiberSample
assert_axioms Zcash.Snark.ZeroKnowledge.digestFiberSample_apply
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_mul_digestFiberSample
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_digest_recovery_law
assert_axioms Zcash.Snark.ZeroKnowledge.digestFiberSample_support
assert_axioms Zcash.Snark.ZeroKnowledge.digestTapeFiberSample
assert_axioms Zcash.Snark.ZeroKnowledge.digestTape_recovery_law
assert_axioms Zcash.Snark.ZeroKnowledge.liftDigestTapeView
assert_axioms Zcash.Snark.ZeroKnowledge.liftDigestTapeView_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.ofDigits_div_pow_mod
assert_axioms Zcash.Snark.ZeroKnowledge.leos2ip_i2leosp
assert_axioms Zcash.Snark.ZeroKnowledge.i2leosp_toList_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarCodec_injective
assert_axioms Zcash.Snark.ZeroKnowledge.vestaCoordinate_lt_two_pow_256
assert_computable Zcash.Snark.ZeroKnowledge.vestaCoordinateCodec
assert_axioms Zcash.Snark.ZeroKnowledge.vestaCoordinateCodec_length
assert_axioms Zcash.Snark.ZeroKnowledge.vestaCoordinateCodec_injective
assert_computable Zcash.Snark.ZeroKnowledge.vestaAffineCodec +choice
assert_axioms Zcash.Snark.ZeroKnowledge.vestaAffineCodec_length
assert_axioms Zcash.Snark.ZeroKnowledge.vestaAffineCodec_injective
assert_computable Zcash.Snark.ZeroKnowledge.transcriptElementBytes +choice
assert_computable Zcash.Snark.ZeroKnowledge.transcriptBytes +choice
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytes_append
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytes_eq_nil_iff
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptElementBytes_append_injective
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytes_injective
assert_computable Zcash.Snark.ZeroKnowledge.halo2TranscriptPersonalization
assert_axioms Zcash.Snark.ZeroKnowledge.halo2TranscriptPersonalization_length
assert_computable Zcash.Snark.ZeroKnowledge.TranscriptHashAddress
assert_computable Zcash.Snark.ZeroKnowledge.transcriptHashAddress +choice
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptHashAddress_injective
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptHashAddress_squeeze
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytes_squeeze_length
assert_computable Zcash.Snark.ZeroKnowledge.byteFiatShamir +choice
assert_axioms Zcash.Snark.ZeroKnowledge.byteFiatShamir_squeeze
assert_axioms Zcash.Snark.ZeroKnowledge.byteFiatShamir_statement_theta
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengeFields +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeFields_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesFromFields
assert_axioms Zcash.Snark.ZeroKnowledge.attachPlonkDigests
assert_axioms Zcash.Snark.ZeroKnowledge.rawDigestChallengeExperiment
assert_axioms Zcash.Snark.ZeroKnowledge.attachPlonkDigests_wideChallenges

-- Consistent lazy oracle execution and its conflict-only programming comparison.
assert_computable Zcash.Snark.ZeroKnowledge.OracleCache
assert_computable Zcash.Snark.ZeroKnowledge.oracleCacheLookup
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookup_nil
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookup_cons_same
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookup_cons_ne
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookup_eq_none
assert_computable Zcash.Snark.ZeroKnowledge.cacheOracleComp
assert_axioms Zcash.Snark.ZeroKnowledge.cacheOracleComp_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.cacheOracleComp_run
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleLaw
assert_computable Zcash.Snark.ZeroKnowledge.cachedOracleRunTape
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleRunTape_ne_none
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleRunTape_law
assert_computable Zcash.Snark.ZeroKnowledge.programOracleTrace
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTrace_append
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTrace_keeps
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTrace_answers
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTrace_ne_none_of_fresh
assert_computable Zcash.Snark.ZeroKnowledge.programOracleView
assert_axioms Zcash.Snark.ZeroKnowledge.freshOracleTraceLaw
assert_axioms Zcash.Snark.ZeroKnowledge.freshOracleTraceLaw_result
assert_computable Zcash.Snark.ZeroKnowledge.freshOracleRunTape
assert_axioms Zcash.Snark.ZeroKnowledge.freshOracleRunTape_ne_none
assert_axioms Zcash.Snark.ZeroKnowledge.freshOracleRunTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleRunTape_eq_programmed
assert_axioms Zcash.Snark.ZeroKnowledge.programmedOracleLaw
assert_axioms Zcash.Snark.ZeroKnowledge.programmedOracleRunTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.oracleProgramming_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.oracleProgramming_family_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshOracleRunTape_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTrace_length
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleRunTape_cache_length_le

-- Single-attempt classical oracle simulation, executable tapes, and resource bounds.
-- AnchorProbability
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptAnchor_mass_le
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptAnchorList_mass_le
-- OracleContinuation
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_bind_support
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleLaw_cache_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptContinue
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptContinue_error_bound
-- OracleContinuationResources
assert_computable Zcash.Snark.ZeroKnowledge.oracleAttemptCache
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleView_cache_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptContinue_cache_length_le
-- OracleSchedule
assert_computable Zcash.Snark.ZeroKnowledge.replayOracleSchedule
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleSchedule_queries_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleSchedule_queries_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleSchedule_result
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleSchedule_queries_nodup
assert_computable Zcash.Snark.ZeroKnowledge.oracleHistoryTape
assert_axioms Zcash.Snark.ZeroKnowledge.oracleHistoryTape_snoc_agrees
assert_computable Zcash.Snark.ZeroKnowledge.prefixOracleComp
assert_axioms Zcash.Snark.ZeroKnowledge.prefixOracleComp_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.prefixOracleComp_replay
-- OracleTableResources
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_queries_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleView_cache_length
-- PlonkAnchor
assert_axioms Zcash.Snark.ZeroKnowledge.attachPlonkDigests_forget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_firstAdvice
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaMaskSimulator_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJointSimulator_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkVerifierSimulator_advice
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierSimulator_advice
assert_axioms Zcash.Snark.ZeroKnowledge.digestPlonkVerifierSimulator_advice
-- PlonkOracle
assert_computable Zcash.Snark.ZeroKnowledge.plonkRawOracleView +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_query_mem_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_queries_nodup
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceOracleTrace +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceOracleTrace_causal
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceOracleComp +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceOracleComp_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceOracleComp_replay
-- PlonkQuerySchedule
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStageBlocks_split
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaBlocks_transcript
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPrefix_preIpa
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryPrefix_ipaRound
assert_axioms Zcash.Snark.ZeroKnowledge.deriveChallenges_protocolQuery_preIpa
assert_axioms Zcash.Snark.ZeroKnowledge.deriveChallenges_protocolQuery
assert_axioms Zcash.Snark.ZeroKnowledge.byteFiatShamir_protocolQuery
-- PlonkSimulatorTape
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskSimulatorSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskSimulatorTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkSimulatorSampleCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulatorSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulatorSampleCount_eleven
assert_computable Zcash.Snark.ZeroKnowledge.plonkSimulatorTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierSimulatorFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierSimulatorFromTape_law
-- ProtocolOracle
assert_computable Zcash.Snark.ZeroKnowledge.protocolAttemptContinues
assert_computable Zcash.Snark.ZeroKnowledge.protocolOracleReport +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleReport_stopped
assert_computable Zcash.Snark.ZeroKnowledge.protocolOracleView +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_result
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_queries_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_queries_anchor
assert_computable Zcash.Snark.ZeroKnowledge.protocolOracleComp +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleComp_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleComp_replay
-- RawChallenges
assert_computable Zcash.Snark.ZeroKnowledge.extendDigestTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.extendDigestTape_fin
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengesFromDigests +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesFromDigests_read
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesFromDigests_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesFromDigests_extend
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesFromDigests_extend_read
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterDigests_causal
-- SimulationAgreement
-- StageQuery
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_queryPrefix
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefix_stages
-- TranscriptQuery
assert_computable Zcash.Snark.ZeroKnowledge.protocolQueryPrefix
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefix_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefix_inj
assert_computable Zcash.Snark.ZeroKnowledge.protocolQueryAddress +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddress_inj
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddresses_nodup
assert_computable Zcash.Snark.ZeroKnowledge.HasTranscriptAnchor +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddress_anchor
assert_axioms Zcash.Snark.ZeroKnowledge.HasTranscriptAnchor.unique

-- Fixed uniform bit tapes and the complete oracle simulator reduction budget.
-- OracleBitBounds
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_expanded
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_queries
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_mono_queries
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_le_actions_mul_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_one_lt_two_pow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBitSimulationErrorBound_lt_actions_mul_two_pow
-- RawBits
assert_computable Zcash.Snark.ZeroKnowledge.rawBitsTapeEquiv +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rawBitsTapeEquiv_word
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRawBitsTape
assert_axioms Zcash.Snark.ZeroKnowledge.rawBitsTape_map
-- RawFieldTape
assert_computable Zcash.Snark.ZeroKnowledge.RawFieldTape
assert_computable Zcash.Snark.ZeroKnowledge.reduceFieldTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRawFieldTape_reduce
assert_axioms Zcash.Snark.ZeroKnowledge.rawFieldTape_sample_law
assert_axioms Zcash.Snark.ZeroKnowledge.splitRawFieldTape_sample_law
assert_axioms Zcash.Snark.ZeroKnowledge.rawFieldTape_error_bound

-- Finite retained retries with shared oracle state and exact tape laws.
-- OracleCachePreservation
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleRunTape_keeps
assert_axioms Zcash.Snark.ZeroKnowledge.cachedOracleLaw_keeps
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleView_attemptCache_keeps
-- OracleRetry
assert_computable Zcash.Snark.ZeroKnowledge.oracleRetryRequested
assert_computable Zcash.Snark.ZeroKnowledge.oracleRetrySet
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequested_none
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequested_some
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequested_complete
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequested_coincident
assert_computable Zcash.Snark.ZeroKnowledge.oracleAttemptState
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptState_none
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptState_some
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryTransition
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries
-- OracleRetryBounds
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_zero
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_succ
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_eq_stateful
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_eq_mul
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_mono_queries
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryError_binary_le
-- OracleRetryResources
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryTransition_growth
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_policy
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_resources
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_cache_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_keeps
assert_axioms Zcash.Snark.ZeroKnowledge.retryAttemptTape_support_length
-- OracleRetrySimulation
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_simulation_error_bound
-- OracleRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.runOracleRetries
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetries_fromTape
-- StatefulRetry
assert_computable Zcash.Snark.ZeroKnowledge.prependStatefulRetry
assert_computable Zcash.Snark.ZeroKnowledge.runStatefulRetries
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryNext
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_exhausted
-- StatefulRetryResources
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_invariant
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_policy
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_resources
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_state_size_le
-- StatefulRetrySimulation
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryError
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryNext_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_simulation_error_bound

-- Uniform-seed PRNG game and exact test-dependent reduction.
assert_axioms Zcash.Snark.ZeroKnowledge.boolean_false_le
assert_axioms Zcash.Snark.ZeroKnowledge.boolean_event_bias
assert_axioms Zcash.Snark.ZeroKnowledge.boolean_event_bias_iff
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedTapeSource
assert_axioms Zcash.Snark.ZeroKnowledge.auxiliaryPrngGame
assert_axioms Zcash.Snark.ZeroKnowledge.auxiliaryPrngGame_seed_law
assert_computable Zcash.Snark.ZeroKnowledge.UniformSeedPrngSecure +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedPrngSecure_event_bias
assert_axioms Zcash.Snark.ZeroKnowledge.auxiliaryPrngGame_reduction_law
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedPrng_simulation_error_bound

-- Continuous generator state, exact private-prefix replay, and the finite PRNG reduction.
-- GeneratorTape
assert_computable Zcash.Snark.ZeroKnowledge.drawGeneratorTape
assert_axioms Zcash.Snark.ZeroKnowledge.drawGeneratorTape_state
assert_axioms Zcash.Snark.ZeroKnowledge.drawGeneratorTape_at
assert_axioms Zcash.Snark.ZeroKnowledge.drawGeneratorTape_cast
assert_computable Zcash.Snark.ZeroKnowledge.drawGeneratorBlocks
assert_axioms Zcash.Snark.ZeroKnowledge.drawGeneratorBlocks_state
assert_axioms Zcash.Snark.ZeroKnowledge.drawGeneratorBlocks_at
-- GeneratedRetryCoins
assert_computable Zcash.Snark.ZeroKnowledge.runGeneratedCoinRetries
assert_axioms Zcash.Snark.ZeroKnowledge.runGeneratedCoinRetries_replay
assert_axioms Zcash.Snark.ZeroKnowledge.runGeneratedCoinRetries_state
assert_axioms Zcash.Snark.ZeroKnowledge.runGeneratedCoinRetries_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.runGeneratedCoinRetries_word_state
assert_axioms Zcash.Snark.ZeroKnowledge.zip_ofFn_pair
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_map
-- RetryTapeSource
assert_axioms Zcash.Snark.ZeroKnowledge.independentTapeLaw_toList
assert_axioms Zcash.Snark.ZeroKnowledge.retryAttemptTape_map
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRetryTape_source_law
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRetryTape_source_map_law

-- Complete shared-oracle streams, uniform retry potentials, and retained nontermination.

-- MeasureAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_map_of_agree

-- MeasureEventBias
assert_computable Zcash.Snark.ZeroKnowledge.MeasureEventBiasLE +choice
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_toMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_map
assert_axioms Zcash.Snark.ZeroKnowledge.measure_event_le_approximation
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_of_cylinders

-- MeasureStreamLimit
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_of_prefixes

-- OracleRetryPotential
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryPotential
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryPotential_eq
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryPotential_mono_queries
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryPotential_step
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryPotential_binary_lt

-- OracleRetryTail
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleView_retry_imp
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleView_retry_le

-- PlonkRawObservation
assert_axioms Zcash.Snark.ZeroKnowledge.rawDigestChallengeExperiment_observed

-- StatefulRetryGeometric
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_bind_average_support
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryNext_average_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_potential_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetries_exhaustion_le

-- StatefulRetryStream
assert_computable Zcash.Snark.ZeroKnowledge.retainRetryState
assert_computable Zcash.Snark.ZeroKnowledge.retainedStateRetrySet
assert_computable Zcash.Snark.ZeroKnowledge.forgetRetryStates
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_forget_states
assert_computable Zcash.Snark.ZeroKnowledge.statefulRetryStream
assert_computable Zcash.Snark.ZeroKnowledge.statefulRetryPrefix
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_zero
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_succ
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_at
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_stopped_stream
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStream_none_of_stopped

-- StatefulRetryStreamLaw
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryRecorded
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryRecorded_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryRecorded_potential_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_map_law
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStream_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_isProbabilityMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_prefix

-- StatefulRetryStreamLimit
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_simulation_error_bound

-- StatefulRetryStreamTail
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryRecorded_exhaustion_le
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryPrefix_event_law
assert_computable Zcash.Snark.ZeroKnowledge.retryStreamNontermination
assert_axioms Zcash.Snark.ZeroKnowledge.retryStreamNontermination_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStream_nontermination_exhausts
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_nontermination_le
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_nontermination_le_of_tail
assert_computable Zcash.Snark.ZeroKnowledge.truncateRetryStream
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryStream_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryStream_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryStream_of_stopped
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_truncate
assert_axioms Zcash.Snark.ZeroKnowledge.statefulRetryStreamLaw_truncation_error_bound

-- UniformInfiniteTape
assert_axioms Zcash.Snark.ZeroKnowledge.uniformInfiniteTape
assert_axioms Zcash.Snark.ZeroKnowledge.uniformInfiniteTape_isProbabilityMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.uniformInfiniteTape_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.uniformInfiniteTape_prefix_map
assert_axioms Zcash.Snark.ZeroKnowledge.uniformInfiniteTape_prefix_list

-- Complete seeded retry histories, exact finite replay, and explicit computational truncation.

-- GeneratedRetryStream
assert_computable Zcash.Snark.ZeroKnowledge.generatedPublicRun
assert_computable Zcash.Snark.ZeroKnowledge.generatedRecordedStep
assert_computable Zcash.Snark.ZeroKnowledge.generatedRetryRecord
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRecordedStep_run
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_eq_run
assert_computable Zcash.Snark.ZeroKnowledge.generatedRetryStream
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStream_at
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStream_of_stopped

-- GeneratedRetryStreamLaw
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecordLaw
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStream_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStreamLaw
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStreamLaw_isProbabilityMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStream_truncate
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_map_law
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStreamLaw_truncate

-- GeneratedRetryStreamTail
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_event_law
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryStreamLaw_truncation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.seededGeneratedRetryStreamLaw
assert_axioms Zcash.Snark.ZeroKnowledge.seededGeneratedRetryStreamLaw_isProbabilityMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.seededGeneratedRetryStreamLaw_truncate
assert_axioms Zcash.Snark.ZeroKnowledge.seededGeneratedRetryStreamLaw_truncation_error_bound

-- MeasureBiasComposition
assert_axioms Zcash.Snark.ZeroKnowledge.MeasureEventBiasLE.mono
assert_axioms Zcash.Snark.ZeroKnowledge.MeasureEventBiasLE.trans
assert_axioms Zcash.Snark.ZeroKnowledge.pmfObservedMeasure_map

-- MeasureMixture
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture_apply
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture_isProbabilityMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture_const
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture_map
assert_axioms Zcash.Snark.ZeroKnowledge.pmfMeasureMixture_toMeasure
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_mixture
assert_axioms Zcash.Snark.ZeroKnowledge.measureEventBias_mixture_average

-- RetryRecordedSource
assert_computable Zcash.Snark.ZeroKnowledge.recordedCoinRetries
assert_axioms Zcash.Snark.ZeroKnowledge.recordedCoinRetriesFromSource
assert_axioms Zcash.Snark.ZeroKnowledge.recordedCoinRetriesFromSource_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecord_replay
assert_axioms Zcash.Snark.ZeroKnowledge.generatedRetryRecordLaw_source

-- RetryStreamNontermination
assert_axioms Zcash.Snark.ZeroKnowledge.truncateRetryStream_nontermination_measure_zero

-- Application witness normalization, actual hint decoding, and placed advice execution.

-- WindowDigits
assert_axioms Zcash.Snark.ZeroKnowledge.octalDigit_eq_shift_mask
assert_axioms Zcash.Snark.ZeroKnowledge.octalDigits_sum_mod

-- AdviceWitnessExecution
assert_axioms Zcash.Snark.ZeroKnowledge.PlacedAdviceProgram
assert_computable Zcash.Snark.ZeroKnowledge.regionAdvicePrograms
assert_computable Zcash.Snark.ZeroKnowledge.circuitAdvicePrograms
assert_computable Zcash.Snark.ZeroKnowledge.writeAdviceValue
assert_computable Zcash.Snark.ZeroKnowledge.runAdvicePrograms +choice
assert_axioms Zcash.Snark.ZeroKnowledge.writeAdviceValue_get_target
assert_axioms Zcash.Snark.ZeroKnowledge.writeAdviceValue_get_frame
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_get_frame
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_get_nonadvice
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_hint
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_usableRows

-- AdviceWitnessAssignment
assert_axioms Zcash.Snark.ZeroKnowledge.proverEnvironment_ext
assert_computable Zcash.Snark.ZeroKnowledge.initialPublicWitnessAssignment +choice
assert_axioms Zcash.Snark.ZeroKnowledge.initialPublicWitnessAssignment_inst
assert_axioms Zcash.Snark.ZeroKnowledge.initialPublicWitnessAssignment_publicInput
assert_computable Zcash.Snark.ZeroKnowledge.topLevelAdviceEnvironment +choice
assert_computable Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment +choice
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_environment
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_publicInput
assert_axioms Zcash.Snark.ZeroKnowledge.generatedAdviceAssignment_publicInput

-- Source witness equations, compiled fixed data, and checked structured-IR read support.

-- AdviceWitnessCausality
assert_computable Zcash.Snark.ZeroKnowledge.adviceProgramTarget
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceReadAgreement
assert_computable Zcash.Snark.ZeroKnowledge.AdviceProgramReadsFrom +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceProgramsCausal +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceWitnessEquations +choice
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_readAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_satisfies

-- AdviceWitnessEquations
assert_computable Zcash.Snark.ZeroKnowledge.eraseRegionAdvice
assert_computable Zcash.Snark.ZeroKnowledge.eraseCircuitAdvice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceWitnessEquations_append
assert_axioms Zcash.Snark.ZeroKnowledge.regionWitnessEquations_iff
assert_axioms Zcash.Snark.ZeroKnowledge.circuitWitnessEquations_iff
assert_axioms Zcash.Snark.ZeroKnowledge.eraseRegionAdvice_extends_congr
assert_axioms Zcash.Snark.ZeroKnowledge.eraseCircuitAdvice_extends_congr
assert_axioms Zcash.Snark.ZeroKnowledge.runAdvicePrograms_fixedWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.runCircuitAdvice_extendsWitnesses

-- CompiledFixedWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.erasedRegionWitnesses_iff_fixed
assert_axioms Zcash.Snark.ZeroKnowledge.erasedCircuitWitnesses_iff_fixed
assert_axioms Zcash.Snark.ZeroKnowledge.compiledFixedValue_of_mem_raw
assert_axioms Zcash.Snark.ZeroKnowledge.compiledEnvironment_fixedConstraints
assert_axioms Zcash.Snark.ZeroKnowledge.compiledEnvironment_fixedWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses

-- WitnessReadSupport
assert_computable Zcash.Snark.ZeroKnowledge.fieldWitnessReads
assert_computable Zcash.Snark.ZeroKnowledge.listWitnessReads
assert_computable Zcash.Snark.ZeroKnowledge.natWitnessReads
assert_computable Zcash.Snark.ZeroKnowledge.boolWitnessReads
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.mono
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.left
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.right
assert_axioms Zcash.Snark.ZeroKnowledge.fieldWitnessReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.listWitnessReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.natWitnessReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.boolWitnessReads_eval

-- WitnessProgramSupport
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.withLocals
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.withIndex
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessContextAgreement.list_member
assert_computable Zcash.Snark.ZeroKnowledge.vectorWitnessReads
assert_computable Zcash.Snark.ZeroKnowledge.stepsWitnessReads
assert_axioms Zcash.Snark.ZeroKnowledge.vectorWitnessReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.stepsWitnessReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.structuredWitnessReads_eval
assert_computable Zcash.Snark.ZeroKnowledge.placedWitnessCell
assert_axioms Zcash.Snark.ZeroKnowledge.adviceReadAgreement_context
assert_axioms Zcash.Snark.ZeroKnowledge.structuredWitness_readsFrom

-- Repeated advice writes, original copy semantics, and checked source support.

-- AdviceAliasCollection
assert_computable Zcash.Snark.ZeroKnowledge.NativeAdviceCopySource
assert_computable Zcash.Snark.ZeroKnowledge.regionAdviceAliases
assert_computable Zcash.Snark.ZeroKnowledge.circuitAdviceAliases
assert_axioms Zcash.Snark.ZeroKnowledge.regionAdviceAliases_erase
assert_axioms Zcash.Snark.ZeroKnowledge.circuitAdviceAliases_erase
assert_computable Zcash.Snark.ZeroKnowledge.RegionNativeCopiesSound +choice
assert_computable Zcash.Snark.ZeroKnowledge.CircuitNativeCopiesSound +choice
assert_axioms Zcash.Snark.ZeroKnowledge.regionAdviceAliases_sources
assert_axioms Zcash.Snark.ZeroKnowledge.circuitAdviceAliases_sources

-- AdviceAliasInvariant
assert_computable Zcash.Snark.ZeroKnowledge.AdviceAddress
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasesWellFormed
assert_computable Zcash.Snark.ZeroKnowledge.AdviceAliasValues
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasesWellFormed_empty
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasValues_id
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasRoot_ne_fresh
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasesWellFormed_cons
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasesWellFormed_copy
assert_axioms Zcash.Snark.ZeroKnowledge.runAdviceInstruction_value_frame
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasValues_fresh
assert_computable Zcash.Snark.ZeroKnowledge.AdviceCopySemantics +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasValues_copy_fresh
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasCopy_eq_self

-- AdviceAliasPlan
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasPlan
assert_computable Zcash.Snark.ZeroKnowledge.AdviceAliasSources +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasPlan_certificate
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_aliasPlan

-- AdviceReadPlan
assert_computable Zcash.Snark.ZeroKnowledge.adviceCellReadAvailable
assert_computable Zcash.Snark.ZeroKnowledge.adviceReadPlan
assert_computable Zcash.Snark.ZeroKnowledge.NativeAdviceReads +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceReadPlan_causal

-- AdviceWitnessTrace
assert_computable Zcash.Snark.ZeroKnowledge.runAdviceInstruction +choice
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceTraceCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.adviceTrace_preserves
assert_axioms Zcash.Snark.ZeroKnowledge.adviceTrace_readAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.adviceTrace_satisfies
assert_axioms Zcash.Snark.ZeroKnowledge.runAdviceInstruction_frame_of_fresh
assert_axioms Zcash.Snark.ZeroKnowledge.runAdviceInstruction_eq_of_same_value
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_trace

-- NativeArithmeticCopySupport
assert_axioms Zcash.Snark.ZeroKnowledge.add_nativeCopiesSound
assert_axioms Zcash.Snark.ZeroKnowledge.mulComplete_round_nativeCopiesSound
assert_axioms Zcash.Snark.ZeroKnowledge.mulComplete_assign_nativeCopiesSound

-- NativeCopyComposition
assert_computable Zcash.Snark.ZeroKnowledge.NativeCopyOperationSound +choice
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_iff_operations
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_append
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_cons
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_nil
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_of_none

-- NativeCopyLift
assert_axioms Zcash.Snark.ZeroKnowledge.circuitNativeCopiesSound_toFormal

-- NativeCopyLoops
assert_axioms Zcash.Snark.ZeroKnowledge.regionNativeCopiesSound_foldRange
assert_axioms Zcash.Snark.ZeroKnowledge.nativeCopyOperationSound_toIRScalar

-- NativeCopyRegions
assert_axioms Zcash.Snark.ZeroKnowledge.circuitNativeCopiesSound_append
assert_axioms Zcash.Snark.ZeroKnowledge.circuitNativeCopiesSound_outside

-- WitnessBuilderSupport
assert_computable Zcash.Snark.ZeroKnowledge.valueBuilderReads
assert_computable Zcash.Snark.ZeroKnowledge.natBuilderReads
assert_computable Zcash.Snark.ZeroKnowledge.boolBuilderReads
assert_axioms Zcash.Snark.ZeroKnowledge.valueBuilderReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.natBuilderReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.boolBuilderReads_eval
assert_axioms Zcash.Snark.ZeroKnowledge.scalarBuilder_readsFrom

-- WitnessCopySemantics
assert_computable Zcash.Snark.ZeroKnowledge.witnessCopyCell
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCopyCell_eval
assert_computable Zcash.Snark.ZeroKnowledge.witnessCopyAddress
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCopyAddress_semantics

-- Structural byte-cache costs and actual protocol size bounds.

-- ByteEqualityCost
assert_computable Zcash.Snark.ZeroKnowledge.byteListEqCosted
assert_axioms Zcash.Snark.ZeroKnowledge.byteListEqCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.byteListEqCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.transcriptAddressEqCosted
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptAddressEqCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptAddressEqCosted_cost_le

-- OracleCacheCost
assert_computable Zcash.Snark.ZeroKnowledge.oracleCacheLookupCosted
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookupCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.oracleCacheLookupCosted_cost_le

-- OracleProgrammingCost
assert_computable Zcash.Snark.ZeroKnowledge.programOracleTraceCosted
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTraceCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTraceCosted_cost_le_capacity
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTraceCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleTraceCosted_cost_le_budget
assert_computable Zcash.Snark.ZeroKnowledge.programOracleViewCosted
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleViewCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.programOracleViewCosted_cost_le

-- TranscriptByteSize
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptElementBytes_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytes_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefix_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddress_bytes_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_query_bytes_le

-- PlonkTranscriptSize
assert_axioms Zcash.Snark.ZeroKnowledge.length_flatten_ofFn_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscript_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQueryAddress_bytes_le

-- ProtocolCacheCost
assert_axioms Zcash.Snark.ZeroKnowledge.protocolOracleView_programming_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_programming_cost_le

-- Semantic support of original witness functions and checked advice annotations.

-- WitnessFunctionSupport
assert_computable Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport.mono
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport.map
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport.pair
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_const
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_readCell
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_valueBuilder
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_natBuilder
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_boolBuilder
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionSupport_readsFrom

-- PoseidonWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.poseidon_constWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.poseidon_addWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.poseidon_readCellWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.poseidon_rowWit_support

-- MulIncompleteWitnessSupport
assert_computable Zcash.Snark.ZeroKnowledge.mulIncompleteStateReads
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_readsValue_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_readWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_stepWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_stepWit_baseX_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_stepWit_baseY_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulIncomplete_initLambdaWit_support

-- MulCompleteWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.mulComplete_zWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulComplete_yPWit_support

-- FixedBaseWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_windowVal_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_xPWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_yPWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_uWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_hintWindowVal_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_xPWitH_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_yPWitH_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_uWitH_support

-- FixedCanonicityWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_alphaZeroPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_alpha1Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_alpha2Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.mulFixed_yVarWit_support

-- NoteWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.note_brWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_bWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_dWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_eWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_gWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_hWit_support

-- NoteCanonicityWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.note_aPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_b3CPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_e1FPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_g1G2PrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_k0Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_k2Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_k3Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_jPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.note_jWit_support

-- CommitIvkWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_bWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_dWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_aPrimeWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_b2CPrimeWit_support

-- SinsemillaWitnessSupport
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaStateReads
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_readsValue_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_initXPWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_stepWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_exitXAWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_initLWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_boundaryYA_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_finalYAWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_zeroWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_constWit_support

-- MerkleWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.merkle_waWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.merkle_wb1Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.merkle_wb2Wit_support
assert_axioms Zcash.Snark.ZeroKnowledge.merkle_wbWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.merkle_wcWit_support

-- NativeScalarWitnessSupport
assert_axioms Zcash.Snark.ZeroKnowledge.nativeScalar_support
assert_axioms Zcash.Snark.ZeroKnowledge.nativeConstant_support
assert_axioms Zcash.Snark.ZeroKnowledge.nativeBoolean_support
assert_axioms Zcash.Snark.ZeroKnowledge.addChip_sumWit_support

-- AdviceSupportPlan
assert_axioms Zcash.Snark.ZeroKnowledge.SupportedAdviceProgram
assert_computable Zcash.Snark.ZeroKnowledge.supportedAdviceProgram +choice
assert_computable Zcash.Snark.ZeroKnowledge.supportedStructuredAdvice +choice
assert_computable Zcash.Snark.ZeroKnowledge.adviceSupportPlan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceSupportPlan_causal
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_supportPlan

-- ActionHintReadSupport
assert_computable Zcash.Snark.ZeroKnowledge.actionFieldHintPrograms +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionPointHintPrograms +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionScalarHintPrograms +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionFieldHintPrograms_reads_nil
assert_axioms Zcash.Snark.ZeroKnowledge.actionPointHintPrograms_reads_nil
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarHintPrograms_reads_nil
assert_axioms Zcash.Snark.ZeroKnowledge.actionScalarWindow_reads_nil
assert_axioms Zcash.Snark.ZeroKnowledge.actionMerkleSiblingHint_support
assert_axioms Zcash.Snark.ZeroKnowledge.actionMerkleSwapHint_support

-- Exact finite-map refinements of the advice alias and certified read checks.

-- AdviceAliasAddressPlan
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasAddressData
assert_computable Zcash.Snark.ZeroKnowledge.adviceAddressAliasPlan
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasPlan_eq_addressPlan
assert_computable Zcash.Snark.ZeroKnowledge.regionAdviceAliasAddresses
assert_computable Zcash.Snark.ZeroKnowledge.circuitAdviceAliasAddresses
assert_axioms Zcash.Snark.ZeroKnowledge.regionAdviceAliasAddresses_eq
assert_axioms Zcash.Snark.ZeroKnowledge.circuitAdviceAliasAddresses_eq

-- AdviceAliasMap
assert_computable Zcash.Snark.ZeroKnowledge.adviceAddressKey
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAddressKey_injective
assert_computable Zcash.Snark.ZeroKnowledge.AdviceAliasMap +choice
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasMapLookup +choice
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasMapInsert +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapLookup_empty
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapLookup_insert
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapRepresents_empty
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents.root
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents.known
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents.insert
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents.insert_self
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceAliasMapRepresents.cons_known

-- AdviceAliasMapPlan
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasMapPlan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapPlan_eq
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapPlan_original
assert_axioms Zcash.Snark.ZeroKnowledge.circuitAdviceAliasMapPlan_original

-- AdviceSupportMapPlan
assert_computable Zcash.Snark.ZeroKnowledge.adviceCellReadMapAvailable +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceCellReadMapAvailable_eq
assert_computable Zcash.Snark.ZeroKnowledge.adviceSupportMapPlan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceSupportMapPlan_eq
assert_axioms Zcash.Snark.ZeroKnowledge.adviceSupportMapPlan_causal
assert_computable Zcash.Snark.ZeroKnowledge.adviceMapScan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceMapScan_cons
assert_computable Zcash.Snark.ZeroKnowledge.adviceReadMapStep +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceSupportMapPlan_eq_scan
assert_computable Zcash.Snark.ZeroKnowledge.adviceAliasMapStep +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceAliasMapPlan_eq_scan
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_mapPlans

-- Source equations act on pure address data before the original read policy.
assert_computable Zcash.Snark.ZeroKnowledge.adviceReadAddressData +choice
assert_computable Zcash.Snark.ZeroKnowledge.adviceReadAddressMapStep +choice
assert_axioms Zcash.Snark.ZeroKnowledge.adviceReadMapStep_eq_addressStep

-- ActionWitnessObservation

-- Source-preserving read and copy certificates.
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate.nil +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate.cons +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate.append +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate.transport +choice
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_certificate
assert_axioms Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.nil +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.cons +choice
assert_computable Zcash.Snark.ZeroKnowledge.adviceSourceEntryData
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.consWithData +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.append +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.transport +choice
assert_computable Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate.readCertificate +choice
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelAdviceAssignment_extendsWitnesses_of_sourceCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemilla_zWit_support
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessLoadSourceCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessLoad_readPlan
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessLoad_aliasPlan
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessLoad_annotationCount

-- Exact extraction from original witness equations.
assert_axioms Zcash.Snark.ZeroKnowledge.loadPrivate_cell_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.witnessPoint_cells_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.witnessNonIdPoint_cells_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.actionInitialHintCells_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.condSwap_hintCells_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.merkleLayer_hintCells_of_extendsWitnesses
assert_axioms Zcash.Snark.ZeroKnowledge.merkleHintFold_region
assert_axioms Zcash.Snark.ZeroKnowledge.merkleFold_hintCells_of_extendsWitnesses

-- The converse gate-scaling and inactive-selector compiler laws.
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_selReplacement_zero_of_inactive
assert_axioms Zcash.Snark.ZeroKnowledge.SourceListCertificate
assert_computable Zcash.Snark.ZeroKnowledge.SourceListCertificate.nil
assert_computable Zcash.Snark.ZeroKnowledge.SourceListCertificate.cons
assert_computable Zcash.Snark.ZeroKnowledge.SourceListCertificate.transport

-- Native callbacks also retain the immutable public and fixed environment.
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionAgreement
assert_axioms Zcash.Snark.ZeroKnowledge.witnessFunctionAgreementCoe
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionAgreement.mono
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionAgreement.left
assert_axioms Zcash.Snark.ZeroKnowledge.WitnessFunctionAgreement.right
assert_axioms Zcash.Snark.ZeroKnowledge.instanceGet_support

-- Exact counted implementations of the simulator's input packing and wide reduction.
assert_computable Zcash.Snark.ZeroKnowledge.packBitsLECosted
assert_axioms Zcash.Snark.ZeroKnowledge.packBitsLECosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.packBitsLECosted_lt
assert_axioms Zcash.Snark.ZeroKnowledge.packBitsLECosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.packBitsLECosted_raw_word
assert_axioms Zcash.Snark.ZeroKnowledge.packBitsLECosted_raw_word_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted_raw_word
assert_axioms Zcash.Snark.ZeroKnowledge.wideReduceBitsLECosted_raw_word_cost_le

-- Complete coverage of gates sharing selector indices.
assert_computable Zcash.Snark.ZeroKnowledge.sourceGateLabel
assert_computable Zcash.Snark.ZeroKnowledge.sourceGateActivationLabels
assert_computable Zcash.Snark.ZeroKnowledge.gateActivationCoverageCheck
assert_axioms Zcash.Snark.ZeroKnowledge.gateActivationCoverageCheck_sound
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_gate_enabled_of_coverage

-- Source completeness and the generated advice footprint.
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_environment_fixed_nat
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_substitutedGate_zero_of_constraints
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_verifierGates_zero_of_constraints

-- Actual Action query feeds, including signed row-zero reads.

-- Inactive compiler rows do not constrain private query values.
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_substitutedGate_zero_of_inactive
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_verifierGates_zero_of_inactive

-- The original equations imply the compiler's full ordered copy stream.
assert_axioms Zcash.Snark.ZeroKnowledge.regionCopiesSplit_fst_eq_declared
assert_axioms Zcash.Snark.ZeroKnowledge.v1Copies_fst_eq_declared
assert_computable Zcash.Snark.ZeroKnowledge.sourceCopyValue
assert_axioms Zcash.Snark.ZeroKnowledge.sourceCopyValue_resolveCell
assert_axioms Zcash.Snark.ZeroKnowledge.sourceCopyValue_instance
assert_axioms Zcash.Snark.ZeroKnowledge.sourceCopyValue_eq_of_resolveDeclared
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_nonconstantCopyValues_of_constraints
assert_axioms Zcash.Snark.ZeroKnowledge.constSite_mem_declaredCopies
assert_axioms Zcash.Snark.ZeroKnowledge.operationConstSite_mem_declaredCopies
assert_axioms Zcash.Snark.ZeroKnowledge.sourceCopyValue_column
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_constantCopyColumn_registered
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_constantCopyValue
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_constantCopyValues_of_constraints
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_copyValues_of_constraints

-- Lookup compiler semantics and exact Action permutation and table reads.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_value
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_enabledLookup_selectorProjection
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_verifierLookup_eval
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_enabledLookup_tuple_of_constraints
assert_computable Zcash.Snark.ZeroKnowledge.sourceLookupActivationLabels
assert_computable Zcash.Snark.ZeroKnowledge.lookupActivationCoverageCheck
assert_axioms Zcash.Snark.ZeroKnowledge.lookupActivationCoverageCheck_sound
assert_axioms Zcash.Snark.ZeroKnowledge.topLevel_lookup_enabled_of_coverage
assert_axioms Zcash.Snark.ZeroKnowledge.partialProductValue_sound
assert_axioms Zcash.Snark.ZeroKnowledge.sourcePartialValue_sound

-- Complete gate and lookup row bridges through the actual reference-key shape.

-- All three source-constraint bridges compose into the actual reference relation.

-- Public IPA folds retain the complete reader and group-operation costs.
assert_computable Zcash.Snark.ZeroKnowledge.powTwoCosted
assert_axioms Zcash.Snark.ZeroKnowledge.powTwoCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.powTwoCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.loHalfCosted
assert_computable Zcash.Snark.ZeroKnowledge.hiHalfCosted
assert_axioms Zcash.Snark.ZeroKnowledge.loHalfCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.hiHalfCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.loHalfCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.hiHalfCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.publicFoldCosted
assert_axioms Zcash.Snark.ZeroKnowledge.publicFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.publicFoldCosted_cost_le

-- Direct declaration inventory: IpaScalarCost.
assert_computable Zcash.Snark.ZeroKnowledge.allFinCosted
assert_axioms Zcash.Snark.ZeroKnowledge.allFinCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.allFinCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.squarePowerCosted
assert_axioms Zcash.Snark.ZeroKnowledge.squarePowerCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.squarePowerCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.chooseIpaScalarCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.chooseIpaScalarCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.chooseIpaScalarCosted_cost_le

-- Direct declaration inventory: FiniteArithmeticCost.
assert_computable Zcash.Snark.ZeroKnowledge.ofFnCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ofFnCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ofFnCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.ofFnCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.mapListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.mapListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.mapListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.sumFinCosted
assert_axioms Zcash.Snark.ZeroKnowledge.sumFinCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.sumFinCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.fieldPowerCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldPowerCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fieldPowerCosted_cost

-- Direct declaration inventory: IpaArithmeticCost.
assert_axioms Zcash.Snark.ZeroKnowledge.IpaOperationCosts
assert_axioms Zcash.Snark.ZeroKnowledge.IpaPublicCosted
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublicCosted.erase
assert_computable Zcash.Snark.ZeroKnowledge.ipaMessageSumCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSumCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaMessageSumCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSumCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaPublicResponseCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaPublicResponseCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaPublicResponseCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaPublicResponseCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.completeIpaMaskCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.completeIpaMaskCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.completeIpaMaskCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.completeIpaMaskCosted_cost_le

-- Direct declaration inventory: IpaSimulatorCost.
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.eraseCosts
assert_axioms Zcash.Snark.ZeroKnowledge.MaterializedIpaTranscript
assert_computable Zcash.Snark.ZeroKnowledge.materializedIpaTranscript
assert_computable Zcash.Snark.ZeroKnowledge.materializeIpaCosted
assert_axioms Zcash.Snark.ZeroKnowledge.materializeIpaCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializeIpaCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorRoundCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSimulatorRoundCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorFromCoinsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSimulatorFromCoinsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializedIpaSimulatorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.IpaPublicCosted.ReadBound
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorScalarCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.materializedIpaSimulatorCosted_cost_le

-- Direct declaration inventory: ExpressionCost.
assert_computable Zcash.Snark.ZeroKnowledge.exprNodeCount
assert_computable Zcash.Snark.ZeroKnowledge.exprEvalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.exprEvalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.exprEvalCosted_cost_le

-- Direct declaration inventory: ListFoldCost.
assert_computable Zcash.Snark.ZeroKnowledge.foldlCosted
assert_axioms Zcash.Snark.ZeroKnowledge.foldlCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.foldlCosted_invariant
assert_axioms Zcash.Snark.ZeroKnowledge.foldlCosted_cost_le_sum

-- Direct declaration inventory: PolynomialArithmeticCost.
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCoeffCosted
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoeffCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoeffCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.polynomialArrayCosted
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialArrayCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialArrayCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.listHornerCosted
assert_axioms Zcash.Snark.ZeroKnowledge.listHornerCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.listHornerCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.polynomialEvalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialEvalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialEvalCosted_cost_le

-- Direct declaration inventory: CommitmentArithmeticCost.
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCommitmentCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitmentCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitmentCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.commitmentHornerFoldCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.commitmentHornerFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.commitmentHornerFoldCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarFoldCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarFoldCosted_cost_le

-- Direct declaration inventory: FieldArithmeticCost.
assert_axioms Zcash.Snark.ZeroKnowledge.FieldOperationCosts
assert_computable Zcash.Snark.ZeroKnowledge.fieldAddCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldAddCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.fieldNegateCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldNegateCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.fieldSubtractCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSubtractCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.fieldMultiplyCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldMultiplyCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.fieldInverseCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldInverseCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.fieldDivideCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldDivideCosted_result

-- Direct declaration inventory: ExpressionCompressionCost.
assert_computable Zcash.Snark.ZeroKnowledge.compressExprsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.compressExprsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.compressExprsCosted_cost_le

-- Direct declaration inventory: LookupExpressionsCost.
assert_computable Zcash.Snark.ZeroKnowledge.lookupCompressionCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.lookupExpressionsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressionsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupEvalReadBound
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressionsCosted_cost_le

-- Direct declaration inventory: PermutationChunkCost.
assert_computable Zcash.Snark.ZeroKnowledge.permChunkExpressionCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permChunkExpressionCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permChunkExpressionCosted_cost_le

-- Direct declaration inventory: FieldExponentCost.
assert_computable Zcash.Snark.ZeroKnowledge.fieldNatCastCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldNatCastCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fieldNatCastCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.fieldIntegerPowerCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.fieldIntegerPowerCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fieldIntegerPowerCosted_cost_le

-- Direct declaration inventory: LagrangeBasisCost.
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeBasisValueCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeBasisValueCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeBasisValueCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeBasisValueCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeBasisCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeBasisCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeBasisCosted_cost_le

-- Direct declaration inventory: ListRoutingCost.
assert_computable Zcash.Snark.ZeroKnowledge.getDListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lastListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lastListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lastListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.appendListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.appendListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.appendListCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.zipListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.zipListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.zipListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.mapIndexListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.mapIndexListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.mapIndexListCosted_cost_le

-- Direct declaration inventory: PermutationBoundaryCost.
assert_axioms Zcash.Snark.ZeroKnowledge.permSetReadBound
assert_computable Zcash.Snark.ZeroKnowledge.optionalFieldCosted
assert_axioms Zcash.Snark.ZeroKnowledge.optionalFieldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.optionalFieldCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationFirstCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationFirstCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationFirstCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationFirstCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationLastCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationLastCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationLastCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationLastCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationChainCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationChainCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationChainCosted_cost_le

-- Direct declaration inventory: PermutationExpressionsCost.
assert_computable Zcash.Snark.ZeroKnowledge.permutationExpressionsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressionsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.permutationChunkListCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressionsCosted_cost_le

-- Direct declaration inventory: QuotientEvaluationCost.
assert_computable Zcash.Snark.ZeroKnowledge.fieldHornerFoldCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fieldHornerFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fieldHornerFoldCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.expectedHEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.expectedHEvalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.expectedHEvalCosted_cost_le

-- Direct declaration inventory: ListCollectedCost.
assert_axioms Zcash.Snark.ZeroKnowledge.mapListCosted_cost_le_sum
assert_computable Zcash.Snark.ZeroKnowledge.flatMapListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.flatMapListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.flatMapListCosted_cost_le_sum
assert_computable Zcash.Snark.ZeroKnowledge.flattenFinCosted
assert_axioms Zcash.Snark.ZeroKnowledge.flattenFinCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.flattenFinCosted_cost_le

-- Direct declaration inventory: ConstraintAssemblyCost.
assert_axioms Zcash.Snark.ZeroKnowledge.listValue_le_map_sum
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressionsCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressionsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.subProofConstraintsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.subProofConstraintsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.subProofPermutationCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.subProofLookupCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressionsCosted_cost_le_aggregate
assert_computable Zcash.Snark.ZeroKnowledge.subProofConstraintCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.subProofConstraintsCosted_cost_le

-- Direct declaration inventory: ConstraintCollectionCost.
assert_axioms Zcash.Snark.ZeroKnowledge.subProofConstraintsCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.allConstraintsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.allConstraintsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.allConstraintsCosted_cost_le

-- Direct declaration inventory: QueryRoutingCost.
assert_computable Zcash.Snark.ZeroKnowledge.finFnCosted
assert_axioms Zcash.Snark.ZeroKnowledge.finFnCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.finFnCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.columnResolveCosted
assert_axioms Zcash.Snark.ZeroKnowledge.columnResolveCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.columnResolveCosted_cost_le

-- Direct declaration inventory: InterpolationWeightCost.
assert_computable Zcash.Snark.ZeroKnowledge.rangeListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.rangeListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rangeListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.interpolationWeightStepCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.interpolationWeightStepCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.interpolationWeightStepCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.interpolationWeightCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.interpolationWeightCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.interpolationWeightCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.interpolationWeightCosted_cost_le

-- Direct declaration inventory: LagrangeEvaluationCost.
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeSummandStepCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeSummandStepCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeSummandStepCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeEvalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.lagrangeEvalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeEvalCosted_cost_le

-- Direct declaration inventory: MultiopenEvaluationCost.
assert_computable Zcash.Snark.ZeroKnowledge.multiopenDenominatorStepCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenDenominatorStepCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenDenominatorStepCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.multiopenSetEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenSetEvalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.multiopenSetEvalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenSetEvalCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.multiopenEvalStepCosted +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenEvalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.multiopenEvalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenEvalCosted_cost_le

-- Direct declaration inventory: MultiopenCombinationCost.
assert_computable Zcash.Snark.ZeroKnowledge.multiopenPointStepCosted
assert_computable Zcash.Snark.ZeroKnowledge.multiopenPointFoldCosted
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenPointFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenPointFoldCosted_msm
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenPointFoldCosted_cost_le

-- Direct declaration inventory: ListIndexCost.
assert_computable Zcash.Snark.ZeroKnowledge.idxOfListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.idxOfListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.idxOfListCosted_cost_le

-- Direct declaration inventory: PrivateColumnOrderCost.
assert_axioms Zcash.Snark.ZeroKnowledge.flattenFinCosted_length_eq
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnOrderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrderCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrderCosted_cost_le

-- Direct declaration inventory: PrivateColumnRoutingCost.
assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_property
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnIndexCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnIndexCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnIndexCosted_lt
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnIndexCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnViewCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnViewCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnViewCosted_cost_le

-- Direct declaration inventory: CommitmentEntryCost.
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnEntryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnEntryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLinearEntryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLinearEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLinearEntryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPieceEntryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPieceEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPieceEntryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPrimeEntryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPrimeEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPrimeEntryCosted_cost_le

-- RowCoefficientCost
assert_computable Zcash.Snark.ZeroKnowledge.rowCoefficientSummandCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientSummandCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientSummandCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.rowCoefficientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.rowCoefficientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientCosted_rowPolynomial

-- RowPolynomialCost
assert_computable Zcash.Snark.ZeroKnowledge.rowCoefficientsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.rowPolynomialEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomialEvalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomialEvalCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.rowPolynomialCommitmentCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomialCommitmentCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomialCommitmentCosted_cost_le

-- OpeningGroupLayoutCost
assert_computable Zcash.Snark.ZeroKnowledge.firstOpeningGroupCosted
assert_axioms Zcash.Snark.ZeroKnowledge.firstOpeningGroupCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.firstOpeningGroupCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.firstOpeningGroupCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.privateGroupActionCosted
assert_computable Zcash.Snark.ZeroKnowledge.privateOpeningGroupCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningGroupCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningGroupCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningGroupCosted_cost_le

-- CollapsedQuotientPointCost
assert_computable Zcash.Snark.ZeroKnowledge.collapsedQuotientPointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.collapsedQuotientPointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.collapsedQuotientPointCosted_cost_le

-- PlonkMaskSimulatorCost
assert_computable Zcash.Snark.ZeroKnowledge.materializePlonkMaskView
assert_computable Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted_points_length
assert_axioms Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted_columns_length
assert_axioms Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted_observations_length
assert_axioms Zcash.Snark.ZeroKnowledge.materializedPlonkMaskSimulatorCosted_cost_le

-- PrivateOpeningEvaluationCost
assert_computable Zcash.Snark.ZeroKnowledge.privateOpeningEvaluationCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningEvaluationCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningEvaluationCosted_groupValue
assert_computable Zcash.Snark.ZeroKnowledge.privateOpeningEvaluationCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningEvaluationCosted_cost_le

-- QueryOrderCost
assert_computable Zcash.Snark.ZeroKnowledge.fixedQueryOrderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fixedQueryOrderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fixedQueryOrderCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.adviceQueryOrderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.adviceQueryOrderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.adviceQueryOrderCosted_cost_le

-- PublicOpeningClaimsCost
assert_computable Zcash.Snark.ZeroKnowledge.publicRowEvaluationCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.fixedRowEvaluationCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.fixedRowEvaluationCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fixedRowEvaluationCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.firstPublicOpeningClaimsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningClaimsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.publicOpeningClaimAccessBudget
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningClaimsCosted_cost_le

-- PrivateOpeningPointCost
assert_computable Zcash.Snark.ZeroKnowledge.privateOpeningPointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningPointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningPointCosted_cost_le

-- PublicOpeningPointsCost
assert_computable Zcash.Snark.ZeroKnowledge.publicRowCommitmentCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.fixedRowPointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.fixedRowPointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fixedRowPointCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.firstPublicOpeningPointsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningPointsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.publicOpeningPointAccessBudget
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningPointsCosted_cost_le

-- PublicOpeningCommitmentCost
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningPointsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.firstPublicOpeningCommitmentCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningCommitmentCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningCommitmentCosted_cost_le

-- OpeningCommitmentVectorCost
assert_computable Zcash.Snark.ZeroKnowledge.openingCommitmentVectorCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingCommitmentVectorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingCommitmentVectorCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingCommitmentVectorCosted_cost_le

-- PrivateOpeningNodesCost
assert_computable Zcash.Snark.ZeroKnowledge.openingPointIndicesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointIndicesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointIndicesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointIndicesCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.privateOpeningNodesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningNodesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningNodesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.privateOpeningNodesCosted_cost_le

-- PublicOpeningValueCost
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningClaimsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.firstPublicOpeningValueCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningValueCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.firstPublicOpeningValueCosted_cost_le

-- OpeningScalarVectorsCost
assert_computable Zcash.Snark.ZeroKnowledge.openingNodeValuesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingNodeValuesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingNodeValuesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingNodeValuesCosted_node_lengths
assert_axioms Zcash.Snark.ZeroKnowledge.openingNodeValuesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.openingGroupValuesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingGroupValuesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingGroupValuesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingGroupValuesCosted_cost_le

-- OpeningPointSetsCost
assert_computable Zcash.Snark.ZeroKnowledge.observationPointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.observationPointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.observationPointCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.openingPointSetCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.openingPointSetsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingPointSetsCosted_cost_le

-- OpeningEvaluationSetsCost
assert_computable Zcash.Snark.ZeroKnowledge.openingSetEntryCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingSetEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingSetEntryCosted_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.openingSetEntryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.openingEvaluationSetsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingEvaluationSetsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingEvaluationSetsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.openingEvaluationSetsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenEvalCostBudget_le_five

-- PublicOpeningCost
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicOpeningCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicOpeningCosted_result

-- PublicOpeningCostBound
assert_axioms Zcash.Snark.ZeroKnowledge.openingNodeList_getD_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.openingEvaluationSetsCosted_entry_bounds
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicOpeningCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicOpeningCosted_cost_le

-- PlonkClaimInputsCost
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationSetCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationSetsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupEvalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupEvalCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupEvalCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceClaimCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceClaimCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceClaimCosted_cost_le

-- PermutationQueryPreparationCost
assert_computable Zcash.Snark.ZeroKnowledge.permutationColumnPairCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationColumnPairCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationColumnPairCosted_readCost
assert_axioms Zcash.Snark.ZeroKnowledge.permutationColumnPairCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationQueryChunkCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunkCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunkCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_cost_le

-- PlonkLookupInputsCost
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupInputCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_cost_le

-- PlonkClaimQueriesCost
assert_computable Zcash.Snark.ZeroKnowledge.publicRowQueryCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.publicRowQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.publicRowQueryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkFixedQueryCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFixedQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFixedQueryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceQueryCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryCosted_cost_le

-- PlonkClaimInputBounds
assert_axioms Zcash.Snark.ZeroKnowledge.permSetReadBound_mono
assert_axioms Zcash.Snark.ZeroKnowledge.lookupEvalReadBound_mono
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationSetsCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_entry_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationQueryChunksCosted_columns_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_nodes
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupInputsCosted_width

-- PlonkPreparedConstraintBudget
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreparedConstraintCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreparedConstraintCostBudget_bound

-- PlonkClaimConstraintsCost
assert_computable Zcash.Snark.ZeroKnowledge.plonkClaimConstraintsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkClaimConstraintsCosted_result

-- PlonkClaimConstraintsCostBound
assert_computable Zcash.Snark.ZeroKnowledge.plonkClaimConstraintsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkClaimConstraintsCosted_cost_le

-- PlonkConstraintListLength
assert_axioms Zcash.Snark.ZeroKnowledge.flattenFinCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkClaimConstraintsCosted_length_le

-- PlonkVerifierHxCost
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierHxCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierHxCosted_result

-- PlonkVerifierHxCostBound
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierHxCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierHxCosted_cost_le

-- StoredRowsCost
assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_ofFn_result
assert_computable Zcash.Snark.ZeroKnowledge.storedMatrixEntryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.storedMatrixEntryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedMatrixEntryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedMatrixEntryCosted_ofFn
assert_computable Zcash.Snark.ZeroKnowledge.storedRowReadersCosted
assert_axioms Zcash.Snark.ZeroKnowledge.storedRowReadersCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRowReadersCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedRowReadersCosted_erase_materialize
assert_axioms Zcash.Snark.ZeroKnowledge.storedRowReadersCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedRowReadersCosted_readBound

-- StoredBitTapeCost
assert_computable Zcash.Snark.ZeroKnowledge.storedWordBitCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedWordBitCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedWordBitCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedRawWordCosted +choice
assert_computable Zcash.Snark.ZeroKnowledge.storedFieldWordCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawWordCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedFieldWordCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawWordCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedFieldWordCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedRawTapeCosted +choice
assert_computable Zcash.Snark.ZeroKnowledge.storedFieldTapeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawTapeCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedFieldTapeCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawTapeCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedFieldTapeCosted_cost_le

-- StoredPlonkSetupCost
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.encode
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.urs
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.generatorCosted
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.fixedCosted +choice
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.sigmaCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.generatorCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.urs_encode
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.fixedCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.sigmaCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.generatorCosted_encode_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.fixedCosted_encode_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkSetup.sigmaCosted_encode_cost_le

-- StoredPlonkKeyCost
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkKey.encode
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkKey.gatesCosted
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkKey.layoutCosted
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupInputCosted
assert_computable Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupTableCosted
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.gatesCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.layoutCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupInputCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupTableCosted_encode_result
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.gatesCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.layoutCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupInputCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupTableCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupInputCosted_encode_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkKey.lookupTableCosted_encode_cost_le

-- IpaPreparedInputCost
assert_computable Zcash.Snark.ZeroKnowledge.prepareIpaPublicCosted
assert_axioms Zcash.Snark.ZeroKnowledge.prepareIpaPublicCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.prepareIpaPublicCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.prepareIpaPublicCosted_readBound
assert_computable Zcash.Snark.ZeroKnowledge.preparedIpaSimulatorCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.preparedIpaSimulatorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.preparedIpaSimulatorCosted_cost_le

-- ChallengeReadCost
assert_computable Zcash.Snark.ZeroKnowledge.Challenges.eraseCosts
assert_computable Zcash.Snark.ZeroKnowledge.Challenges.ReadBound

-- PlonkJointSimulatorCost
assert_computable Zcash.Snark.ZeroKnowledge.materializePlonkJointView
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSimulatorCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointSimulatorCosted_result

-- PlonkJointSimulatorBudget
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointAccessBudget
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSimulatorCostBudget

-- PlonkJointStoredBounds
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskStoredViews_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskStoredViews_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskStoredViews_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskStoredPoints_cost_le

-- PlonkJointSimulatorCostBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointSimulatorCosted_cost_le

/-! ## Complete stored-bit tape production and exact coin routing -/

assert_axioms Zcash.Snark.ZeroKnowledge.PlonkSimulatorCoinsCosted
assert_computable Zcash.Snark.ZeroKnowledge.PlonkSimulatorCoinsCosted.erase
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkFieldReadCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkFieldReadCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkFieldReadCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkCoinsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkCoinsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.PlonkSimulatorCoinsCosted.ReadBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkCoinsCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkCoinsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkChallengesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkChallengesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkChallengesCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkChallengesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkPreparedSimulatorTapes
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_raw_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_raw_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_challenges_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_coins_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredTapeReadBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_readBound
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredTapeCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_cost_le

/-! ## Complete algebraic simulation from stored bits -/

assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_cost_of_lt
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkFieldReadCosted_cost_of_lt
assert_computable Zcash.Snark.ZeroKnowledge.Challenges.readPrices
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkChallengePriceModel +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_challenge_prices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointSimulatorCostBudget_congr_prices

/-! ## Complete proof and transcript codecs -/

assert_computable Zcash.Snark.ZeroKnowledge.i2leosp256ByteCosted
assert_axioms Zcash.Snark.ZeroKnowledge.i2leosp256ByteCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.i2leosp256ByteCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.i2leosp256Costed
assert_axioms Zcash.Snark.ZeroKnowledge.i2leosp256Costed_result
assert_axioms Zcash.Snark.ZeroKnowledge.i2leosp256Costed_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarCodecCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarCodecCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarCodecCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.vestaCoordinateCodecCosted
assert_axioms Zcash.Snark.ZeroKnowledge.vestaCoordinateCodecCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.vestaCoordinateCodecCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.vestaAffineCodecCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.vestaAffineCodecCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.vestaAffineCodecCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPointCodecCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodecCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodecCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.transcriptElementBytesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptElementBytesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptElementBytesCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptElementBytesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.transcriptBytesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.transcriptBytesCosted_cost_le

-- Complete priced proof routing and original message schedule.
assert_computable Zcash.Snark.ZeroKnowledge.appendProducedCosted
assert_axioms Zcash.Snark.ZeroKnowledge.appendProducedCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.appendProducedCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.absorbPointsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPointsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPointsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPointsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbScalarsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalarsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalarsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalarsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbPoints2Costed
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPoints2Costed_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPoints2Costed_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPoints2Costed_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbScalars2Costed
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalars2Costed_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalars2Costed_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbScalars2Costed_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbLookupPairCosted
assert_computable Zcash.Snark.ZeroKnowledge.absorbLookupPermutedCosted
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupPermutedCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupPermutedCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupPermutedCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbPermSetCosted
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPermSetCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPermSetCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPermSetCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.absorbLookupCosted
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookupCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.eraseProofCosts
assert_axioms Zcash.Snark.ZeroKnowledge.ProofFieldReadBound
assert_computable Zcash.Snark.ZeroKnowledge.concatTranscriptBlocksCosted
assert_axioms Zcash.Snark.ZeroKnowledge.concatTranscriptBlocksCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.concatTranscriptBlocksCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.proofEvaluationBlocksCosted
assert_computable Zcash.Snark.ZeroKnowledge.preIpaTranscriptCosted
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaTranscriptCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaRoundBlocksCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRoundBlocksCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptTraceCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTraceCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.concatTranscriptBlocksCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.proofEvaluationBlocksCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaTranscriptCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTraceCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.absorbPermSets2Costed_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.absorbLookups2Costed_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.proofEvaluationBlocksCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaTranscriptCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRoundBlocksCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTraceCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTraceCosted_eleven_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.payPermSetProducer
assert_axioms Zcash.Snark.ZeroKnowledge.payPermSetProducer_result
assert_axioms Zcash.Snark.ZeroKnowledge.payPermSetProducer_readBound
assert_computable Zcash.Snark.ZeroKnowledge.payLookupProducer
assert_axioms Zcash.Snark.ZeroKnowledge.payLookupProducer_result
assert_axioms Zcash.Snark.ZeroKnowledge.payLookupProducer_readBound
assert_computable Zcash.Snark.ZeroKnowledge.fixedClaimReaderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fixedClaimReaderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fixedClaimReaderCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkRoutedProofCosts +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRoutedProofCosts_result
assert_computable Zcash.Snark.ZeroKnowledge.routedProofReadBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRoutedProofCosts_readBound

-- Complete stored-bit transcript, canonical observation, and raw reply prefixes.
assert_computable Zcash.Snark.ZeroKnowledge.observeProtocolTraceCosted
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTraceCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTraceCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedIpaReadersCosted
assert_axioms Zcash.Snark.ZeroKnowledge.storedIpaReadersCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedIpaReadersCosted_readBound
assert_computable Zcash.Snark.ZeroKnowledge.storedJointProofCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointProofCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.storedJointProofInputBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointProofCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointProofCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedJointTraceCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointTraceCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointTraceCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengeSequenceCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeSequenceCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeSequenceCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeSequenceCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.afterStoredChallengeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.afterStoredChallengeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.afterStoredChallengeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.replayOracleScheduleCosted
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleScheduleCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.replayOracleScheduleCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.protocolPrefixCosted
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefixCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefixCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefixCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.protocolQueryPrefixCosted
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefixCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefixCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryPrefixCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.protocolQueryAddressCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddressCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.protocolQueryAddressCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.canonicalProtocolObserverCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolObserverCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolObserverCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.materializePlonkJointView_shape
assert_computable Zcash.Snark.ZeroKnowledge.protocolChallengeCountCosted
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCountCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCountCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleReportCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleReportCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleReportCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedDigestPrefixCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedDigestPrefixCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedDigestPrefixCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_digest_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_digest_agreement
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkSimulatorTapesCosted_digest_cost_le

-- Complete stored-input oracle simulator, its total bound, and exact statistical law.
assert_computable Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleViewCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleViewCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleViewBudget
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalProtocolOracleViewCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointTraceCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedJointTraceCosted_challengeCount

-- Exact original coverage scans, stored data, and collision-free configured-name indices.
assert_computable Zcash.Snark.ZeroKnowledge.gateActivationCoverageScan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.gateActivationCoverageScan_eq
assert_computable Zcash.Snark.ZeroKnowledge.lookupActivationCoverageScan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lookupActivationCoverageScan_eq
assert_computable Zcash.Snark.ZeroKnowledge.coverageListAll
assert_axioms Zcash.Snark.ZeroKnowledge.coverageListAll_cons
assert_computable Zcash.Snark.ZeroKnowledge.coverageTreeFold +choice
assert_axioms Zcash.Snark.ZeroKnowledge.coverageTreeFold_chunk
assert_computable Zcash.Snark.ZeroKnowledge.gateCoverageEmpty +choice
assert_computable Zcash.Snark.ZeroKnowledge.gateCoverageTree +choice
assert_axioms Zcash.Snark.ZeroKnowledge.gateCoverageTree_contains
assert_computable Zcash.Snark.ZeroKnowledge.gateCoveragePredicate +choice
assert_computable Zcash.Snark.ZeroKnowledge.gateCoverageAgainst +choice
assert_axioms Zcash.Snark.ZeroKnowledge.gateActivationCoverageScan_stored
assert_computable Zcash.Snark.ZeroKnowledge.lookupCoverageEmpty +choice
assert_computable Zcash.Snark.ZeroKnowledge.lookupCoverageTree +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lookupCoverageTree_contains
assert_computable Zcash.Snark.ZeroKnowledge.lookupCoveragePredicate +choice
assert_computable Zcash.Snark.ZeroKnowledge.lookupCoverageAgainst +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lookupActivationCoverageScan_stored
assert_computable Zcash.Snark.ZeroKnowledge.gateCoverageIndexLabel
assert_axioms Zcash.Snark.ZeroKnowledge.gateCoverageIndexLabel_eq_iff
assert_axioms Zcash.Snark.ZeroKnowledge.gateCoverageIndexLabel_mem_iff
assert_computable Zcash.Snark.ZeroKnowledge.gateIndexedCoveragePredicate +choice
assert_computable Zcash.Snark.ZeroKnowledge.gateIndexedCoverageScan +choice
assert_axioms Zcash.Snark.ZeroKnowledge.gateIndexedCoverageScan_original
assert_axioms Zcash.Snark.ZeroKnowledge.gateIndexedCoverageScan_stored

-- Complete lookup-prefix and real-prover ratio-scan costs.
assert_computable Zcash.Snark.ZeroKnowledge.lengthListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lengthListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lengthListCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.reverseAuxListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.reverseAuxListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.reverseAuxListCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.reverseListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.reverseListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.reverseListCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.lookupRunPlanCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlanCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlanCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.lookupReservedCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupReservedCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupReservedCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupContainsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupContainsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupContainsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupEraseCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupEraseCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupEraseCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.reserveLookupValuesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValuesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValuesCosted_cost_le_bound
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValuesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.fillLookupPlanCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlanCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlanCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupInsertCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupInsertCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupInsertCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.canonicalLookupSortCosted
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSortCosted_insertionSort
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSortCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSortCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSortCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortColumnsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumnsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValuesCosted_remaining_length
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortColumnsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumnsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortedPrefixesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixesCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortedPrefixesCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.runningProductRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductInitialCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductInitialCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductInitialCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.lookupProductRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRowsCosted_cost_le

-- Complete real lookup-column construction and polynomial query costs.
assert_computable Zcash.Snark.ZeroKnowledge.observeColumnRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.observeColumnRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.observeColumnRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.observeColumnRowsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.observeColumnRowsCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialQuery_eval_finFn
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservedAdviceQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowFixedQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowInstanceQueryCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkRowQueryCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowQueryCostBudget_mono_point
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservedAdviceQueryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowFixedQueryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPublicQueryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRowsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupCompressionCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupSortedRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnPolynomialEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomialEvalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnPolynomialEvalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomialEvalCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomialEvalCostBudget_mono_point
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnRowValueCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRowValueCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnRowValueCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRowValueCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupBaseRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupBaseRowsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupProductCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupBaseRowsCosted_cost_le

-- Complete real permutation factor construction and inherited chunk scans.
assert_computable Zcash.Snark.ZeroKnowledge.prodFinCosted
assert_axioms Zcash.Snark.ZeroKnowledge.prodFinCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.prodFinCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.permutationNumeratorFactorCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationNumeratorFactorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationNumeratorFactorCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.permutationDenominatorFactorCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationDenominatorFactorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationDenominatorFactorCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowNumeratorCosted
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowDenominatorCosted
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowNumeratorCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowDenominatorCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowNumeratorCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowDenominatorCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowNumeratorCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowDenominatorCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowNumeratorCostBudget_mono
assert_axioms Zcash.Snark.ZeroKnowledge.permutationRowDenominatorCostBudget_mono
assert_axioms Zcash.Snark.ZeroKnowledge.columnRef_resolve_polynomial_eval
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationPairAtPointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairAtPointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairAtPointCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.listGetD_length_le_sum
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationFactorCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRowsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationProductCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRowsCosted_cost_le

-- Complete stored private-column construction, masking, and history bounds.
assert_computable Zcash.Snark.ZeroKnowledge.materializeOptionalRowsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.materializeOptionalRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializeOptionalRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.materializeOptionalRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstructColumnResultCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResultCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.storedLookupSortCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnPrepareCostBudget +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnRowCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResultCosted_prepare_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstructStoredColumnCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructStoredColumnCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructStoredColumnCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructStoredColumnCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResultCosted_row_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnRecipesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRecipesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRecipesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRecipesCosted_steps
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnRecipesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRowsCosted_lengths
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRowsCosted_read_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnCostBudget_mono_columns
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredColumnCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredColumnCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredColumnsFromTapeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnsFromTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnsFromTapeCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnsFromTapeCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredColumnsCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnsFromTapeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedColumnHistory +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedRow_getD_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnHistory_materialize
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnHistory_cons_materialized
assert_computable Zcash.Snark.ZeroKnowledge.storedColumnRowsFromTapeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnRowsFromTapeCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnRowsFromTapeCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnRowsFromTapeCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedColumnRowsFromTapeCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.storedMaskedRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedMaskedRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedMaskedRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedMaskedRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.totalizeOptionalRowsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.totalizeOptionalRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.totalizeOptionalRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.totalizeOptionalRowsCosted_cost_le

-- Actual batched tape decoding and complete stored private material.
assert_computable Zcash.Snark.ZeroKnowledge.batchedColumnTapeListsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeListsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeListsCosted_source
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeListsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_castTape
assert_axioms Zcash.Snark.ZeroKnowledge.batchedToColumnTape_cons_list
assert_computable Zcash.Snark.ZeroKnowledge.batchedColumnTapeLists
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowSampleCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeLists_rows_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeLists_blinds_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnTapeLists_result
assert_computable Zcash.Snark.ZeroKnowledge.columnTapeLists +choice
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeLists_append
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeLists_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnBatchesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatchesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatchesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatchesCosted_block_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatchesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkBatchedColumnCoinsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBatchedColumnCoinsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBatchedColumnCoinsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.TapeAgrees.ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted_layout_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted_rows_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredMaterialFromTapeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredMaterialFromTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredColumnsCostBudget_mono_tape
assert_computable Zcash.Snark.ZeroKnowledge.plonkStoredMaterialCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredMaterialFromTapeCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_finCongrTape
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaCoinEquiv_lists
assert_axioms Zcash.Snark.ZeroKnowledge.batchedPreIpaCoinEquiv_lists
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsEquiv_lists
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnBatchesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnBatchesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnBatches_length
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnBatchesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_splitTape
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_joinTape
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_splitTape_left
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_splitTape_right
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_cons_lists
assert_computable Zcash.Snark.ZeroKnowledge.splitListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.splitListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.splitListCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.splitListCosted_lengths_le
assert_computable Zcash.Snark.ZeroKnowledge.columnRowSampleCountCosted
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowSampleCountCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowSampleCountCosted_cost

-- Stored coefficient arithmetic and the complete actual Action numerator.
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_coeff
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_ofArray
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_coeff_eq_zero
assert_computable Zcash.Snark.ZeroKnowledge.denseAddCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseAddCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseAddCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseAddCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseScaleCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseScaleCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseScaleCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseScaleCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseNegCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseNegCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseNegCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseNegCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseMulCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseMulCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseMulCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseMulCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseSubCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseSubCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseSubCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseSubCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseSyntheticCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseSyntheticCosted_identity
assert_axioms Zcash.Snark.ZeroKnowledge.denseSyntheticCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseSyntheticCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.denseDivLinearCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivLinearCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivLinearCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivLinearCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.polynomial_divByMonic_product
assert_axioms Zcash.Snark.ZeroKnowledge.polynomial_div_product_monic
assert_axioms Zcash.Snark.ZeroKnowledge.cPolynomial_div_product_monic
assert_computable Zcash.Snark.ZeroKnowledge.distinctListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.distinctListCosted_mem
assert_axioms Zcash.Snark.ZeroKnowledge.distinctListCosted_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.distinctListCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.distinctListCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.distinctListCosted_toFinset
assert_computable Zcash.Snark.ZeroKnowledge.denseRootDivisor +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseRootDivisor_monic
assert_computable Zcash.Snark.ZeroKnowledge.denseDivRootsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivRootsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivRootsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivRootsCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.denseRootDivisor_nodup
assert_computable Zcash.Snark.ZeroKnowledge.denseDivVanishingCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivVanishingCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivVanishingCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseDivVanishingCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_coefficients
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_rowCoefficientsCosted
assert_computable Zcash.Snark.ZeroKnowledge.domainRootsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.domainRootsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.domainRootsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.domainRootsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseRootDivisor_domain
assert_computable Zcash.Snark.ZeroKnowledge.denseDomainQuotientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainQuotientCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainQuotientCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainQuotientCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseCoefficientBlockCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlockCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlockCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlockCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseCoefficientBlocksCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlocksCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlocksCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlocksCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.denseCoefficientBlocksCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseRotateFromCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateFromCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateFromCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateFromCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.denseRotateCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseRotateCosted_cost
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomial_evaluations
assert_axioms Zcash.Snark.ZeroKnowledge.polynomial_comp_inverse_rotation
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomial_coset_evaluations
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorNode +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorShift_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorNode_off_domain
assert_computable Zcash.Snark.ZeroKnowledge.cosetCoefficientsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.cosetCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.cosetCoefficientsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.cosetCoefficientsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.cosetCoefficientsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkHxCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkHxCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkHxCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkHxCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_replace_x
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorEvalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorEvalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorEvalAccessBudget
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorEvalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorEvalCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorNodeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorNodeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorNodeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorSampleCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorSampleCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorSampleCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorSampleCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorCoefficientsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorCoefficientsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.plonkNumeratorCoefficientsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkNumeratorCoefficientsCosted_cost_le

assert_computable Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseLinearMaskCosted
assert_axioms Zcash.Snark.ZeroKnowledge.denseLinearMaskCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseLinearMaskCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.denseDomainPiecesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainPiecesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainPiecesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainPiecesCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.denseDomainPiecesCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseDomainPiecesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.fixedCoefficientQueryCosted
assert_axioms Zcash.Snark.ZeroKnowledge.fixedCoefficientQueryCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.fixedCoefficientQueryCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCosted
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningGroupMembersCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialFoldFromCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldFromCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldFromCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialFoldStepBudget
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldFromCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialFoldCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialFoldCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialSumCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialSumCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialSumCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialSumCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.densePlonkQuotientPiecesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.densePowerWeightedTermCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePowerWeightedTermCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePowerWeightedTermCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.densePowerWeightedTermCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseWeightedSumCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseWeightedSumCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseWeightedSumCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.denseWeightedSumCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseWeightedSumCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.firstOpeningGroupCosted_property
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPiecesFromRowsCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnCoefficientsCosted_from_rows
assert_computable Zcash.Snark.ZeroKnowledge.privatePolynomialCoefficientsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privatePolynomialCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privatePolynomialCoefficientsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.privatePolynomialCoefficientsCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.privatePolynomialCoefficientsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomial_getD

assert_computable Zcash.Snark.ZeroKnowledge.denseLagrangeNodeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeNodeCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.denseLagrangeNodeCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeNodeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted_quotient_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted_quotient_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenFinalCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.storedOpeningQuotientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedOpeningQuotientCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.denseMultiopenQuotientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenQuotientCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenQuotientCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.denseMultiopenQuotientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseMultiopenQuotientCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseLagrangeCoefficientsCostBudget_mono_lengths
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCostBudget_mono_lengths
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningQuotientCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.listHornerCosted_densePolynomial_result
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialNodeValuesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialNodeValuesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialNodeValuesCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialNodeValuesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangePoly_eval_total
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangeBasis_natDegree_le_total
assert_axioms Zcash.Snark.ZeroKnowledge.lagrangePoly_natDegree_le_total
assert_computable Zcash.Snark.ZeroKnowledge.openingBlindMemberAccessBudget
assert_computable Zcash.Snark.ZeroKnowledge.openingBlindMembersCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.openingBlindMembersCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.openingBlindMembersCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingBlindMembersCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.openingBlindMembersCosted_length_le
assert_computable Zcash.Snark.ZeroKnowledge.openingGroupBlindCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.openingGroupBlindCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.openingGroupBlindCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.openingGroupBlindCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.rowCoefficientsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.rowPolynomialCoefficientsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.rowPolynomialCoefficientsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted_rowProviders_width
assert_axioms Zcash.Snark.ZeroKnowledge.denseOpeningPolynomialCosted_rowProviders_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted_dimensions
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningMaterialCosted_points
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted_stored_width
assert_axioms Zcash.Snark.ZeroKnowledge.denseCollapsedQuotientCosted_stored_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomialsFromRowsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.scalarHornerCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.scalarHornerCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.scalarHornerCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
assert_computable Zcash.Snark.ZeroKnowledge.StoredOpeningGroup.erase +choice
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCosted_points
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted_dimensions
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkOpeningGroupsCosted_points

/- Complete real IPA transcript, original tape decoding, and full structural cost bound. -/
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaMaskCostBudget
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscriptCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.materializedHonestIpaCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaRoundCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaRoundCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscriptCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscriptCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializedHonestIpaCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaVectorReadBudget
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaCoreCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaCoreCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaRoundCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaRoundCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.IpaPublicCosted.readBound_mono
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscriptFromTapeCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscriptFromTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscriptFromTapeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaNextVectorReadBudget
assert_computable Zcash.Snark.ZeroKnowledge.ipaCoreMessagesCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessagesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessagesCostBudget_mono
assert_computable Zcash.Snark.ZeroKnowledge.ipaCoreMessagesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessagesCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTermCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTermCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTermCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTermCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTermsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTermsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTermsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTermsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaFinalBlindCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaFinalBlindCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaFinalBlindCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaFinalBlindCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaFoldReaderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaFoldReaderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ipaFoldReaderCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaInverseRoundCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaInverseRoundCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ipaInverseRoundCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.ipaAlphaTapeCosted
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskTapeCosted
assert_computable Zcash.Snark.ZeroKnowledge.ipaRoundTapeCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaAlphaTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRoundTapeCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.ipaAlphaTapeCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskTapeCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRoundTapeCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskedVectorReadBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskedVectorCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaEvaluationReaderCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaWitnessScalarCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.ipaWitnessScalarCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskedVectorCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskedVectorCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.ipaEvaluationReaderCosted
assert_axioms Zcash.Snark.ZeroKnowledge.ipaEvaluationReaderCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_inverse_rounds
assert_computable Zcash.Snark.ZeroKnowledge.ipaWitnessScalarCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaWitnessScalarCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaTermCosted
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaTermCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaCoefficientCosted
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaCoefficientCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaCoefficientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaCoefficientCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.vectorCommitmentCosted
assert_axioms Zcash.Snark.ZeroKnowledge.vectorCommitmentCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.vectorCommitmentCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.innerProductCosted
assert_axioms Zcash.Snark.ZeroKnowledge.innerProductCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.innerProductCosted_cost_le

/- Complete real PLONK commitments, opening data, and joint IPA composition. -/
assert_computable Zcash.Snark.ZeroKnowledge.privateCommitmentCoefficientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.privateCommitmentCoefficientCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.privateCommitmentCoefficientCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateCommitmentCoefficientCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCosted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentCoefficientCosted_from_rows
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialCommitmentCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialCommitmentCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.densePolynomialCommitmentCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.densePolynomialCommitmentCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.getFinListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.getFinListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.getFinListCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestJointRowsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.honestJointRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestJointRowsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestJointRowsCosted_dimensions
assert_axioms Zcash.Snark.ZeroKnowledge.honestJointRowsCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkMaskCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted_points_length
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted_columns_length
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted_observations_width
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.materializeRowsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.materializeRowsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.materializeRowsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.materializeRowsCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.materializeRowsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentPointsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPointsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPointsCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentPointsCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPointsCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.preparedHonestIpaCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.preparedHonestIpaCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.preparedHonestIpaCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.preparedHonestIpaCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.preparedHonestIpaCosted_computed
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnAtCosted
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnAtCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnAtCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.emptyStoredOpeningGroup +choice
assert_computable Zcash.Snark.ZeroKnowledge.storedFirstOpeningCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedFirstOpeningCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedFirstOpeningCosted_width
assert_axioms Zcash.Snark.ZeroKnowledge.storedFirstOpeningCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedMultiopenBlindCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenBlindCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.storedMultiopenBlindCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenBlindCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_width
assert_computable Zcash.Snark.ZeroKnowledge.storedMultiopenDataCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.StoredMultiopenData
assert_computable Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_quotient_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_polynomial_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_blind_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedMultiopenDataCosted_value_result

/- Complete real private-tape construction, stored inputs, and canonical observed view. -/
assert_axioms Zcash.Snark.ZeroKnowledge.honestStoredMaterialCosted_dimensions
assert_axioms Zcash.Snark.ZeroKnowledge.honestTapeJointCosted_dimensions
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_challenge_prices
assert_axioms Zcash.Snark.ZeroKnowledge.honestTapeJointCostBudget_congr_prices
assert_computable Zcash.Snark.ZeroKnowledge.honestStoredMaterialInputBudget
assert_computable Zcash.Snark.ZeroKnowledge.honestStoredMaterialCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestStoredMaterialCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestStoredMaterialCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestStoredMaterialCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.honestStoredMaterialCostBudget_mono_tape
assert_computable Zcash.Snark.ZeroKnowledge.honestTapeJointCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestTapeJointCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.honestTapeJointCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.honestTapeJointCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsCosted_blinds_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStoredMaterialFromTapeCosted_dimensions
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestInputBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestJointCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestTapeJointCosted_shape
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestTapeJointCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestTapeJointCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestTraceCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestTraceCosted_cost_le_fixed
assert_computable Zcash.Snark.ZeroKnowledge.encodeActionWitness
assert_computable Zcash.Snark.ZeroKnowledge.storedActionWitnessRowCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionWitnessRowCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionWitnessRowCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkProverTapeReadBudget
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkProverTapeCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapes
assert_computable Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_lengths
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_raw_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_challenges_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_private_result
assert_computable Zcash.Snark.ZeroKnowledge.storedPrivateMaterial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedPrivateMaterial_materialize
assert_axioms Zcash.Snark.ZeroKnowledge.storedPrivateMaterial_readers
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_digest_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_digest_agreement
assert_axioms Zcash.Snark.ZeroKnowledge.storedPlonkProverTapesCosted_digest_cost_le

/- Complete real cached attempt from stored raw tapes. -/
assert_computable Zcash.Snark.ZeroKnowledge.cachedPrefixRunCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.cachedPrefixRunCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.cachedPrefixRunCosted
assert_axioms Zcash.Snark.ZeroKnowledge.cachedPrefixRunCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.cachedPrefixRunCosted_cache_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.cachedPrefixRunCosted_result_of_history_bound
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHistoryTraceCostBudget_mono_history
assert_computable Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCostBudget +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedActionHonestFieldTraceCostBudget_congr_prices
assert_computable Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted_readBound
assert_axioms Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted_prices
assert_axioms Zcash.Snark.ZeroKnowledge.storedHistoryChallengesCosted_agreement
assert_computable Zcash.Snark.ZeroKnowledge.rawFieldWordCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rawFieldWordCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.rawFieldWordCosted_cost
assert_computable Zcash.Snark.ZeroKnowledge.storedRawFieldsCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawFieldsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawFieldsCosted_length
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawFieldsCosted_ofFn_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawFieldsCosted_cost_le

/- Complete counted real retries and their exact verifier-bit law. -/
assert_computable Zcash.Snark.ZeroKnowledge.runStatefulRetriesCosted
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetriesCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_map_tape
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetries_congr_retry
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetriesCosted_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.runStatefulRetriesCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.oracleAttemptStateCosted
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptStateCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.oracleAttemptStateCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.oracleRetryRequestedCosted
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequestedCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.oracleRetryRequestedCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.rawMatrixBitsEquiv +choice
assert_axioms Zcash.Snark.ZeroKnowledge.rawMatrixBitsEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRawMatrixBits
assert_computable Zcash.Snark.ZeroKnowledge.storedRawMatrixCosted +choice
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawMatrixCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawMatrixCosted_shape
assert_computable Zcash.Snark.ZeroKnowledge.storedRawMatrixCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.storedRawMatrixCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.zipListCosted_ofFn_result
assert_axioms Zcash.Snark.ZeroKnowledge.zipListCosted_shape

/- Complete executable PRNG reductions, full-view tests, and resource admissibility. -/
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.inputCost
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.evalCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.runBooleanTestCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestProgram.costBudget
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram.evalCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestInstruction
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.eval
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.evalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.evalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.runBooleanTest
assert_computable Zcash.Snark.ZeroKnowledge.runBooleanTestCosted
assert_axioms Zcash.Snark.ZeroKnowledge.runBooleanTestCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.runBooleanTestCosted_length
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestProgram.eval
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestProgram.evalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram.evalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.mapInput
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.eval_mapInput
assert_computable Zcash.Snark.ZeroKnowledge.BooleanTestProgram.mapInput
assert_axioms Zcash.Snark.ZeroKnowledge.runBooleanTest_mapInput
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram.eval_mapInput
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram.mapInput_length
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestInstruction.eval_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.runBooleanTest_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.BooleanTestProgram.eval_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.getDListCosted_cost_le_index
assert_computable Zcash.Snark.ZeroKnowledge.getOptionListCosted
assert_axioms Zcash.Snark.ZeroKnowledge.getOptionListCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.getOptionListCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkHistoryChallenges_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.uniformRawPlonkChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.uniformBitPlonkChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.interactiveRecordedView_injective
assert_axioms Zcash.Snark.ZeroKnowledge.RawTapeTestAddress
assert_computable Zcash.Snark.ZeroKnowledge.RawTapeTestAddress.eval
assert_computable Zcash.Snark.ZeroKnowledge.RawTapeTestAddress.evalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.RawTapeTestAddress.evalCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.RawTapeTestAddress.costBudget
assert_axioms Zcash.Snark.ZeroKnowledge.RawTapeTestAddress.evalCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.RawTapeTestProgram
assert_computable Zcash.Snark.ZeroKnowledge.rawTapeTest
assert_computable Zcash.Snark.ZeroKnowledge.rawTapeTestCosted
assert_axioms Zcash.Snark.ZeroKnowledge.rawTapeTestCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.rawTapeTestCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.rawTapeTestCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.RecordedTestProgram
assert_computable Zcash.Snark.ZeroKnowledge.recordedViewTest
assert_computable Zcash.Snark.ZeroKnowledge.recordedViewTestCosted
assert_axioms Zcash.Snark.ZeroKnowledge.recordedViewTestCosted_result
assert_computable Zcash.Snark.ZeroKnowledge.recordedViewTestCostBudget
assert_axioms Zcash.Snark.ZeroKnowledge.recordedViewTestCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.recordedExhaustionTest
assert_axioms Zcash.Snark.ZeroKnowledge.recordedExhaustionTest_eval
assert_computable Zcash.Snark.ZeroKnowledge.copyAuxiliaryWordsCosted
assert_axioms Zcash.Snark.ZeroKnowledge.copyAuxiliaryWordsCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.copyAuxiliaryWordsCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.RecordedTestCacheSlot
assert_axioms Zcash.Snark.ZeroKnowledge.RecordedTestAddress
assert_computable Zcash.Snark.ZeroKnowledge.testEmptyAttempt
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestOutput
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestCache
assert_computable Zcash.Snark.ZeroKnowledge.optionalByteTest
assert_computable Zcash.Snark.ZeroKnowledge.optionalFieldTest
assert_computable Zcash.Snark.ZeroKnowledge.optionalRawWordTest
assert_computable Zcash.Snark.ZeroKnowledge.RecordedTestAddress.eval
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestHistoryCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestOutputCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestCacheCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestProofCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestScalarCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestCacheEntryCosted
assert_computable Zcash.Snark.ZeroKnowledge.recordedTestCacheByteCosted
assert_computable Zcash.Snark.ZeroKnowledge.RecordedTestAddress.evalCosted
assert_axioms Zcash.Snark.ZeroKnowledge.RecordedTestAddress.evalCosted_result
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestHistoryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestOutputCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestCacheCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestProofCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestScalarCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestCacheEntryCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTestCacheByteCosted_cost_le
assert_computable Zcash.Snark.ZeroKnowledge.RecordedTestAddress.indexSum
assert_computable Zcash.Snark.ZeroKnowledge.RecordedTestAddress.costBudget
assert_axioms Zcash.Snark.ZeroKnowledge.RecordedTestAddress.evalCosted_cost_le
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTest_history_absence_regression
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTest_cache_routing_regression
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTest_query_parts_regression
assert_axioms Zcash.Snark.ZeroKnowledge.rawTapeTest_candidate_regression
assert_axioms Zcash.Snark.ZeroKnowledge.booleanTest_wire_routing_regression
assert_axioms Zcash.Snark.ZeroKnowledge.recordedTest_failure_status_regression
assert_axioms Zcash.Snark.ZeroKnowledge.StreamTestProgram
assert_computable Zcash.Snark.ZeroKnowledge.streamViewTest
assert_computable Zcash.Snark.ZeroKnowledge.StreamTestProgram.toRecorded
assert_axioms Zcash.Snark.ZeroKnowledge.streamViewTest_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.streamViewTest_recorded
assert_axioms Zcash.Snark.ZeroKnowledge.StreamTestAddress
assert_computable Zcash.Snark.ZeroKnowledge.StreamTestAddress.toRecorded
assert_computable Zcash.Snark.ZeroKnowledge.StreamTestAddress.index
assert_computable Zcash.Snark.ZeroKnowledge.StreamTestAddress.readEntry
assert_computable Zcash.Snark.ZeroKnowledge.StreamTestAddress.eval
assert_axioms Zcash.Snark.ZeroKnowledge.StreamTestAddress.eval_measurable
assert_axioms Zcash.Snark.ZeroKnowledge.StreamTestAddress.eval_recorded
