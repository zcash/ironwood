import Zcash.Security.KeyBinding.Instance
import Zcash.Security.KeyBinding.Probability
import Zcash.Security.Common.Birthday
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Meta.AxiomCheck
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Deployed.ConcreteBounds
import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.Forking.Adversary
import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Composition.Completeness
import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Composition.Prefixes
import Zcash.Snark.Soundness.Composition.Residual
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction
import Zcash.Snark.Soundness.VestaBudget
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.ConstraintRelations
import Zcash.Snark.Soundness.ChallengePricing

/-!
# Trust boundary, build-checked

The library-wide census that makes the trust claims build-time checks rather than prose: a change
that widens a declaration's trusted base — a `sorry` reached through some dependency, an unexpected
axiom, or `native_decide` where none was permitted — fails this file rather than passing silently.

Two commands from `Zcash.Meta.AxiomCheck`, per the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`):

* **Computed break reductions** get `assert_computable`: the declaration is a plain `def` — not a
  theorem, not marked `noncomputable` — with axioms bounded by `propext` / `Quot.sound`.
  `+choice` additionally permits `Classical.choice`; with the plain-`def` check this asserts
  choice enters only through erased `Prop` certificate fields, so the break data cannot have been
  conjured from mere propositional existence.
* **Theorems** get `assert_axioms`, an upper bound at the standard tier
  (`propext` / `Classical.choice` / `Quot.sound`). Both commands reject `sorryAx`.
-/

open Zcash.Security.KeyBinding Zcash.Security.RandomOracle Zcash.Security.Birthday
open Zcash.Security.Ledger Zcash.Security.BindingSignature
open Zcash.Meta

/-! ## Key binding — computed break reductions -/

assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak +choice
assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak +choice

/-! ## Key binding — theorems -/

assert_axioms Zcash.Security.KeyBinding.Extractor.card_ivk_ge
assert_axioms Zcash.Security.KeyBinding.commit_scalar_pm
assert_axioms Zcash.Security.KeyBinding.rivk_eq_finalOracle
assert_axioms Zcash.Security.KeyBinding.sameIvk_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.openingBreak_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.break_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.residual_of_finalQuery_eq
assert_axioms Zcash.Security.KeyBinding.nk_pinned
assert_axioms Zcash.Security.KeyBinding.ak_pinned
assert_axioms Zcash.Security.KeyBinding.qk_or_sk_pinned
assert_axioms Zcash.Security.KeyBinding.collision_mem_shifted_pm
assert_axioms Zcash.Security.KeyBinding.toInterface

/-! ## Birthday bound -/

assert_axioms Zcash.Security.Birthday.card_shifted_pm_collision_le
assert_axioms Zcash.Security.Birthday.shifted_pm_collision_fraction_le
assert_axioms Zcash.Security.Birthday.birthday_closed_form

/-! ## Key binding — whole-table random-oracle model -/

assert_computable Zcash.Security.KeyBinding.finalQueryEquiv
assert_axioms Zcash.Security.KeyBinding.eval_restrict
assert_axioms Zcash.Security.KeyBinding.pair_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.finset_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.ofBreak_queries
assert_axioms Zcash.Security.KeyBinding.break_measure_le
assert_computable Zcash.Security.KeyBinding.badList
assert_axioms Zcash.Security.KeyBinding.mem_badList
assert_axioms Zcash.Security.KeyBinding.badList_measure_le
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory_measure_le
assert_axioms Zcash.Security.KeyBinding.CollidesDuring
assert_axioms Zcash.Security.KeyBinding.CollidesDuring.of_pair
assert_axioms Zcash.Security.KeyBinding.sum_two_mul_add
assert_axioms Zcash.Security.KeyBinding.collidesDuring_measure_le
assert_axioms Zcash.Security.KeyBinding.queries_pair_collision_measure_le
assert_computable Zcash.Security.KeyBinding.derivQueries
assert_axioms Zcash.Security.KeyBinding.break_measure_le_adaptive
assert_axioms Zcash.Security.KeyBinding.break_measure_le_of_queryBound
assert_axioms Zcash.Security.KeyBinding.toOuterMeasure_bind_le
assert_axioms Zcash.Security.KeyBinding.break_measure_le_mixture
assert_axioms Zcash.Security.KeyBinding.uniformOfFintype_prod
assert_computable Zcash.Security.KeyBinding.evalEquiv
assert_axioms Zcash.Security.KeyBinding.uniform_triple_eval
assert_axioms Zcash.Security.KeyBinding.break_measure_le_product
assert_axioms Zcash.Security.toInterface_break_measure_le

/-! ## Ledger-layer break reductions

These data-producing reductions rest on `propext` and `Quot.sound` only — no `Classical.choice`
even in erased positions, which is the strict (flagless) `assert_computable` tier. -/

assert_computable Collision.upToSign
assert_computable Merkle.collisionOfWrongLeaf
assert_computable noteCommitBreakOfNe
assert_computable Zcash.Security.Ledger.nfOldEqOrBreak +choice

/-! ## Binding-signature relation reductions

Unlike the ledger break reductions, these depend on `Classical.choice` (`+choice`). It enters
only through erased `Prop` certificate fields (the arithmetic side proofs); the relation
coefficients themselves are direct terms of the inputs, and the plain-`def` check means the data
cannot have been conjured from mere propositional existence. -/

assert_computable NontrivialRelation.ofImbalance +choice
assert_computable NontrivialRelation.ofBundleModImbalance +choice
assert_computable NontrivialRelation.ofBundleIntImbalance +choice
assert_computable NontrivialRelation.ofOrchardImbalance +choice
assert_computable NontrivialRelation.ofSaplingImbalance +choice

/-!
## SNARK soundness stack

The census also carries the SNARK binding and knowledge-soundness reductions, consolidated here
from the former per-directory files and, like the key-binding and ledger sections above, expressed
through the `Zcash.Meta.AxiomCheck` macros rather than the older `assert_no_sorry` +
`#guard_msgs`-pinned `#print axioms` idiom:

* **Computed break reductions** — the data-producing `def`s that extract a discrete-log relation
  from a collision, fold, peel, or fork — get `assert_computable`: a plain `def`, not marked
  `noncomputable`. `Classical.choice` enters only through erased `Prop` certificate fields
  (`+choice`); the relation coefficients are direct terms of the inputs, so the break data cannot
  have been conjured from mere propositional existence. Vesta-instantiated producers additionally
  inherit CompElliptic's `native_decide` curve point-count axiom (`+native`).
* **Theorems** — the probability-layer bounds, the knowledge-soundness and binding endpoints across
  all adversary models, the DL capstones, and the run-time/query-charge lemmas — get
  `assert_axioms`, bounding the trusted base at the standard tier (`propext` / `Classical.choice` /
  `Quot.sound`), with `+native` on the Vesta-instantiated endpoints.
-/

open Zcash.Snark

/-! ### Binding reductions from IPA/CommitFold collisions -/

assert_computable NontrivialDLRelation.ofCollision +choice
assert_computable NontrivialDLRelation.ofIpaOpenings +choice

/-! ### Verifier-soundness capstones -/

assert_axioms deployedAccepts_verifierEq
assert_axioms orchard_verifier_sound_conditional
assert_axioms orchard_verifier_deployed_opening_of_forked
assert_axioms orchard_verifier_deployed_constraint_of_forked
assert_axioms orchard_verifier_sound_vesta_conditional +native
assert_axioms orchard_verifier_vesta_opening_of_forked +native
assert_axioms orchard_verifier_vesta_constraint_of_forked +native

/-! ### Deployed binding-reduction breaks

The binding reductions return computed data (plain `def`s); the same treatment covers the forking
reductions `ipa_extractV`, `ipaRelation_extract`, `produceDeployed`, `deployed_forking_tree`, and
`deployed_forking_relation`, each computing its witness from an explicit certificate. -/

assert_computable NontrivialRelation.ofCombinationCollision +choice
assert_computable NontrivialRelation.ofFoldedGens +choice
assert_computable NontrivialRelation.ofLeafPeel +choice
assert_computable NontrivialRelation.ofDeployedTree +choice
assert_computable NontrivialRelation.ofUnopenedFork +choice
assert_computable NontrivialRelation.ofUnopenedForkVesta +choice +native
assert_computable ipa_extractV +choice
assert_computable ipaRelation_extract +choice
assert_computable produceDeployed +choice
assert_computable deployed_forking_tree +choice
assert_computable deployed_forking_relation +choice

/-! ### AGM / Fiat–Shamir soundness

The AGM kernels compute representations, openings, relations, certificates, and deployed instances
as data (`assert_computable`); the probability layer, the knowledge-soundness and binding endpoints,
and the run-time bounds are theorems (`assert_axioms`). -/

assert_computable discreteLogOfBasis_of_relation +choice
assert_computable DLChallengeGame.solveFromRelation +choice
assert_computable fixedSlotExtractOrMiss +choice
assert_computable AugmentedRelationWitness.toAlgebraicRelationWitness +choice
assert_computable relationWitnessOfCollision +choice
assert_computable discreteLogOfAugmentedRelationAtChallenge +choice
assert_computable separateOrRelationWitness +choice
assert_computable relationOfFoldGensWitness +choice
assert_computable deployedLeafPeelWitness +choice
assert_computable deployedToAcceptVWitness +choice
assert_computable algebraicRelationOfDeployedAccept +choice
assert_axioms AlgebraicProver.toProver
assert_axioms AlgebraicDForkCert.toDForkCert
assert_axioms algebraicProverAccept_forkValid
assert_computable deployedAlgebraicForkingRelation +choice
assert_axioms deployed_forking_relation_shifted
assert_axioms deployedAlgebraicForkingRelation_shifted
assert_computable deployedAlgebraicForkingFixedSlot +choice
assert_axioms DeployedAlgebraicForkingInstance.run
assert_axioms DeployedAlgebraicForkingInstance.ProducesRelation
assert_axioms deployedAlgebraicRelationProduced
assert_axioms deployedAlgebraicRelationEvent
assert_computable deployedAlgebraicRelationFinder +choice
assert_axioms deployedAlgebraicRelationFinder_isSome_iff
assert_computable deployedAlgebraicRelation +choice
assert_computable deployedAlgebraicRelationWitness +choice
assert_axioms orchardDeployedAlgebraicForkingFixedSlot +native
assert_axioms orchardDeployedRelationSet +native
assert_axioms OrchardUniformURSIdentification +native
assert_axioms orchardGeneratorROSetup
assert_axioms orchardGeneratorROBasis
assert_axioms orchard_uniformURSIdentification_of_generatorRO +native
assert_axioms recursiveAlgebraicForkFrom
assert_axioms recursiveAlgebraicForkFrom_realizes
assert_axioms algebraicForkCertAttempt +native
assert_axioms algebraicForkCertAttempt_valid +native
assert_axioms computedDeployedAlgebraicInstance +native
assert_axioms computedAlgebraicInstanceFailure_measure_le +native
assert_axioms AlgebraicRelationWitness.augment
assert_axioms DeployedAlgebraicForkingInstance.runRelation
assert_axioms DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
assert_computable DeployedAlgebraicForkingInstance.runToSnark +choice +native
assert_axioms ComputedAlgebraicFSFamily.relationFinder +native
assert_axioms ComputedAlgebraicFSFamily.relationFinder_isSome_of_bindingWin +native
assert_axioms ComputedAlgebraicFSFamily.snarkRelationFinder +native
assert_axioms ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le +native
assert_axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure +native
assert_axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.ReductionEfficient +native
assert_axioms ComputedAlgebraicFSFamily.reductionEfficient_exists +native
assert_axioms ComputedAlgebraicFSFamily.instanceAttempt_runs_eq +native
assert_axioms ComputedAlgebraicFSFamily.reductionEfficient_exponential +native
assert_axioms ComputedAlgebraicFSFamily.DiscreteLogRelationHardFor +native
assert_axioms ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL +native
assert_axioms ComputedAlgebraicFSFamily.binding_under_DL +native
assert_axioms bindingWin_unbounded_measure_le +native
assert_axioms queryCharge
assert_axioms queryCharge_sum_mul_le
assert_axioms le_queryCharge_of_mem_queries
assert_axioms mem_queries_dedup
assert_axioms applyUpdates_apply_mem_nodup
assert_axioms queryCharge_sum_mul_le_table_budget
assert_axioms steeredCharge_context_sum_mul_le
assert_axioms steeredCharge_context_sum_mul_le_table_budget
assert_axioms steeredCharge_sum_mul_le
assert_axioms scanCandidate_self
assert_axioms self_mem_goodChallenges_iff
assert_axioms scanRank_insert_erase
assert_axioms scanRank_insert_eq_filter
assert_axioms goodChallengesAt
assert_axioms OracleComp.queries_queryList
assert_axioms recursiveAlgebraicForkFrom_node_runs_le_gated
assert_axioms OracleComp.queries_bind
assert_axioms OracleComp.mem_queries_completing
assert_axioms scanCandidateAt
assert_axioms scanCandidateAt_fork
assert_axioms scanCandidateAt_update
assert_axioms goodChallengesAt_fork
assert_axioms goodChallengesAt_update
assert_axioms sum_card_scanRank_erase_lt_le
assert_axioms OracleComp.restrictSum
assert_axioms fsWinsFull_restrictSum_le
assert_axioms ComputedAlgebraicFSFamilyRand.determinize
assert_axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailureEvent +native
assert_axioms ComputedAlgebraicFSFamilyRand.foldedRelationFinder +native
assert_axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamilyRand.foldedSnarkRelationFinder +native
assert_axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand +native
assert_computable ComputedAlgebraicFSFamilyUnbounded.globalReachSet +choice
assert_axioms ComputedAlgebraicFSFamilyUnbounded.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnbounded.splitFamilyRand +choice
assert_axioms ComputedAlgebraicFSFamilyUnbounded.run_splitFamilyRand_adversary
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL +native
assert_axioms uniformURS_basis_transfer +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailureEventUnbounded +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.bindingEventUnbounded +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.determinize
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.globalReachSet +choice
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.splitFamilyRand +choice
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.run_splitFamilyRand_adversary
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailureEventUnboundedRand +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.bindingEventUnboundedRand +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL +native
assert_axioms recursiveAlgebraicForkFrom_node_runs_le
assert_axioms recursiveAlgebraicFork_sum_runs_le_unconditional
assert_axioms recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional
assert_axioms recursiveAlgebraicForkFrom_sum_runs_le_of_forkSpread
assert_axioms recursiveAlgebraicFork_sum_runs_le_of_forkSpread
assert_axioms AlgebraicPoint.point_eq_components +native
assert_axioms Msm.eval_repr +native
assert_axioms RepresentedMultiopen.ofCoveredList +native
assert_axioms AlgebraicWfProof.ofRepresented +native
assert_axioms assembleQueries_points_mem
assert_axioms constructIntermediateSets_ref_mem
assert_axioms multiopenMsm_points_mem
assert_axioms AlgebraicWfProof.ofStandard +native
assert_axioms OracleComp.reachSet
assert_axioms OracleComp.run_congr_reachSet
assert_axioms OracleComp.restrictTo
assert_axioms OracleComp.splitDomain
assert_axioms finite_domain_restriction
assert_axioms fsWinsFull_mapDomain_measure_eq
assert_axioms fsWinsFull_splitDomain
assert_axioms fsWinsFull_unbounded_measure_le
assert_axioms truncateTranscript
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog +choice
assert_axioms Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_axioms Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog
assert_axioms hitProb_ge_inv_card
assert_axioms relSet_card_le_succSet_card
assert_axioms reduction_advantage_ge
assert_axioms relation_prob_le_of_DL
assert_axioms winSet_card
assert_axioms textbook_winProb_eq_succProb
assert_axioms relation_prob_le_of_textbookDL
assert_axioms orchard_relation_prob_le_of_DL +native
assert_axioms orchard_reduction_advantage_ge +native
assert_axioms orchard_relation_prob_le_of_textbookDL +native
assert_axioms commitment_binding_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_reduction_advantage_ge +native
assert_axioms orchard_deployed_relation_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_relation_set_eq_relSet +native
assert_axioms orchard_deployed_relation_event_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_relation_prob_eq_of_uniformURS +native
assert_axioms orchard_deployed_relation_prob_le_of_uniformURS_textbookDL +native
assert_axioms orchard_deployed_relation_prob_le_of_generatorRO_textbookDL +native

/-! ### Fork-tree knowledge error

The closed form of the fork-tree knowledge error and its evaluation over the deployed Orchard
parameters. All theorems, so `assert_axioms`: the arithmetic runs on `Nat`/`ℝ≥0∞` and the deployed
field cardinality comes from `ZMod.card`, so no compiler trust enters here. -/

assert_axioms kerr_mul_card
assert_axioms kerr_eq
assert_axioms kerr_div_card
assert_axioms deployed_forking_knowledge_error
assert_axioms deployed_forking_knowledge_error_captured

/-! ### Multiopen decode, budgeted extraction, and the forking composition

The decode layer that recovers the verifier's columns from the batched multiopen, the budgeted
extraction that replaces the per-run squeeze floors with one joint accept floor, and the
composition layer that joins the forking extraction to the decoded capstones. Theorems throughout,
so `assert_axioms`, with `+native` on the Vesta-instantiated endpoints. -/

-- The multiopen value-check chain: the deployed value check derived from the nested
-- forking floors, the x₁ member un-batch on top of it, and the terminal with `hadvice`/`hinstance`
-- produced rather than assumed (`Soundness.Multiopen.NodeBinding`, `Soundness.Vesta`).
assert_axioms deployed_value_check_node_binding
assert_axioms deployed_member_node_binding
assert_axioms orchard_verifier_vesta_member_constraint_derived +native

-- The forking-extraction ∘ decoded-capstone composition (`Soundness.Composition.Bridge`): the algebraic
-- clean opening identified with the deployed capstone's shape (`ipaRelation_deployed_of_instance`),
-- the witness-tie composition (`member_snark_of_instance`), and the computed-path soundness
-- endpoint (`orchard_verifier_sound_vesta_computed`) that concludes the plain `SnarkRelation` with
-- NO `ExtractableFromAcceptance` hypothesis. On the witness tie the opened-value shift is derived
-- (`shift_eq_zero_of_openings_agree`), so `hshift` survives only on the standalone single-opening
-- bridge. `snarkExtraction_prob_le_of_generatorRO_textbookDL` is the CONDITIONAL knowledge-error
-- bound: the SNARK-extraction failure is contained in the clean-opening failure and inherits its
-- `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε` bound, conditional on `hExtract` (clean opening ⟹
-- extraction). Discharging `hExtract` — coupling the AGM family's coin measure to the multiopen
-- budget below — is the remaining reconciliation.
assert_axioms ipaRelation_deployed_of_instance +native
assert_axioms member_snark_of_instance +native
assert_axioms snarkRelation_of_memberColumns
assert_axioms orchard_verifier_sound_vesta_computed +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL +native
assert_axioms instanceAttempt_provenance +native
assert_axioms ipaRelation_deployed_of_openings_agree +native
assert_axioms shift_eq_zero_of_openings_agree +native

-- The budgeted multiopen extraction (`Soundness.Multiopen.FloorBudget`,
-- `Soundness.Multiopen.BudgetedExtraction`): the heavy-fiber Markov descent
-- (`uniformOfFintype_heavy_fiber_lt`) replaces the `∀`-over-runs squeeze floors of the value-check
-- and member cores with a single joint accept floor at honest-base thresholds, the runs pinned by
-- the canonical selectors; `deployed_member_budget` is the combined soundness budget — the joint
-- accept measure sits within the four-threshold budget, or every decoded member column takes its
-- claimed evaluation (or a computed relation exists).
assert_axioms uniformOfFintype_heavy_fiber_lt
assert_axioms deployed_value_check_node_binding_budgeted
assert_axioms deployed_member_node_binding_budgeted
assert_axioms deployed_member_budget

-- The decode layer (`Soundness.Multiopen.Decode`/`Deployed`): the Vandermonde recovery of the
-- column witnesses, the deployed x4 collapse proved to be a flat power batch, and the two-level
-- binding of the extracted witness to the member commitments.
assert_axioms decodedColumnFamily_of_batch_openings
assert_axioms deployedCommitment_x4_batch
assert_axioms multiopenValue_x4_batch
assert_axioms x1_batch_open_soundV
assert_axioms member_binding_of_x1_samples
assert_axioms deployed_witness_member_binding
assert_axioms deployed_witness_two_level
assert_axioms node_binding_of_samples
-- The multiopen support modules, pinned directly rather than transitively through the capstones
-- above. `Opened` holds the rewind accept events and the three `Classical.choose` witness
-- extractors; `RPoly` the interpolation/power-form algebra; `Compat` the Msm-evaluation and
-- two-openings binding lemmas; `Claimed` the counting cores; `ValueCheckDeployed` the deployed
-- point sets. A stray axiom here would surface at a capstone, but only these pins name the
-- declaration that introduced it.
assert_axioms vandermonde_decode_map
assert_axioms vandermonde_reconstruct_map
assert_axioms openedColumnDecode
assert_axioms openedDecodedCols
assert_axioms openedDecodedCols_eval_x3
assert_axioms openedDecodedCols_top_eval_x3
assert_axioms OpenedColumnDecode.currentWitness_eq
assert_axioms openedRewindForRelation_of_batch
assert_axioms openedX4Batch_of_witnessFamily
assert_axioms OpenedX4Accept
assert_axioms openedX4Accept_of_deployedAccepts
assert_axioms OpenedX3Accept
assert_axioms openedX3Accept_of_deployedAccepts
assert_axioms OpenedX2Accept
assert_axioms openedX2Accept_of_deployedAccepts
assert_axioms openedX4Rewind_of_x4Prob
assert_axioms openedX4Rewind_of_x4Prob_forked
assert_axioms OpenedBatchOpenings.ipaRelation_of_x4Current
assert_axioms opened_constraint_of_relation_and_batch
assert_axioms x1DecodeComp
assert_axioms opened_witness_member_binding
assert_axioms OpenedX1Accept
assert_axioms openedX1Accept_of_deployedAccepts
assert_axioms openedMemberDecode_of_x1Prob
assert_axioms rotatedFeed
assert_axioms member_constraint_of_relation_and_batch
assert_axioms member_constraint_of_relation_and_batch_xgood
assert_axioms poly_eq_of_agree_on_family
assert_axioms foldl_range_add_eq_sum
assert_axioms foldl_range_guardProd_eq_prod
assert_axioms guardProd_eq_prod_erase
assert_axioms lagrangePoly
assert_axioms lagrangePoly_eval_node
assert_axioms lagrangePoly_eval
assert_axioms foldl_mul_inv_eq_prod
assert_axioms multiopenEval_powerForm
assert_axioms coeffs_zero_of_power_sum_vanishes
assert_axioms multiopenEval_perSet_zero_of_samples
assert_axioms lagrangePoly_natDegree_lt
assert_axioms col_eq_lagrangePoly_of_samples
assert_axioms col_eval_node_eq_claimed
assert_axioms Msm.eval_zero
assert_axioms Msm.eval_scale
assert_axioms Msm.eval_add
assert_axioms HasNontrivialRelation
assert_axioms HasNontrivialRelation.of_nontrivialRelation
assert_axioms deployed_to_acceptV
assert_axioms hasNontrivialRelation_of_two_openings
assert_axioms decoded_constraint_of_relation_and_batch
assert_axioms decoded_constraint_of_opening_or_relation
assert_axioms claimedEval_of_x3Prob
assert_axioms claimedCombined_of_x2Prob
assert_axioms gateGood_of_xProb
assert_axioms hgood_of_xProb
assert_axioms deployedSetPts
assert_axioms deployedAllPts
assert_axioms deployedSetPts_subset
assert_axioms member_aggregate_eval_bridge
assert_axioms deployed_query_point_mem
-- The avoidance-strengthened forking count (`Soundness.Forking.Probability`): the counting lemma
-- that buys the multiopen grid's interpolation samples off the opened set points, so the value
-- check takes no sample-avoidance hypothesis.
assert_axioms exists_injective_accepting_avoiding_of_measure
-- The good-challenge production (`Soundness.GoodChallenge`): the Schwartz-Zippel exclusion budget
-- and the pigeonhole that produces an accepting challenge outside the bad set.
assert_axioms uniformChallenge_szBadSet
assert_axioms uniformChallenge_szGoodSet
assert_axioms uniformChallenge_quotient_szBadSet
assert_axioms uniformChallenge_szBadSet_union
assert_axioms exists_accepting_good_challenge
assert_axioms exists_accepting_good_challenge_quotient
-- The deployed Vesta capstone family: the decoded-column rungs and the terminal, alongside the
-- derived capstone already pinned below.
assert_axioms orchard_verifier_vesta_decoded_constraint_of_forked_x4 +native
assert_axioms orchard_verifier_vesta_forking_constraint_deployed_x4 +native
assert_axioms orchard_verifier_vesta_member_constraint_deployed_x4 +native
assert_axioms orchard_verifier_vesta_member_constraint_deployed_terminal +native

-- The budgeted capstone and computed path (`Soundness.VestaBudget`): the derived deployed member
-- capstone with the run-quantified floors replaced by the joint accept floor, and the computed-path
-- endpoint with the member decode constructed and `hquot` derived — no extraction-data hypothesis.
assert_axioms deployed_member_node_binding_at_point_budgeted
assert_axioms orchard_verifier_vesta_member_constraint_budgeted +native
assert_axioms member_relation_or_dlr_of_instance_budgeted +native
assert_axioms member_snark_of_instance_budgeted +native
assert_axioms orchard_verifier_sound_vesta_budgeted +native
assert_axioms cleanOpening_provenance +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_budgeted +native
-- The `hfold` surface: the grouping's eval faithfulness at the vanishing slot is proven, not
-- assumed, so the derivation reads the verifier-computed `expectedHEval` off the routed member.
assert_axioms vanishing_query_mem_assembleQueries
assert_axioms assembleQueries_vanishingH_unique
assert_axioms constructIntermediateSets_unique_comm_routed
assert_axioms vanishing_slot_routed
assert_axioms hfold_of_expectedHEval_binding
assert_axioms hfold_of_vanishing_slot_binding
-- The root-of-unity exclusion is derived from acceptance (`assemble?` rejects at `xⁿ = 1`), and the
-- budget's good branch supplies `hbind` at the routed vanishing slot — so `hfold` now stands on the
-- fingerprint premise alone.
assert_axioms deployedAccepts_xn_ne_one
assert_axioms hfold_of_member_budget
-- The permutation and lookup arguments folded into the constraint model: the verifier's expression
-- list is the generic builder run on its own claimed evaluations, the same builder over column
-- polynomials evaluates back onto it, and the fold equation therefore needs no fingerprint premise.
assert_axioms permutationExpressions_map
assert_axioms lookupExpressions_map
assert_axioms subProofConstraints_map
assert_axioms allConstraints_map
assert_axioms subProofExpressions_eq
assert_axioms allExpressions_eq
assert_axioms eval_constraintPolys
assert_axioms eval_combineConstraints
assert_axioms eval_combineConstraints_deployed
assert_axioms hfold_of_constraint_polys
-- The permutation and lookup arguments closed from the verifier's own row checks: the combined
-- check splits into its parts, the running product telescopes across the rows, two challenge root
-- counts turn the product into a multiset identity, and the existing structural theorems turn that
-- into the copy constraints and the lookup inclusion.
assert_axioms constraints_dvd_of_good_y
assert_axioms telescope_running_product
assert_axioms grandProduct_eq_or_cell_eq_zero
assert_axioms multiset_pair_eq_of_prod_eval_eq
assert_axioms cellPairs_eq_of_running_product
assert_axioms perm_copy_constraints_of_running_product
assert_axioms lookup_multisets_of_prod_eval_eq
assert_axioms lookup_multisets_of_diff_eq_zero
assert_axioms lookup_subset_of_components
assert_axioms lookup_subset_of_prod_eval_eq
-- The deployed row reading: the step rule's folds are running products, the boundary rules pin the
-- product at the first and last rows, and the cell names separate. These are theorems about
-- `permChunkExpression` itself, so the chain above starts at the verifier's own constraint list.
assert_axioms permChunk_left_eq_prod
assert_axioms permChunk_right_eq_prod
assert_axioms permChunkExpression_eq
assert_axioms eval_eq_zero_of_dvd_vanishing
assert_axioms perm_row_recurrence
assert_axioms running_product_start
assert_axioms running_product_end
assert_axioms name_injective_of_coset
assert_axioms deployed_perm_copy_constraints
-- Locating a single rule inside the verifier's flat constraint list, fixing the permutation sets to
-- committed running products, and chaining the two: the copy constraints now follow from the
-- polynomial constraint identity itself, with no hypothesis about the shape of the checks.
assert_axioms permChunkExpression_mem_permutationExpressions
assert_axioms start_mem_permutationExpressions
assert_axioms end_mem_permutationExpressions
assert_axioms mem_subProofConstraints_of_mem_permutationExpressions
assert_axioms mem_allConstraints_of_mem_subProofConstraints
assert_axioms mem_constraintPolys_of_mem_permutationExpressions
assert_axioms head?_deployedPermSets
assert_axioms getLast?_deployedPermSets
assert_axioms deployed_copy_constraints_of_identity
-- The same for the lookup argument: its five rules located in the list, read row by row, and
-- chained to the inclusion.
assert_axioms lookupExpressions_eq
assert_axioms mem_subProofConstraints_of_mem_lookupExpressions
assert_axioms mem_constraintPolys_of_mem_lookupExpressions
assert_axioms running_product_end_flipped
assert_axioms lookup_row_recurrence
assert_axioms lookup_row_zero
assert_axioms lookup_row_step
assert_axioms lookup_rules_dvd_of_identity
assert_axioms deployed_lookup_subset_of_identity
assert_axioms deployed_lookup_relation_of_identity
-- Decompression: the θ-compressed membership becomes membership of whole rows, since the
-- compression is the fold polynomial of the row's values and a good θ separates distinct tuples.
assert_axioms foldPoly_sub
assert_axioms tuple_eq_of_foldPoly_eval_eq
assert_axioms compress_eval_eq_foldPoly
assert_axioms deployed_lookup_tuple_of_identity
-- Every new challenge surface priced the way `hgood` is: a uniform-challenge measure bound per
-- root-set event — the fold split's `y`, the bridge's `β` and `γ`, the vanishing-factor escapes,
-- and the decompression's pairwise `θ`. Sequential conditioning across the squeezes is the same
-- coupling hook `hgood` carries, documented with the `hfold`/`hgood` surfaces.
assert_axioms uniformChallenge_szBadSet_iUnion_le
assert_axioms goodY_failure_measure_le
assert_axioms perm_gamma_failure_measure_le
assert_axioms perm_beta_failure_measure_le
assert_axioms escape_measure_le
assert_axioms theta_failure_measure_le
-- The deployed capstone family over the full constraint system: the same witness chain — the batch
-- family's opening and the constructed member decodes — with the constraint check on the decoded
-- columns in place of the gate check, ending in `SnarkRelation` at `circuitSatViaConstraints`.
assert_axioms SnarkRelationWithMemberConstraints.toSnarkRelation
assert_axioms member_constraints_of_relation_and_batch
assert_axioms orchard_verifier_vesta_member_constraints_deployed_x4 +native
assert_axioms orchard_verifier_vesta_member_constraints_terminal +native
assert_axioms orchard_verifier_vesta_member_constraints_terminal_derived +native
-- The last links: the point check lifted to the polynomial identity, the permutation taken to be the
-- one keygen builds from the circuit's copy constraints, the cells of every chunk covered at once,
-- and circuit satisfaction defined by the whole constraint list rather than the gates alone.
assert_axioms constraint_identity_of_hfold
assert_axioms declared_equalities_of_running_product
assert_axioms deployed_declared_equalities_of_identity
assert_axioms prod_map_chunkCellPairs
assert_axioms perm_copy_constraints_of_chunk_products
assert_axioms chunkName_injective_of_coset
assert_axioms deployed_declared_equalities_of_identity_chunks
assert_axioms circuitSatViaConstraints_of_check
assert_axioms orchard_verifier_sound_vesta_constraints +native
-- Closing the loop: the capstone hands over an opening paired with satisfaction of the whole
-- constraint list, and the two arguments' relations are read back out of that same predicate.
assert_axioms snarkRelation_constraints
assert_axioms declared_equalities_of_circuitSat
assert_axioms lookup_relation_of_circuitSat
assert_axioms lookup_tuple_of_circuitSat
-- Several permutation chunks, not one: the chaining rule located in the list, read at row zero, and
-- the chunks flattened into a single running product so the permutation acts on every cell.
assert_axioms chain_mem_permutationExpressions
assert_axioms running_product_chain
assert_axioms deployed_copy_constraints_of_identity_chunks
assert_axioms hgood_failure_priced
assert_axioms hgood_of_good_challenge
-- The UNCONDITIONAL decomposition: `hExtract` removed, the residual quantified as the
-- clean-but-not-extracted measure term (bounded by the multiopen budget under the coupling
-- documented in `Composition.Decomposition`, not assumed here).
assert_axioms ComputedAlgebraicFSFamily.snarkExtractionFailureEvent_subset_union +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed +native
-- The forking reduction: the residual closed to the multiopen budget `t` by the fibered single-slot
-- counting bound, transported along the challenge-uniformity coupling. The coupling `hcouple` and the
-- accept containment `hcont` are the isolated non-circular premises (documented in `Composition.Residual`);
-- the reduction itself is proven.
assert_axioms fibered_accept_below_threshold_le
assert_axioms residual_le_of_coupling_containment
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_unconditional +native
-- The adaptive-coupling ladder (`Soundness.Composition.Assembly`): the residual bounded through the
-- honest random-oracle query loss instead of the over-idealised exact pushforward. Its two inputs
-- are the family `PeelDecode` and the honest-completeness containment `hcont`.
assert_axioms independentProductPMF_fiber_bound
assert_axioms residual_le_via_ladder +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder +native
-- The ladder at the concrete multiopen prefixes (`Soundness.Composition.Prefixes`): the four `x₁`–`x₄`
-- squeeze points, the decode's chain half discharged outright, and its state half reduced to the
-- level-0 factorisation of the accept event (`exists_multiopenStateAt_iff`, an iff — so the
-- factorisation is exactly the standing decode-side input, not a convenient sufficient condition).
assert_axioms multiopenPrefixReads_eq +native
assert_axioms multiopenLen_lt
assert_axioms multiopenChainAt_prefixes +native
assert_axioms multiopenLevelOf_prefixes +native
assert_axioms multiopenChainAt_ne
assert_axioms exists_multiopenStateAt_iff +native
assert_axioms multiopenPeelDecode_of_factors +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_multiopen +native
-- The honest-completeness half of `hcont` (`Soundness.Composition.Completeness`): the bad event priced
-- unconditionally, and the landing side reduced to the AGM-completeness supply, itself built from a
-- clean opening's forked transcript.
assert_axioms memberBadEvent_measure_le
assert_axioms memberBadEvent_of_supply
assert_axioms honestCompletenessSupply_of_forkedTranscript
assert_axioms forkedTranscript_nonempty_of_instanceOpening +native
assert_axioms honestCompletenessSupply_of_instanceOpening +native
-- The supply's own inputs, discharged: the three IPA fold challenges are exhibited in `Fp`, deployed
-- acceptance is reduced to the family's accept predicate, and the value shift is forced by the
-- witness tie. What is left in `honestCompletenessSupply_of_cleanOpening` is the tie itself.
assert_axioms exists_ipaFoldChallenges
assert_axioms deployedAccepts_of_verifierEq
assert_axioms honestCompletenessSupply_of_openings_agree +native
assert_axioms honestCompletenessSupply_of_cleanOpening +native
-- The witness tie is no longer a premise: the clean opening and the batch witness commit to the
-- same element, so either they agree (supply) or they collide (relation).
assert_axioms honestCompletenessSupply_or_relation +native
-- Acceptance through `assemble?`: the deployed decision excludes the verifier's rejection paths,
-- which `DeployedIpaVerifierEq` does not, so the supply carries no `assemble? = some m` premise.
assert_axioms fullAlgebraicAcceptDeployed +native
assert_axioms fullAlgebraicAccept_of_deployed +native
assert_axioms honestCompletenessSupply_of_cleanOpening_deployed +native
assert_axioms snarkExtractionFailureEventDeployed +native
assert_axioms snarkExtractionFailureEventDeployed_subset +native
assert_axioms snarkExtractionFailureEventDeployed_measure_le +native
-- The adaptive coupling (`Forking.AdaptiveCoupling`): escapes blind by overwriting rather than by
-- decoding, the per-level averaging bound, and the ladder logic separated from the weights.
assert_axioms updEsc
assert_axioms updEsc_blind
assert_axioms card_heavy_mul_le
assert_axioms updEsc_measure_le
assert_axioms updEsc_escapesDuringC_measure_le
assert_axioms adaptEsc
assert_axioms adapt_decomposition
assert_axioms adaptEsc_measure_le
