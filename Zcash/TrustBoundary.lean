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
