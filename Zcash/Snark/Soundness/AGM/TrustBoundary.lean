import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Mathlib.Util.AssertNoSorry

/-!
# AGM trust-boundary checks

The definitions below compute representations, openings, or DL relations. They remain plain `def`s`,
so they cannot select data with `Classical.choice`. `assert_no_sorry` and the guarded reports check
their proof dependencies.
-/

open Zcash.Snark

assert_no_sorry discreteLogOfBasis_of_relation
assert_no_sorry DLChallengeGame.solveFromRelation
assert_no_sorry fixedSlotExtractOrMiss
assert_no_sorry AugmentedRelationWitness.toAlgebraicRelationWitness
assert_no_sorry relationWitnessOfCollision
assert_no_sorry discreteLogOfAugmentedRelationAtChallenge
assert_no_sorry separateOrRelationWitness
assert_no_sorry relationOfFoldGensWitness
assert_no_sorry deployedLeafPeelWitness
assert_no_sorry deployedToAcceptVWitness
assert_no_sorry algebraicRelationOfDeployedAccept
assert_no_sorry AlgebraicProver.toProver
assert_no_sorry AlgebraicDForkCert.toDForkCert
assert_no_sorry algebraicProverAccept_forkValid
assert_no_sorry deployedAlgebraicForkingRelation
assert_no_sorry deployedAlgebraicForkingFixedSlot
assert_no_sorry DeployedAlgebraicForkingInstance.run
assert_no_sorry DeployedAlgebraicForkingInstance.ProducesRelation
assert_no_sorry deployedAlgebraicRelationProduced
assert_no_sorry deployedAlgebraicRelationEvent
assert_no_sorry deployedAlgebraicRelationFinder
assert_no_sorry deployedAlgebraicRelationFinder_isSome_iff
assert_no_sorry deployedAlgebraicRelation
assert_no_sorry deployedAlgebraicRelationWitness
assert_no_sorry orchardDeployedAlgebraicForkingFixedSlot
assert_no_sorry orchardDeployedRelationSet
assert_no_sorry OrchardUniformURSIdentification
assert_no_sorry orchardGeneratorROSetup
assert_no_sorry orchardGeneratorROBasis
assert_no_sorry orchard_uniformURSIdentification_of_generatorRO
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog

/-- info: 'Zcash.Snark.discreteLogOfBasis_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfBasis_of_relation

/-- info: 'Zcash.Snark.DLChallengeGame.solveFromRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLChallengeGame.solveFromRelation

/-- info: 'Zcash.Snark.fixedSlotExtractOrMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSlotExtractOrMiss

/-- info: 'Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AugmentedRelationWitness.toAlgebraicRelationWitness

/-- info: 'Zcash.Snark.relationWitnessOfCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationWitnessOfCollision

/-- info: 'Zcash.Snark.discreteLogOfAugmentedRelationAtChallenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfAugmentedRelationAtChallenge

/-- info: 'Zcash.Snark.separateOrRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separateOrRelationWitness

/-- info: 'Zcash.Snark.relationOfFoldGensWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationOfFoldGensWitness

/-- info: 'Zcash.Snark.deployedLeafPeelWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedLeafPeelWitness

/-- info: 'Zcash.Snark.deployedToAcceptVWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedToAcceptVWitness

/-- info: 'Zcash.Snark.algebraicRelationOfDeployedAccept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraicRelationOfDeployedAccept

/-- info: 'Zcash.Snark.deployedAlgebraicForkingRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingRelation

/-- info: 'Zcash.Snark.deployedAlgebraicForkingFixedSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingFixedSlot

/-- info: 'Zcash.Snark.deployedAlgebraicRelationFinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationFinder

/-- info: 'Zcash.Snark.deployedAlgebraicRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelation

/-- info: 'Zcash.Snark.deployedAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog

/-! The probability layer contains theorems rather than data-producing definitions. The checks below
pin its proof dependencies. -/

assert_no_sorry hitProb_ge_inv_card
assert_no_sorry relSet_card_le_succSet_card
assert_no_sorry reduction_advantage_ge
assert_no_sorry relation_prob_le_of_DL
assert_no_sorry winSet_card
assert_no_sorry textbook_winProb_eq_succProb
assert_no_sorry relation_prob_le_of_textbookDL
assert_no_sorry orchard_relation_prob_le_of_DL
assert_no_sorry orchard_reduction_advantage_ge
assert_no_sorry orchard_relation_prob_le_of_textbookDL
assert_no_sorry commitment_binding_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_reduction_advantage_ge
assert_no_sorry orchard_deployed_relation_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_set_eq_relSet
assert_no_sorry orchard_deployed_relation_event_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_prob_eq_of_uniformURS
assert_no_sorry orchard_deployed_relation_prob_le_of_uniformURS_textbookDL
assert_no_sorry orchard_deployed_relation_prob_le_of_generatorRO_textbookDL

/-- info: 'Zcash.Snark.relation_prob_le_of_textbookDL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relation_prob_le_of_textbookDL

/-! The Vesta endpoints also depend on CompElliptic's `native_decide` point-count axiom through the
`Module Fp VestaG` instance. The checks below record that extra dependency. -/

/-- info: 'Zcash.Snark.orchard_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.commitment_binding_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms commitment_binding_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_uniformURS_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_uniformURSIdentification_of_generatorRO

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_generatorRO_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_generatorRO_textbookDL
