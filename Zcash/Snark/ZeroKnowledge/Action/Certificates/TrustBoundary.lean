import Zcash.Snark.ZeroKnowledge.ActionGateSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionGateTraceAgreement
import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceData
import Zcash.Snark.ZeroKnowledge.ActionWitnessSimulation
import Zcash.Snark.ZeroKnowledge.ActionProverCompleteness
import Zcash.Meta.AxiomCheck

/-!
# The certificate-dependent boundary of the Action development

These entries pin the declarations that depend on the evaluated source certificates: the gate
source certificate and the three modules of the advice source certificate. Those four modules
take between forty minutes and an hour each to elaborate, so their consumers are censused here
rather than in `Action/TrustBoundary.lean`, which reaches none of them and checks in seconds.
Everything an entry here depends on is otherwise pinned there.
-/

-- The evaluated source certificates: the advice source programs and the gate source labels.
assert_computable Zcash.Snark.ZeroKnowledge.actionAdviceSourcePrograms +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourcePrograms_eq +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourceCertificateRaw +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionAdviceSourceCertificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionGateSourceLabels +choice +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateSourceLabels_eq +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateSourceCertificateRaw +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGateActivationSourceCertificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateLabels_nodup +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceGateTrace_placed_eq_certificate +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

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
