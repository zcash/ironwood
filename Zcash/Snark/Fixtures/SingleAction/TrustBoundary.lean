import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Fixtures.SingleAction.StaticChecks
import Zcash.Snark.Soundness.Deployed.ActionVesta
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete fingerprint fixture

This module is built by CI (it belongs to the `FixtureCheck` lake target) and turns the trust boundary of
the concrete captured fingerprint into *checked*, build-time obligations. Besides the
coefficient-and-point match, the generated fixture validates every Vesta coordinate, binds the captured
transcript prefix to the canonical VK representation emitted by Rust, and computes both the captured and
Lean-assembled MSMs to the Vesta identity.

Both checks below follow Lean's elaborated dependency graph (via `Lean.collectAxioms`), so they see holes
anywhere in the transitive closure — including the `Soundness/` proof layer and Mathlib — which a
syntactic scan of the verifier sources cannot.

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier and so
  rejects `sorryAx` and any unexpected axiom, walking the whole dependency graph. Applied to every
  captured fixture (`+native` for the `native_decide` ones) and to `assemble` (the verifier assembly it
  runs).
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set each captured claim rests on, so
  a newly introduced axiom changes the set and fails the build. The
  pinned sets record `..._native.native_decide.ax_1_1`, the compiler-trust axiom that
  `native_decide` generates for each theorem (this Lean version emits a per-declaration native axiom rather
  than the global `Lean.ofReduceBool`): pinning it documents that the one place compiler trust enters is
  this concrete numeric fixture, never a general theorem. The other three (`propext`, `Classical.choice`,
  `Quot.sound`) are the standard classical-logic axioms every Mathlib development uses.

`instance_commitments_derived` and `capturedPublicInstances_within_lagrange` are pinned alongside
`fingerprint_matches`: they carry the *derivation* of the instance commitments from the captured public
inputs (ironwood#65), which is the trust this fixture buys in place of taking the commitments as opaque
captured points. The derivation's supporting data and functions (`capturedUrsGLagrange`,
`capturedPublicInstances`, `commitLagrange`, `derivedInstanceCommitment`) are bounded too, so the
`native_decide` claims cannot be narrowed by quietly widening what they range over.
-/

-- Every captured fixture and the verifier assembly it runs are bounded at the standard tier — no
-- `sorry`, no unexpected axiom (whole dependency graph). The `native_decide` fixtures carry the
-- compiler-trust axiom, permitted by `+native` and pinned exactly by the `#print axioms` guards below.
-- The static checks and degree budget at the single-Action captured key (issue #128):
-- the eleven decided facts the Action-level capstone's derived-key checks transfer through.
assert_axioms Zcash.Snark.Fixture.vk_advice_layout_length +native(Zcash.Snark.Fixture.vk_advice_layout_length)
assert_axioms Zcash.Snark.Fixture.vk_instance_layout_length +native(
  Zcash.Snark.Fixture.vk_instance_layout_length)
assert_axioms Zcash.Snark.Fixture.vk_fixed_layout_length +native(Zcash.Snark.Fixture.vk_fixed_layout_length)
assert_axioms Zcash.Snark.Fixture.vk_omega_order +native(Zcash.Snark.Fixture.vk_omega_order)
assert_axioms Zcash.Snark.Fixture.vk_n_cast_ne_zero +native(Zcash.Snark.Fixture.vk_n_cast_ne_zero)
assert_axioms Zcash.Snark.Fixture.vk_gates_degree_le +native(Zcash.Snark.Fixture.vk_gates_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_chunk_width_le +native(Zcash.Snark.Fixture.vk_chunk_width_le)
assert_axioms Zcash.Snark.Fixture.vk_lookup_input_degree_le +native(
  Zcash.Snark.Fixture.vk_lookup_input_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_lookup_table_degree_le +native(
  Zcash.Snark.Fixture.vk_lookup_table_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_quotient_tail_le +native(Zcash.Snark.Fixture.vk_quotient_tail_le)
assert_axioms Zcash.Snark.Fixture.vk_n_pred_le +native(Zcash.Snark.Fixture.vk_n_pred_le)
assert_axioms Zcash.Snark.Fixture.shape_k_pred_le +native(Zcash.Snark.Fixture.shape_k_pred_le)
assert_axioms Zcash.Snark.Fixture.fingerprint_matches +native(
  Zcash.Snark.Fixture.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture.capturedPointCoordinatesValid_eq_true +native(
  Zcash.Snark.Fixture.capturedPointCoordinatesValid_eq_true)
assert_axioms Zcash.Snark.Fixture.capturedInit_startsWith_vkTranscriptRepr +native(
  Zcash.Snark.Fixture.capturedInit_startsWith_vkTranscriptRepr)
assert_axioms Zcash.Snark.Fixture.capturedMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture.capturedMsm_eval_eq_zero)
assert_axioms Zcash.Snark.Fixture.assembledMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture.fingerprint_matches)
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms Zcash.Snark.assemble

-- The instance-commitment derivation: the two captured claims, plus the data and functions they
-- range over. The latter are flagless — they are ordinary definitions, so compiler trust must not
-- reach them; only the two claims about them may spend it.
assert_axioms Zcash.Snark.Fixture.instance_commitments_derived +native(
  Zcash.Snark.Fixture.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange +native(
  Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange)
assert_axioms Zcash.Snark.Fixture.capturedUrsGLagrange
assert_axioms Zcash.Snark.Fixture.capturedPublicInstances
assert_axioms Zcash.Snark.Fixture.commitLagrange
assert_axioms Zcash.Snark.Fixture.derivedInstanceCommitment

-- The keygen certificate and the deployed capstone live in the fixture lane because importing
-- them into the library-wide census would pull the large captured artifacts into `lake build
-- Zcash`. The certificate and its projections name the closed VK comparison together with every
-- concrete circuit fact on which that comparison depends.
assert_axioms Zcash.Snark.Keygen.certificate +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Keygen.shape_eq_mergeDerived +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Keygen.vk_eq_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Deployed.action_bundleStatement_or_relation_of_deployedAccepts +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil,
  Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil,
  Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture.fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture.fingerprint_matches

/-- info: 'Zcash.Snark.Fixture.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture.capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture.capturedMsm_eval_eq_zero

/-- info: 'Zcash.Snark.Fixture.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture.instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture.instance_commitments_derived

/-- info: 'Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange
