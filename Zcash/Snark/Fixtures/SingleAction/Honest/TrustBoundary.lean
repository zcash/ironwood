import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.SingleAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.SingleAction.Honest.StaticChecks
import Zcash.Snark.Fixtures.SingleAction.Honest.Negative
import Zcash.Snark.Fixtures.SingleAction.Honest.Negative.Sweep
import Zcash.Snark.Fixtures.SingleAction.Honest.Boundary
import Zcash.Meta.AxiomCheck
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the concrete fingerprint fixture

This module is built by CI (it belongs to the `FixtureCheck` lake target) and turns the trust boundary of
the concrete captured fingerprint into *checked*, build-time obligations. Besides the
coefficient-and-point match, the generated fixture validates every Vesta coordinate, binds the captured
transcript prefix to the canonical VK representation emitted by Rust, and computes both the captured and
Lean-assembled MSMs to the Vesta identity. Those identity evaluations are the family's non-vacuity
witness — a real accepting run of the pinned deployed verifier, which the random match-only captures
cannot provide — and the family's `vk`/`shape`/URS feed the deployed capstone lane
(`Capstones/Action.lean` with the `Circuits/Integration` terminals); the invariant
itself rides on the derived boundary statements (see `Fingerprint/Match.lean`).

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
inputs, which is the trust this fixture buys in place of taking the commitments as opaque
captured points. The derivation's supporting data and functions (`capturedUrsGLagrange`,
`capturedPublicInstances`, `commitLagrange`, `derivedInstanceCommitment`) are bounded too, so the
`native_decide` claims cannot be narrowed by quietly widening what they range over.
-/

-- Census the captured single-Action fixtures, including permitted native-code trust.
assert_axioms Zcash.Snark.Fixture.vk_advice_layout_length
assert_axioms Zcash.Snark.Fixture.vk_instance_layout_length
assert_axioms Zcash.Snark.Fixture.vk_fixed_layout_length
assert_axioms Zcash.Snark.Fixture.vk_omega_order +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.vk_n_cast_ne_zero
assert_axioms Zcash.Snark.Fixture.vk_gates_degree_le +native(Zcash.Snark.Fixture.vk_gates_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_chunk_width_le +native(Zcash.Snark.Fixture.vk_chunk_width_le)
assert_axioms Zcash.Snark.Fixture.vk_lookup_input_degree_le +native(
  Zcash.Snark.Fixture.vk_lookup_input_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_lookup_table_degree_le +native(
  Zcash.Snark.Fixture.vk_lookup_table_degree_le)
assert_axioms Zcash.Snark.Fixture.vk_quotient_tail_le
assert_axioms Zcash.Snark.Fixture.vk_n_pred_le
assert_axioms Zcash.Snark.Fixture.shape_k_pred_le
assert_axioms Zcash.Snark.Fixture.fingerprint_matches +native(
  Zcash.Snark.Fixture.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture.capturedPointCoordinatesValid_eq_true +native(
  Zcash.Snark.Fixture.capturedPointCoordinatesValid_eq_true)
assert_axioms Zcash.Snark.Fixture.capturedInit_startsWith_vkTranscriptRepr +native(
  Zcash.Snark.Fixture.capturedInit_startsWith_vkTranscriptRepr)
-- The statement-bound path must reproduce the captured VK/instance prefix, challenge schedule,
-- rejection-aware assembly, and final fingerprint.
assert_axioms Zcash.Snark.Fixture.capturedInit_eq_initialTranscript +native(
  Zcash.Snark.Fixture.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture.deriveChallengesForStatement_matches_captured_schedule +native(
  Zcash.Snark.Fixture.instance_commitments_derived,
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule)
assert_computable Zcash.Snark.Fixture.capturedRawInstances +choice
assert_axioms Zcash.Snark.Fixture.capturedRawInstances_have_expected_column_count
assert_axioms Zcash.Snark.Fixture.capturedRawInstances_columns_fit
assert_axioms Zcash.Snark.Fixture.capturedRawInstances_commitments_eq
assert_axioms Zcash.Snark.Fixture.capturedInstanceQueryLayout_eq
assert_axioms Zcash.Snark.Fixture.capturedRawInstances_commitments_eq_on_layout
assert_axioms Zcash.Snark.Fixture.assembleNonInteractiveInstances?_matches_captured +native(
  Zcash.Snark.Fixture.instance_commitments_derived,
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule)
assert_axioms Zcash.Snark.Fixture.nonInteractiveFingerprint_matches +native(
  Zcash.Snark.Fixture.instance_commitments_derived,
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture.capturedMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture.capturedMsm_eval_eq_zero)
assert_axioms Zcash.Snark.Fixture.assembledMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture.fingerprint_matches)
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms Zcash.Snark.assemble

-- The negative suite (`SingleAction/Negative.lean`): modeled rejection paths, schedule
-- sensitivity, and per-slot tamper sensitivity of the fingerprint match — including the blind
-- slots, whose honest values are recomputable from the key, publics, and challenges, so only
-- tamper sensitivity detects a sourcing error in `assemble` on honest captures.
assert_axioms Zcash.Snark.Fixture.valid_capture_assembles +native(
  Zcash.Snark.Fixture.valid_capture_assembles)
-- Acceptance joins successful assembly with zero MSM evaluation. The Vesta order certificate
-- supports the `evalNat`-to-`eval` bridge.
assert_axioms Zcash.Snark.Fixture.capture_deployedAccepts +native(
  Zcash.Snark.Fixture.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture.fingerprint_matches,
  Zcash.Snark.Fixture.valid_capture_assembles,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture.unexpected_last_permutation_eval_rejected +native(
  Zcash.Snark.Fixture.unexpected_last_permutation_eval_rejected)
assert_axioms Zcash.Snark.Fixture.missing_nonlast_permutation_eval_rejected +native(
  Zcash.Snark.Fixture.missing_nonlast_permutation_eval_rejected)
assert_axioms Zcash.Snark.Fixture.x_power_one_rejected +native(
  Zcash.Snark.Fixture.x_power_one_rejected)
assert_axioms Zcash.Snark.Fixture.x3_collision_rejected +native(
  Zcash.Snark.Fixture.x3_collision_rejected)
assert_axioms Zcash.Snark.Fixture.duplicate_advice_query_rejected +native(
  Zcash.Snark.Fixture.duplicate_advice_query_rejected)
assert_axioms Zcash.Snark.Fixture.tampered_advice_eval_assembles +native(
  Zcash.Snark.Fixture.tampered_advice_eval_assembles)
assert_axioms Zcash.Snark.Fixture.tampered_advice_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture.tampered_advice_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture.malformed_u_count_rejected +native(
  Zcash.Snark.Fixture.malformed_u_count_rejected)
assert_axioms Zcash.Snark.Fixture.swapped_lookup_permuted_breaks_schedule +native(
  Zcash.Snark.Fixture.swapped_lookup_permuted_breaks_schedule)
assert_axioms Zcash.Snark.Fixture.tampered_fixed_eval_assembles +native(
  Zcash.Snark.Fixture.tampered_fixed_eval_assembles)
assert_axioms Zcash.Snark.Fixture.tampered_fixed_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture.tampered_fixed_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture.tampered_permutation_common_eval_assembles +native(
  Zcash.Snark.Fixture.tampered_permutation_common_eval_assembles)
assert_axioms Zcash.Snark.Fixture.tampered_permutation_common_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture.tampered_permutation_common_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture.tampered_instance_eval_assembles +native(
  Zcash.Snark.Fixture.tampered_instance_eval_assembles)
assert_axioms Zcash.Snark.Fixture.tampered_instance_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture.tampered_instance_eval_fingerprint_mismatch)

-- The sensitivity sweep (`SingleAction/Negative/Sweep.lean`): one fingerprint-mismatch theorem per
-- `ProofString` field/axis and subfield, per challenge, and for the public inputs — complete
-- by construction against the `ProofString`/`Challenges` declarations, with `assembles`
-- pairs pinning the only rejection-capable challenge tampers (`x`, `x3`) to the MSM side.
-- The shared `mapAt`/`mapAt2` combinators the tampers range over are ordinary definitions,
-- censused flagless so compiler trust cannot reach them.
assert_axioms Zcash.Snark.Fixture.sweep_advice_commitments_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_advice_commitments_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_advice_commitments_last_column_mismatch +native(
  Zcash.Snark.Fixture.sweep_advice_commitments_last_column_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_permuted_input_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_permuted_input_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_permuted_input_last_lookup_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_permuted_input_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_permuted_table_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_permuted_table_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_permuted_table_last_lookup_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_permuted_table_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_product_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_product_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_product_last_set_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_product_last_set_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_product_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_product_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_product_last_lookup_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_product_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_vanishing_random_mismatch +native(
  Zcash.Snark.Fixture.sweep_vanishing_random_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_h_pieces_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_h_pieces_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_h_pieces_last_piece_mismatch +native(
  Zcash.Snark.Fixture.sweep_h_pieces_last_piece_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_instance_evals_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_instance_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_advice_evals_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_advice_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_advice_evals_last_query_mismatch +native(
  Zcash.Snark.Fixture.sweep_advice_evals_last_query_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_fixed_evals_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_fixed_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_fixed_evals_last_query_mismatch +native(
  Zcash.Snark.Fixture.sweep_fixed_evals_last_query_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_vanishing_random_eval_mismatch +native(
  Zcash.Snark.Fixture.sweep_vanishing_random_eval_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_common_evals_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_common_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_common_evals_last_column_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_common_evals_last_column_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_set_evals_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_set_evals_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_set_evals_eval_last_set_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_set_evals_eval_last_set_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_set_evals_next_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_set_evals_next_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_permutation_set_evals_last_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_permutation_set_evals_last_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_product_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_product_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_product_eval_last_lookup_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_product_eval_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_product_next_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_product_next_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_permuted_input_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_permuted_input_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_permuted_input_inv_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_permuted_input_inv_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_lookup_evals_permuted_table_eval_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_lookup_evals_permuted_table_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_multiopen_q_prime_mismatch +native(
  Zcash.Snark.Fixture.sweep_multiopen_q_prime_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_multiopen_u_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_multiopen_u_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_multiopen_u_last_point_set_mismatch +native(
  Zcash.Snark.Fixture.sweep_multiopen_u_last_point_set_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_s_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_s_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_rounds_l_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_rounds_l_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_rounds_l_last_round_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_rounds_l_last_round_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_rounds_r_first_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_rounds_r_first_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_c_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_c_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_f_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_f_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_theta_mismatch +native(
  Zcash.Snark.Fixture.sweep_theta_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_beta_mismatch +native(
  Zcash.Snark.Fixture.sweep_beta_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_gamma_mismatch +native(
  Zcash.Snark.Fixture.sweep_gamma_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_y_mismatch +native(
  Zcash.Snark.Fixture.sweep_y_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_x_assembles +native(
  Zcash.Snark.Fixture.sweep_x_assembles)
assert_axioms Zcash.Snark.Fixture.sweep_x_mismatch +native(
  Zcash.Snark.Fixture.sweep_x_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_x1_mismatch +native(
  Zcash.Snark.Fixture.sweep_x1_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_x2_mismatch +native(
  Zcash.Snark.Fixture.sweep_x2_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_x3_assembles +native(
  Zcash.Snark.Fixture.sweep_x3_assembles)
assert_axioms Zcash.Snark.Fixture.sweep_x3_mismatch +native(
  Zcash.Snark.Fixture.sweep_x3_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_x4_mismatch +native(
  Zcash.Snark.Fixture.sweep_x4_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_xi_mismatch +native(
  Zcash.Snark.Fixture.sweep_xi_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_z_mismatch +native(
  Zcash.Snark.Fixture.sweep_z_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_0_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_0_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_1_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_1_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_2_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_2_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_3_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_3_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_4_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_4_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_5_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_5_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_6_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_6_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_7_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_7_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_8_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_8_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_9_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_9_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_ipa_round_10_mismatch +native(
  Zcash.Snark.Fixture.sweep_ipa_round_10_mismatch)
assert_axioms Zcash.Snark.Fixture.sweep_public_input_mismatch +native(
  Zcash.Snark.Fixture.sweep_public_input_mismatch)
assert_axioms Zcash.Snark.mapAt
assert_axioms Zcash.Snark.mapAt2

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
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Keygen.actionShape_eq_fixtureShape +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Keygen.vk_eq_toVerifierKey +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
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
-- The Fiat–Shamir schedule checks, the composed fingerprint, and the boundary statements at the
-- Lean-derived key (`Boundary.lean`). The oracle/schedule data and the composed-statement
-- functions are flagless — compiler trust may enter only through the named claims — except
-- `derivedVk`, whose circuit argument itself carries the natively-certified fixed-base
-- facts.
assert_axioms Zcash.Snark.Fixture.capturedChallengeValues_eq_expected +native(
  Zcash.Snark.Fixture.capturedChallengeValues_eq_expected)
assert_axioms Zcash.Snark.Fixture.missingChallenge_not_captured +native(
  Zcash.Snark.Fixture.missingChallenge_not_captured)
assert_axioms Zcash.Snark.Fixture.capturedChallengeValues_nodup +native(
  Zcash.Snark.Fixture.capturedChallengeValues_nodup)
assert_axioms Zcash.Snark.Fixture.capturedScheduleIncludesInit_eq_true +native(
  Zcash.Snark.Fixture.capturedScheduleIncludesInit_eq_true)
assert_axioms Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule +native(
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule)
assert_axioms Zcash.Snark.Fixture.nonInteractiveFingerprint_matches +native(
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture.fingerprint_matches,
  Zcash.Snark.Fixture.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture.capturedFs
assert_axioms Zcash.Snark.Fixture.capturedInit
assert_axioms Zcash.Snark.deriveChallenges
assert_axioms Zcash.Snark.nonInteractiveFingerprint
assert_axioms Zcash.Snark.Fixture.derivedVk +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.nonInteractiveFingerprint_matches_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero,
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture.fingerprint_matches,
  Zcash.Snark.Fixture.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture.nonInteractiveFingerprint_matches_derived_inputs +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.Keygen.instanceCommitment_capturedActionInputs,
  Zcash.Snark.Keygen.publicInputRows_capturedActionInputs,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero,
  Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture.fingerprint_matches,
  Zcash.Snark.Fixture.instance_commitments_derived)

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

/-- info: 'Zcash.Snark.Fixture.nonInteractiveFingerprint_matches_derived' depends on axioms: [propext,
Classical.choice,
Quot.sound,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_1,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_2,
Zcash.Snark.Fixture.deriveChallenges_matches_captured_schedule._native.native_decide.ax_1_1,
Zcash.Snark.Fixture.fingerprint_matches._native.native_decide.ax_1_1,
Zcash.Snark.Fixture.instance_commitments_derived._native.native_decide.ax_1_1,
Zcash.Snark.Keygen.certificate._native.native_decide.ax_1_1,
CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_2,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_3,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_4,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_5,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_6,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_7,
Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero._native.native_decide.ax_1_8,
Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_1,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_2,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_3,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_4,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_5,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_6,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_7,
Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero._native.native_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture.nonInteractiveFingerprint_matches_derived
