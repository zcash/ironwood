import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.MultiAction.Honest.Degree
import Zcash.Snark.Fixtures.MultiAction.Honest.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Honest.Schedule
import Zcash.Snark.Fixtures.MultiAction.Honest.Negative
import Zcash.Snark.Fixtures.MultiAction.Honest.Negative.Sweep
import Zcash.Snark.Fixtures.MultiAction.Honest.StraightLineKnowledgeError
import Zcash.Snark.Fixtures.MultiAction.Honest.CapturedZeroFamily
import Zcash.Snark.Capstones.Action
import Zcash.Snark.Fixtures.MultiAction.Honest.Boundary
import Zcash.Snark.Fixtures.PostNu63
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.Honest.TrustBoundary`, and checked the same way: CI
bounds the trusted base of the concrete coordinate validation, verifier fingerprint match, executable
Vesta MSM identity, and instance-commitment derivation, and pins the exact axiom set of the
`native_decide` claims among them. The MSM identity facts are this family's non-vacuity witness — a
real accepting two-action run of the pinned deployed verifier, which the random match-only captures
cannot provide; the invariant itself rides on the derived boundary statements (see
`Fingerprint/Match.lean`).

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier,
  rejecting `sorryAx` and any unexpected axiom, walking the whole elaborated dependency graph
  (`Lean.collectAxioms`) rather than a syntactic scan. `+native` on the captured fixtures that run
  through `native_decide`.
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set, so a newly introduced
  axiom fails the build. As in the single-action sibling, this is the case the pinned form is
  reserved for: for a concrete numeric fixture the exact axiom set *is* the claim, documenting that
  compiler trust enters here and nowhere else.

The instance-commitment derivation (`instance_commitments_derived`,
`capturedPublicInstances_within_lagrange`) is pinned on the same footing, together with the data and
functions it ranges over; see the single-action sibling for why this is the fixture's new trust
surface.

The retained AGM capstones include the straight-line endpoint and the adaptive-statement knowledge
endpoints.  Their representations are ghost extractor data: they are neither transmitted nor
checked by the Halo2 verifier.  Accordingly the endpoints are AGM-and-random-oracle results under
the supplied finite-security Vesta DLOG profiles.  The adaptive-statement profile conservatively
charges its four short-circuiting finder stages and one additional extraction traversal.  The
adversary's group work and the complete reduction postprocessing work remain explicit bounded
profile inputs; only the named assembly/basis sub-budget is operationally derived here.
-/

assert_axioms Zcash.Snark.Fixture2.capturedPointCoordinatesValid_eq_true +native(
  Zcash.Snark.Fixture2.capturedPointCoordinatesValid_eq_true)
assert_axioms Zcash.Snark.Fixture2.capturedInit_startsWith_vkTranscriptRepr +native(
  Zcash.Snark.Fixture2.capturedInit_startsWith_vkTranscriptRepr)
-- The statement-bound path must reproduce the captured VK/instance prefix, challenge schedule,
-- rejection-aware assembly, and final fingerprint.
assert_axioms Zcash.Snark.Fixture2.capturedInit_eq_initialTranscript +native(
  Zcash.Snark.Fixture2.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture2.deriveChallengesForStatement_matches_captured_schedule +native(
  Zcash.Snark.Fixture2.instance_commitments_derived,
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule)
assert_computable Zcash.Snark.Fixture2.capturedRawInstances +choice
assert_axioms Zcash.Snark.Fixture2.capturedRawInstances_have_expected_column_count
assert_axioms Zcash.Snark.Fixture2.capturedRawInstances_columns_fit
assert_axioms Zcash.Snark.Fixture2.capturedRawInstances_commitments_eq
assert_axioms Zcash.Snark.Fixture2.capturedInstanceQueryLayout_eq
assert_axioms Zcash.Snark.Fixture2.capturedRawInstances_commitments_eq_on_layout
assert_axioms Zcash.Snark.Fixture2.assembleNonInteractiveInstances?_matches_captured +native(
  Zcash.Snark.Fixture2.instance_commitments_derived,
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule)
assert_axioms Zcash.Snark.Fixture2.nonInteractiveFingerprint_matches +native(
  Zcash.Snark.Fixture2.instance_commitments_derived,
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture2.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture2.fingerprint_matches +native(
  Zcash.Snark.Fixture2.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero)
assert_axioms Zcash.Snark.Fixture2.assembledMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture2.fingerprint_matches)
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms Zcash.Snark.assemble

-- The negative suite (`MultiAction/Negative.lean`): modeled rejection paths, schedule
-- sensitivity, and per-slot tamper sensitivity of the fingerprint match — including the blind
-- slots, whose honest values are recomputable from the key, publics, and challenges, so only
-- tamper sensitivity detects a sourcing error in `assemble` on honest captures.
assert_axioms Zcash.Snark.Fixture2.valid_capture_assembles +native(
  Zcash.Snark.Fixture2.valid_capture_assembles)
-- Acceptance joins successful assembly with zero MSM evaluation. The Vesta order certificate
-- supports the `evalNat`-to-`eval` bridge.
assert_axioms Zcash.Snark.Fixture2.capture_deployedAccepts +native(
  Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture2.fingerprint_matches,
  Zcash.Snark.Fixture2.valid_capture_assembles,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.unexpected_last_permutation_eval_rejected +native(
  Zcash.Snark.Fixture2.unexpected_last_permutation_eval_rejected)
assert_axioms Zcash.Snark.Fixture2.missing_nonlast_permutation_eval_rejected +native(
  Zcash.Snark.Fixture2.missing_nonlast_permutation_eval_rejected)
assert_axioms Zcash.Snark.Fixture2.x_power_one_rejected +native(
  Zcash.Snark.Fixture2.x_power_one_rejected)
assert_axioms Zcash.Snark.Fixture2.x3_collision_rejected +native(
  Zcash.Snark.Fixture2.x3_collision_rejected)
assert_axioms Zcash.Snark.Fixture2.duplicate_advice_query_rejected +native(
  Zcash.Snark.Fixture2.duplicate_advice_query_rejected)
assert_axioms Zcash.Snark.Fixture2.tampered_advice_eval_assembles +native(
  Zcash.Snark.Fixture2.tampered_advice_eval_assembles)
assert_axioms Zcash.Snark.Fixture2.tampered_advice_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture2.tampered_advice_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture2.malformed_u_count_rejected +native(
  Zcash.Snark.Fixture2.malformed_u_count_rejected)
assert_axioms Zcash.Snark.Fixture2.swapped_advice_absorb_breaks_schedule +native(
  Zcash.Snark.Fixture2.swapped_advice_absorb_breaks_schedule)
assert_axioms Zcash.Snark.Fixture2.swapped_lookup_permuted_breaks_schedule +native(
  Zcash.Snark.Fixture2.swapped_lookup_permuted_breaks_schedule)
assert_axioms Zcash.Snark.Fixture2.swapped_sub_proofs_assemble +native(
  Zcash.Snark.Fixture2.swapped_sub_proofs_assemble)
assert_axioms Zcash.Snark.Fixture2.swapped_sub_proofs_fingerprint_mismatch +native(
  Zcash.Snark.Fixture2.swapped_sub_proofs_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture2.tampered_fixed_eval_assembles +native(
  Zcash.Snark.Fixture2.tampered_fixed_eval_assembles)
assert_axioms Zcash.Snark.Fixture2.tampered_fixed_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture2.tampered_fixed_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture2.tampered_permutation_common_eval_assembles +native(
  Zcash.Snark.Fixture2.tampered_permutation_common_eval_assembles)
assert_axioms Zcash.Snark.Fixture2.tampered_permutation_common_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture2.tampered_permutation_common_eval_fingerprint_mismatch)
assert_axioms Zcash.Snark.Fixture2.tampered_instance_eval_assembles +native(
  Zcash.Snark.Fixture2.tampered_instance_eval_assembles)
assert_axioms Zcash.Snark.Fixture2.tampered_instance_eval_fingerprint_mismatch +native(
  Zcash.Snark.Fixture2.tampered_instance_eval_fingerprint_mismatch)

-- The sensitivity sweep (`MultiAction/Negative/Sweep.lean`): one fingerprint-mismatch theorem per
-- `ProofString` field/axis and subfield, per challenge, and for the public inputs — complete
-- by construction against the `ProofString`/`Challenges` declarations, with `assembles`
-- pairs pinning the only rejection-capable challenge tampers (`x`, `x3`) to the MSM side.
-- The shared `mapAt`/`mapAt2` combinators the tampers range over are ordinary definitions,
-- censused flagless so compiler trust cannot reach them.
assert_axioms Zcash.Snark.Fixture2.sweep_advice_commitments_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_commitments_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_advice_commitments_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_commitments_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_advice_commitments_last_column_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_commitments_last_column_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_input_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_input_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_input_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_input_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_input_last_lookup_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_input_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_table_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_table_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_table_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_table_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_permuted_table_last_lookup_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_permuted_table_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_product_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_product_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_product_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_product_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_product_last_set_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_product_last_set_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_product_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_product_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_product_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_product_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_product_last_lookup_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_product_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_vanishing_random_mismatch +native(
  Zcash.Snark.Fixture2.sweep_vanishing_random_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_h_pieces_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_h_pieces_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_h_pieces_last_piece_mismatch +native(
  Zcash.Snark.Fixture2.sweep_h_pieces_last_piece_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_instance_evals_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_instance_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_instance_evals_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_instance_evals_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_advice_evals_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_advice_evals_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_evals_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_advice_evals_last_query_mismatch +native(
  Zcash.Snark.Fixture2.sweep_advice_evals_last_query_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_fixed_evals_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_fixed_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_fixed_evals_last_query_mismatch +native(
  Zcash.Snark.Fixture2.sweep_fixed_evals_last_query_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_vanishing_random_eval_mismatch +native(
  Zcash.Snark.Fixture2.sweep_vanishing_random_eval_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_common_evals_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_common_evals_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_common_evals_last_column_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_common_evals_last_column_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_last_set_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_set_evals_eval_last_set_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_set_evals_next_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_set_evals_next_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_permutation_set_evals_last_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_permutation_set_evals_last_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_last_proof_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_last_proof_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_last_lookup_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_product_eval_last_lookup_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_product_next_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_product_next_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_input_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_input_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_input_inv_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_input_inv_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_table_eval_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_lookup_evals_permuted_table_eval_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_multiopen_q_prime_mismatch +native(
  Zcash.Snark.Fixture2.sweep_multiopen_q_prime_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_multiopen_u_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_multiopen_u_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_multiopen_u_last_point_set_mismatch +native(
  Zcash.Snark.Fixture2.sweep_multiopen_u_last_point_set_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_s_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_s_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_rounds_l_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_rounds_l_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_rounds_l_last_round_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_rounds_l_last_round_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_rounds_r_first_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_rounds_r_first_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_c_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_c_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_f_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_f_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_theta_mismatch +native(
  Zcash.Snark.Fixture2.sweep_theta_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_beta_mismatch +native(
  Zcash.Snark.Fixture2.sweep_beta_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_gamma_mismatch +native(
  Zcash.Snark.Fixture2.sweep_gamma_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_y_mismatch +native(
  Zcash.Snark.Fixture2.sweep_y_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_x_assembles +native(
  Zcash.Snark.Fixture2.sweep_x_assembles)
assert_axioms Zcash.Snark.Fixture2.sweep_x_mismatch +native(
  Zcash.Snark.Fixture2.sweep_x_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_x1_mismatch +native(
  Zcash.Snark.Fixture2.sweep_x1_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_x2_mismatch +native(
  Zcash.Snark.Fixture2.sweep_x2_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_x3_assembles +native(
  Zcash.Snark.Fixture2.sweep_x3_assembles)
assert_axioms Zcash.Snark.Fixture2.sweep_x3_mismatch +native(
  Zcash.Snark.Fixture2.sweep_x3_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_x4_mismatch +native(
  Zcash.Snark.Fixture2.sweep_x4_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_xi_mismatch +native(
  Zcash.Snark.Fixture2.sweep_xi_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_z_mismatch +native(
  Zcash.Snark.Fixture2.sweep_z_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_0_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_0_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_1_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_1_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_2_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_2_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_3_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_3_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_4_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_4_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_5_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_5_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_6_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_6_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_7_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_7_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_8_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_8_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_9_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_9_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_ipa_round_10_mismatch +native(
  Zcash.Snark.Fixture2.sweep_ipa_round_10_mismatch)
assert_axioms Zcash.Snark.Fixture2.sweep_public_input_mismatch +native(
  Zcash.Snark.Fixture2.sweep_public_input_mismatch)
assert_axioms Zcash.Snark.mapAt
assert_axioms Zcash.Snark.mapAt2

-- The captured key's degree budget: one literal (`20470`) dominates every constraint family,
-- so the `x`-squeeze schedule's `epsilonX` is the concrete `20470 / |𝔽|` at this key.
assert_axioms Zcash.Snark.Fixture2.vk_gates_degree_le +native(
  Zcash.Snark.Fixture2.vk_gates_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_chunk_width_le +native(
  Zcash.Snark.Fixture2.vk_chunk_width_le)
assert_axioms Zcash.Snark.Fixture2.vk_lookup_input_degree_le +native(
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_lookup_table_degree_le +native(
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_quotient_tail_le +native(
  Zcash.Snark.Fixture2.vk_quotient_tail_le)
assert_axioms Zcash.Snark.Fixture2.vk_n_pred_le +native(Zcash.Snark.Fixture2.vk_n_pred_le)
assert_axioms Zcash.Snark.Fixture2.shape_k_pred_le +native(Zcash.Snark.Fixture2.shape_k_pred_le)
-- The captured key's static checks: the query layouts cover the shape's counts, `ω` has order
-- dividing `n`, and `n` does not vanish in `𝔽` — packaged for any family carrying the
-- captured non-group profile. Literal equality of fixed Vesta commitments is intentionally absent.
assert_axioms Zcash.Snark.Fixture2.capturedVerifierKeyProfile_vk
assert_axioms Zcash.Snark.Fixture2.vk_advice_layout_length +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_instance_layout_length +native(
  Zcash.Snark.Fixture2.vk_instance_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_fixed_layout_length +native(
  Zcash.Snark.Fixture2.vk_fixed_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_omega_order +native(Zcash.Snark.Fixture2.vk_omega_order)
assert_axioms Zcash.Snark.Fixture2.vk_n_cast_ne_zero +native(
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero)
assert_axioms Zcash.Snark.Fixture2.deployedConstraintStaticChecks_of_captured +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_omega_order,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The `x`-squeeze schedule at the captured key: the degree caps are discharged, so `epsilonX` is
-- the concrete `20470 / |𝔽|`; exact leave-one-`x` invariance follows from the family's
-- fresh-query constraint trace.
assert_axioms Zcash.Snark.Fixture2.deployedConstraintXSqueezeSchedule_captured +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The deployed compressed-identity extraction bound at the captured key: the straight-line
-- capstone with the static checks and degree caps discharged, so the bad-`x` term is the concrete
-- `(Q + 1) · 20470 / |𝔽|` and the multiopen term is the additive root budget.  Semantic circuit
-- satisfaction additionally uses the four-budget promotion in the core trust census.
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_straightline_captured_knowledge_error_bound +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_omega_order,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_straightline_captured_generatorRO_knowledge_error_bound +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_omega_order,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The same bound on the interpolation-free route: the deployed constraint family is built by
-- `ofCovered` from the two fresh-query traces, with no field-capacity premise or interpolation.
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_straightline_captured_direct_generatorRO_knowledge_error_bound +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_omega_order,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Census the captured and consensus-generic Action capstones with their fixtures.
-- These public Capstone helper leaves are not protocol endpoints, but nothing else depends on
-- them, so transitive endpoint pins cannot bound their trusted bases.  Keep each one directly
-- censused rather than relying on the endpoint name regex to classify internal public claims.
assert_axioms Zcash.Snark.Capstone.actionProofShape_eq_maxShape +native(
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
assert_axioms Zcash.Snark.Capstone.actionStaticChecks +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.capturedActionThetaBudget +native(
  Zcash.Snark.Capstone.actionLookupActivationCount_le,
  Zcash.Snark.Capstone.actionLookupInputArity_le,
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
assert_axioms Zcash.Snark.Capstone.capturedActionBetaBudget +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Capstone.resolverPermutationCell_card_eq,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.capturedActionGammaBudget +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Capstone.resolverPermutationCell_card_eq,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.capturedActionYBudget +native(
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
assert_axioms Zcash.Snark.Capstone.capturedActionConstraintCount_bound +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.actionConstraintCount_bound +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.adaptiveActionXDegree_bound +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.actionStatisticalModel_at_2pow123 +native(
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
assert_axioms Zcash.Snark.Capstone.actionDlogOracleQueryCost_bound +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.actionDlogGroupWork_bound
assert_axioms Zcash.Snark.Capstone.action_semantic_count_le
assert_axioms Zcash.Snark.Capstone.two_pow_254_le_card
assert_axioms Zcash.Snark.Capstone.action_semantic_terms_le
assert_axioms Zcash.Snark.Capstone.derived_scalars +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.derived_lookups +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The shared five-surface probability bound the two Action endpoints are built from. It is a
-- per-challenge measure rather than a protocol capstone; the pin is what the `_probability_bound`
-- suffix rule demands, not an independent claim.

assert_axioms Zcash.Snark.Capstone.capturedActionStaticChecks +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.capturedActionXSqueezeSchedule +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)

-- The per-surface bound the adaptive-statement capstones consume. Its `_for` form takes the
-- bundle size as a parameter; the census pattern reaches it for the same reason it reaches the
-- other `_measure_le` surfaces, not as an independent claim. Like the captured `x`-schedule
-- above it prices against the captured key, so it carries the derived key's certificate and the
-- degree caps read off it, plus the two lookup-shape and permutation-cell counts the surfaces
-- are evaluated at.
assert_axioms Zcash.Snark.Capstone.orchard_adaptiveActionStatementSurface_measure_le_for +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.Capstone.actionLookupActivationCount_le,
  Zcash.Snark.Capstone.actionLookupInputArity_le,
  Zcash.Snark.Capstone.resolverPermutationCell_card_eq,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)

-- Adaptive-statement knowledge soundness binds the statement-selected instance prefix before
-- `theta` and conservatively charges every stage of the combined finder.
assert_axioms Zcash.Snark.Capstone.orchard_action_knowledgeFailure_prob_le_adaptiveStatement_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  Zcash.Snark.ActionPermutationDomain.numInstanceColumns_eq,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.adviceQueryColumnsAllocated,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  Zcash.Snark.ActionPermutationDomain.instanceQueryLayout_columns_lt,
  Zcash.Snark.Capstone.actionLookupActivationCount_le,
  Zcash.Snark.Capstone.actionLookupInputArity_le,
  Zcash.Snark.Capstone.resolverPermutationCell_card_eq,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Capstone.orchard_action_knowledgeFailure_adaptiveStatement_2pow123_workFactor_generatorRO_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  Zcash.Snark.ActionPermutationDomain.numInstanceColumns_eq,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.adviceQueryColumnsAllocated,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  Zcash.Snark.ActionPermutationDomain.instanceQueryLayout_columns_lt,
  Zcash.Snark.Capstone.actionLookupActivationCount_le,
  Zcash.Snark.Capstone.actionLookupInputArity_le,
  Zcash.Snark.Capstone.resolverPermutationCell_card_eq,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The unpriced-resource form of the adaptive knowledge-failure bound.

-- Its consensus-generic form.

-- The instance-commitment derivation: the two captured claims, plus the data and functions they
-- range over. The latter are flagless — they are ordinary definitions, so compiler trust must not
-- reach them; only the two claims about them may spend it.
assert_axioms Zcash.Snark.Fixture2.instance_commitments_derived +native(
  Zcash.Snark.Fixture2.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange +native(
  Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange)
assert_axioms Zcash.Snark.Fixture2.capturedUrsGLagrange
assert_axioms Zcash.Snark.Fixture2.capturedPublicInstances
assert_axioms Zcash.Snark.Fixture2.commitLagrange
assert_axioms Zcash.Snark.Fixture2.derivedInstanceCommitment

-- Cross-capture provenance (`Fixtures/PostNu63.lean`): the point-level equalities that transport
-- the single-action keygen certificate to this capture, and the URS record equality assembled
-- from them.
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_ursG +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursG)
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_wu +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_wu)
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_ursGLagrange +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursGLagrange)
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments)
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments)
assert_axioms Zcash.Snark.PostNu63Fixture.captures_use_same_urs +native(
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursG,
  Zcash.Snark.PostNu63Fixture.captures_use_same_wu)

-- The transported keygen certificate (`VkCertificate.lean`): the multi-action key equals its
-- end-to-end derivation. Owners are the single-action certificate's plus the cross-capture
-- point equalities — no second keygen evaluation.
assert_axioms Zcash.Snark.Fixture2.vk_eq_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursG,
  Zcash.Snark.PostNu63Fixture.captures_use_same_wu,
  Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments,
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
assert_axioms Zcash.Snark.Fixture2.vk_eq_toVerifierKey +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursG,
  Zcash.Snark.PostNu63Fixture.captures_use_same_wu,
  Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments,
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

-- The Fiat–Shamir schedule checks, the composed fingerprint, and the boundary statement at the
-- Lean-derived key (`Boundary.lean`). The oracle/schedule data and the composed-statement
-- functions are flagless — compiler trust may enter only through the named claims — except
-- `derivedVk`, whose circuit argument itself carries the natively-certified fixed-base
-- facts.
assert_axioms Zcash.Snark.Fixture2.capturedChallengeValues_eq_expected +native(
  Zcash.Snark.Fixture2.capturedChallengeValues_eq_expected)
assert_axioms Zcash.Snark.Fixture2.missingChallenge_not_captured +native(
  Zcash.Snark.Fixture2.missingChallenge_not_captured)
assert_axioms Zcash.Snark.Fixture2.capturedChallengeValues_nodup +native(
  Zcash.Snark.Fixture2.capturedChallengeValues_nodup)
assert_axioms Zcash.Snark.Fixture2.capturedScheduleIncludesInit_eq_true +native(
  Zcash.Snark.Fixture2.capturedScheduleIncludesInit_eq_true)
assert_axioms Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule +native(
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule)
assert_axioms Zcash.Snark.Fixture2.nonInteractiveFingerprint_matches +native(
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture2.fingerprint_matches,
  Zcash.Snark.Fixture2.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture2.capturedFs
assert_axioms Zcash.Snark.Fixture2.capturedInit
assert_axioms Zcash.Snark.deriveChallenges
assert_axioms Zcash.Snark.nonInteractiveFingerprint
assert_axioms Zcash.Snark.Fixture2.derivedVk +native(
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
assert_axioms Zcash.Snark.Fixture2.nonInteractiveFingerprint_matches_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.captures_use_same_ursG,
  Zcash.Snark.PostNu63Fixture.captures_use_same_wu,
  Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments,
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
  Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.Fixture2.fingerprint_matches,
  Zcash.Snark.Fixture2.instance_commitments_derived)

-- The captured key's zero-family test with eleven live IPA rounds
-- (`MultiAction/CapturedZeroFamily`): this exercises the interface at the captured scalar
-- metadata, layouts, and domain rather than only at the round-free witness shape.  It is not the
-- deployed adapter above: its group commitment families are zero and its shape is instance-free,
-- which is what makes the constraint-`x` stage discharge.
-- The key data itself stays executable; the families above it are noncomputable only because a
-- root set is a `szBadSet` of a polynomial, so they are censused for their axiom base instead.
assert_computable Zcash.Snark.Fixture2.capturedZeroVk +choice
assert_axioms Zcash.Snark.Fixture2.capturedZeroStraightLineFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedZeroDeployedConstraintFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedZeroStaticChecks +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length, Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_instance_layout_length, Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_omega_order, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedZeroConstraintSchedule +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The live-instance layers at the full captured shape: the root and IPA layers run with both
-- sub-proofs; the constraint-x stage is the honest-prover boundary and is deliberately absent.
assert_computable Zcash.Snark.Fixture2.capturedLiveZeroVk +choice
assert_axioms Zcash.Snark.Fixture2.capturedLiveZeroRootFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedLiveZeroIpaTrace +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedLiveZeroStraightLineFamily +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedLiveZeroStaticChecks +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length, Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_instance_layout_length, Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_omega_order, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.straightLineInterface_nonempty_at_captured_shape +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- The consensus-maximum work-factor packages (`Zcash.Snark.FixtureMax`, reached through
-- `Capstones.Action`'s import of `Soundness.AGM.StraightLineOrchardConsensusBounds`). These are
-- the profiled endpoints the
-- book's proof journey cites by name, and they are top-level leaves: nothing censused depends on
-- them, so without these entries nothing bounds their trusted base. Unlike the captured-key
-- knowledge-error endpoints, they take the static checks and the `x`-squeeze schedule as
-- hypotheses rather than discharging them from the capture, so they reach no fixture native
-- certificate — only the Vesta point count, through the `Fp`-module structure on the curve.
assert_axioms Zcash.Snark.FixtureMax.orchard_deployed_straightline_consensus_2pow123_generatorRO_finite_security +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture2.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.fingerprint_matches

/-- info: 'Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero

/-- info: 'Zcash.Snark.Fixture2.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.instance_commitments_derived

/-- info: 'Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange

/-- info: 'Zcash.Snark.Fixture2.nonInteractiveFingerprint_matches_derived' depends on axioms: [propext,
Classical.choice,
Quot.sound,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_1,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_2,
Zcash.Snark.Fixture2.deriveChallenges_matches_captured_schedule._native.native_decide.ax_1_1,
Zcash.Snark.Fixture2.fingerprint_matches._native.native_decide.ax_1_1,
Zcash.Snark.Fixture2.instance_commitments_derived._native.native_decide.ax_1_1,
Zcash.Snark.Keygen.certificate._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.captures_use_same_fixedCommitments._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.captures_use_same_permutationCommonCommitments._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.captures_use_same_ursG._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.captures_use_same_wu._native.native_decide.ax_1_1,
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
#print axioms Zcash.Snark.Fixture2.nonInteractiveFingerprint_matches_derived
