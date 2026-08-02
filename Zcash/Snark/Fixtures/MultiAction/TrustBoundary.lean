import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.MultiAction.FiatShamir
import Zcash.Snark.Fixtures.MultiAction.Degree
import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Fixtures.MultiAction.StraightLineKnowledgeError
import Zcash.Snark.Fixtures.MultiAction.CapturedZeroFamily
import Zcash.Snark.Fixtures.MultiAction.ActionCapstone
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.TrustBoundary`, and checked the same way: CI
bounds the trusted base of the concrete coordinate validation, verifier fingerprint match, executable
Vesta MSM identity, and instance-commitment derivation, and pins the exact axiom set of the
`native_decide` claims among them.

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

One AGM capstone is retained: the straight-line endpoint, which consumes an online
representation trace and has a pointwise four-invocation bound.  Those representations are ghost
extractor data: they are neither transmitted nor checked by the Halo2 verifier.  Accordingly the
endpoint is only an AGM-and-random-oracle result under the supplied finite-security Vesta DLOG
profile.
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
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_knowledge_error_captured_straightLine +native(
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
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_knowledge_error_captured_straightLine_generatorRO +native(
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
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_knowledge_error_captured_straightLine_direct_generatorRO +native(
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
assert_axioms Zcash.Snark.Fixture.actionAcceptFalseStatementEvent +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.action_semantic_count_le
assert_axioms Zcash.Snark.Fixture.two_pow_254_le_card
assert_axioms Zcash.Snark.Fixture.action_semantic_terms_le
assert_axioms Zcash.Snark.Fixture.derived_scalars +native(
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
assert_axioms Zcash.Snark.Fixture.derived_lookups +native(
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
assert_axioms Zcash.Snark.Fixture.staticChecks_of_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.schedule_of_derived +native(
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
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_captured +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le,
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
-- The consensus-generic form of the same bound, over every proof multiplicity at or below the
-- Orchard maximum rather than the captured one.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_captured_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_sequential +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Its consensus-generic form.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_sequential_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Consensus-generic endpoints with concrete resources and transcript bias.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_2pow123_workFactor_generatorRO_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq,
  Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le,
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
-- The single-multiplicity form of the same work-factor endpoint.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_2pow123_workFactor_generatorRO +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_adaptive_2pow123_workFactor_generatorRO_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq,
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
assert_axioms Zcash.Snark.Fixture.orchard_action_knowledgeFailure_adaptive_2pow123_workFactor_generatorRO_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq,
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
assert_axioms Zcash.Snark.Fixture.orchard_action_knowledgeFailure_prob_le_adaptive_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Census the public single-Action compatibility endpoints.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_adaptive +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
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
-- Its consensus-generic form.
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_prob_le_adaptive_for +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
  Zcash.Snark.Fixture.resolverPermutationCell_card_eq, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_gates_degree_le, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalseStatement_adaptive_2pow123_workFactor_generatorRO +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.lookupData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.adviceQueryLayout_columns_lt,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.actionLookupActivationCount_le,
  Zcash.Snark.Fixture.actionLookupInputArity_le,
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
assert_computable Zcash.Snark.Fixture2.capturedLiveZeroAdaptiveFamily +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.capturedLiveZeroStaticChecks +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length, Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_instance_layout_length, Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_omega_order, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.straightLineInterface_nonempty_at_captured_shape +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixture2.adaptiveInterface_nonempty_at_captured_shape +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- The consensus-maximum work-factor packages (`Zcash.Snark.FixtureMax`, reached through
-- `ActionCapstone`'s import of `StraightLineMaxShapeBounds`). These are the profiled endpoints the
-- book's proof journey cites by name, and they are top-level leaves: nothing censused depends on
-- them, so without these entries nothing bounds their trusted base. Unlike the captured-key
-- knowledge-error endpoints, they take the static checks and the `x`-squeeze schedule as
-- hypotheses rather than discharging them from the capture, so they reach no fixture native
-- certificate — only the Vesta point count, through the `Fp`-module structure on the curve.
assert_axioms Zcash.Snark.FixtureMax.straightLine_consensus_2pow123_workFactor_generatorRO +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.FixtureMax.straightLine_consensus_2pow122_workFactor_generatorRO +native(
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
