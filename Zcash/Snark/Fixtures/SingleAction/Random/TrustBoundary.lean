import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.SingleAction.Random.Faithfulness
import Zcash.Snark.Fixtures.SingleAction.Random.Negative
import Zcash.Snark.Fixtures.SingleAction.Random.Boundary
import Zcash.Snark.Fixtures.SingleAction.Random.Epsilon
import Zcash.Snark.Fixtures.PostNu63Random
import Zcash.Snark.Fixtures.SingleAction.Random.Transcript
import Zcash.Snark.Fixtures.SingleAction.Random.ProofBytes
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the random single-action fixture

The random-capture analog of the honest `Fixtures.SingleAction.Honest`/`Fixtures.MultiAction.Honest` trust
boundaries, and checked the same way: `assert_axioms` (from `Zcash.Meta.AxiomCheck`) bounds the
trusted base of every captured claim at the standard tier, walking the whole elaborated
dependency graph, with `+native` naming exactly the declarations that may spend compiler trust;
`#print axioms` pinned by `#guard_msgs` freezes the exact axiom set of the load-bearing claims.

Two differences from the honest siblings, both consequences of the capture being match-only:

* The census has no MSM-identity evaluations. Their place is taken by the generated fixture's
  `capturedMsm_evalNat_ne_zero`, which pins the capture as genuinely non-accepting and is censused
  with the other aliveness guards from `Negative.lean`.
* The shape/VK faithfulness checks (`Faithfulness.lean`) are censused here, so every theorem of
  this family sits under a build-time axiom bound.
-/

-- Census the captured random single-action fixture, including permitted native-code trust.
assert_axioms Zcash.Snark.FixtureRandom.capturedPointCoordinatesValid_eq_true +native(
  Zcash.Snark.FixtureRandom.capturedPointCoordinatesValid_eq_true)
assert_axioms Zcash.Snark.FixtureRandom.capturedUrsG_length +native(
  Zcash.Snark.FixtureRandom.capturedUrsG_length)
assert_axioms Zcash.Snark.FixtureRandom.capturedInit_startsWith_vkTranscriptRepr +native(
  Zcash.Snark.FixtureRandom.capturedInit_startsWith_vkTranscriptRepr)
assert_axioms Zcash.Snark.FixtureRandom.fingerprint_matches +native(
  Zcash.Snark.FixtureRandom.fingerprint_matches)
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms Zcash.Snark.assemble

-- The aliveness guards (the generated fixture plus `Negative.lean`): a match-only capture has no
-- accepting evaluation, so these pin what keeps it alive — the model accepts the random point,
-- the captured MSM is not the identity, and the match still detects a blind-slot tamper here.
assert_axioms Zcash.Snark.FixtureRandom.valid_capture_assembles +native(
  Zcash.Snark.FixtureRandom.valid_capture_assembles)
assert_axioms Zcash.Snark.FixtureRandom.capturedMsm_evalNat_ne_zero +native(
  Zcash.Snark.FixtureRandom.capturedMsm_evalNat_ne_zero)
assert_axioms Zcash.Snark.FixtureRandom.tampered_fixed_eval_assembles +native(
  Zcash.Snark.FixtureRandom.tampered_fixed_eval_assembles)
assert_axioms Zcash.Snark.FixtureRandom.tampered_fixed_eval_fingerprint_mismatch +native(
  Zcash.Snark.FixtureRandom.tampered_fixed_eval_fingerprint_mismatch)

-- The shape/VK faithfulness checks (`Faithfulness.lean`): the captured lists, layouts,
-- expression indices, and transcript prefix agree with the generated `shape`, guarding the
-- `finFn`/`finFnG` totalization hazards.
assert_axioms Zcash.Snark.FixtureRandom.captured_list_lengths_match_shape +native(
  Zcash.Snark.FixtureRandom.captured_list_lengths_match_shape)
assert_axioms Zcash.Snark.FixtureRandom.query_layout_columns_in_range +native(
  Zcash.Snark.FixtureRandom.query_layout_columns_in_range)
assert_axioms Zcash.Snark.FixtureRandom.vk_expression_refs_in_range +native(
  Zcash.Snark.FixtureRandom.vk_expression_refs_in_range)
assert_axioms Zcash.Snark.FixtureRandom.permutation_chunks_match_shape +native(
  Zcash.Snark.FixtureRandom.permutation_chunks_match_shape)
assert_axioms Zcash.Snark.FixtureRandom.vk_domain_size_matches_shape +native(
  Zcash.Snark.FixtureRandom.vk_domain_size_matches_shape)

-- The instance-commitment derivation: the two captured claims, plus the data and functions they
-- range over. The latter are flagless — they are ordinary definitions, so compiler trust must not
-- reach them; only the two claims about them may spend it.
assert_axioms Zcash.Snark.FixtureRandom.instance_commitments_derived +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived)
assert_axioms Zcash.Snark.FixtureRandom.capturedPublicInstances_within_lagrange +native(
  Zcash.Snark.FixtureRandom.capturedPublicInstances_within_lagrange)
assert_axioms Zcash.Snark.FixtureRandom.capturedUrsGLagrange
assert_axioms Zcash.Snark.FixtureRandom.capturedPublicInstances
assert_axioms Zcash.Snark.FixtureRandom.commitLagrange
assert_axioms Zcash.Snark.FixtureRandom.derivedInstanceCommitment

-- Cross-capture provenance (`Fixtures/PostNu63Random.lean`): the circuit-id and canonical-VK
-- pins, the point-level equalities that transport the single-action keygen certificate to this
-- capture, and the URS record equality assembled from them.
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_postNu63 +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_postNu63)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_canonicalVk +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_canonicalVk)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursGLagrange +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursGLagrange)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments)
assert_axioms Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_urs +native(
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu)

-- The transported keygen certificate (`VkCertificate.lean`): the random single-action key equals
-- its end-to-end derivation. Owners are the single-action certificate's plus the cross-capture
-- point equalities — no second keygen evaluation.
assert_axioms Zcash.Snark.FixtureRandom.vk_eq_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- The Fiat–Shamir schedule checks, the composed fingerprint, and the boundary statement at the
-- Lean-derived key (`Boundary.lean`). The oracle/schedule data and the composed-statement
-- functions are flagless; compiler trust may enter only through the named claims.
assert_axioms Zcash.Snark.FixtureRandom.capturedChallengeValues_eq_expected +native(
  Zcash.Snark.FixtureRandom.capturedChallengeValues_eq_expected)
assert_axioms Zcash.Snark.FixtureRandom.missingChallenge_not_captured +native(
  Zcash.Snark.FixtureRandom.missingChallenge_not_captured)
assert_axioms Zcash.Snark.FixtureRandom.capturedChallengeValues_nodup +native(
  Zcash.Snark.FixtureRandom.capturedChallengeValues_nodup)
assert_axioms Zcash.Snark.FixtureRandom.capturedScheduleIncludesInit_eq_true +native(
  Zcash.Snark.FixtureRandom.capturedScheduleIncludesInit_eq_true)
assert_axioms Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule +native(
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule)
-- The statement-bound path must reproduce the captured VK/instance prefix and, through it, the
-- challenge schedule: `initialTranscript`'s own shape is checked against the capture rather than
-- entering the boundary as the opaque dumped `capturedInit`.
assert_axioms Zcash.Snark.FixtureRandom.capturedInit_eq_initialTranscript +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived)
assert_axioms Zcash.Snark.FixtureRandom.deriveChallengesForStatement_matches_captured_schedule +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule)
assert_axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.FixtureRandom.fingerprint_matches)
assert_axioms Zcash.Snark.FixtureRandom.capturedFs
assert_axioms Zcash.Snark.FixtureRandom.capturedInit
assert_axioms Zcash.Snark.deriveChallenges
assert_axioms Zcash.Snark.nonInteractiveFingerprint
assert_axioms Zcash.Snark.initialTranscript
assert_axioms Zcash.Snark.deriveChallengesForStatement
assert_axioms Zcash.Snark.nonInteractiveFingerprintForStatement
assert_axioms Zcash.Snark.FixtureRandom.derivedVk +native(
  Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule,
  Zcash.Snark.FixtureRandom.fingerprint_matches)

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.FixtureRandom.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.FixtureRandom.fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.fingerprint_matches

/-- info: 'Zcash.Snark.FixtureRandom.capturedMsm_evalNat_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.FixtureRandom.capturedMsm_evalNat_ne_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.capturedMsm_evalNat_ne_zero

/-- info: 'Zcash.Snark.FixtureRandom.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.FixtureRandom.instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.instance_commitments_derived

/-- info: 'Zcash.Snark.FixtureRandom.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.FixtureRandom.capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.capturedPublicInstances_within_lagrange

/-- info: 'Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_derived' depends on axioms: [propext,
Classical.choice,
Quot.sound,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_1,
CompElliptic.Fields.Pasta.pallasBase._native.native_decide.ax_2,
Zcash.Snark.FixtureRandom.deriveChallenges_matches_captured_schedule._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.fingerprint_matches._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.instance_commitments_derived._native.native_decide.ax_1_1,
Zcash.Snark.Keygen.certificate._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG._native.native_decide.ax_1_1,
Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu._native.native_decide.ax_1_1,
CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_derived

-- Quantified-match ε at this capture (`Epsilon.lean`): the verifying-key symbolic facts and the
-- degree/coordinate literals hold at the captured key, the good event contains the captured
-- point itself, and any competing coefficient family of numerator degree ≤ 16452 over the
-- walk's denominators that differs anywhere from Lean's agrees with the assembled MSM at a
-- uniform sample-space point with probability at most (16452 + 2071)/p = 18523/p, p ≈ 2^254.
-- The challenge-restricted headliner pins the proof-string slots to the captured scalars and
-- prices the same 18523/p bound over the 22 challenge coordinates alone — what the
-- random-oracle premise alone buys at this capture.
-- The cross-denominator pair (`competing_family_agreement_le_denClosure` and its
-- challenge-restricted companion) extends both bounds to a competing family bringing its own
-- denominators from the enumerated factor closure, at (16452 + 2077 + 2071)/p = 20600/p.
assert_axioms Zcash.Snark.FixtureRandom.vkSymbolicFacts +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts)
assert_axioms Zcash.Snark.FixtureRandom.vk_chunk_width_le +native(
  Zcash.Snark.FixtureRandom.vk_chunk_width_le)
assert_axioms Zcash.Snark.FixtureRandom.vk_chunks_length_eq +native(
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq)
assert_axioms Zcash.Snark.FixtureRandom.msmDegreeBudget_eq +native(
  Zcash.Snark.FixtureRandom.msmDegreeBudget_eq)
assert_axioms Zcash.Snark.FixtureRandom.msmDenBudget_eq +native(
  Zcash.Snark.FixtureRandom.msmDenBudget_eq)
assert_axioms Zcash.Snark.FixtureRandom.otherLen_eq +native(
  Zcash.Snark.FixtureRandom.otherLen_eq)
assert_axioms Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq +native(
  Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq)
assert_axioms Zcash.Snark.FixtureRandom.card_scalarSlot
assert_axioms Zcash.Snark.FixtureRandom.capturedSlotVals
assert_axioms Zcash.Snark.FixtureRandom.card_challengeSlot
assert_axioms Zcash.Snark.FixtureRandom.coefficientFamily +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts,
  Zcash.Snark.FixtureRandom.vk_chunk_width_le,
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq)
assert_axioms Zcash.Snark.FixtureRandom.capturedPoint_goodEvent +native(
  Zcash.Snark.FixtureRandom.capturedPoint_goodEvent)
assert_axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts,
  Zcash.Snark.FixtureRandom.vk_chunk_width_le,
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq,
  Zcash.Snark.FixtureRandom.msmDegreeBudget_eq,
  Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq)
assert_axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts,
  Zcash.Snark.FixtureRandom.vk_chunk_width_le,
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq,
  Zcash.Snark.FixtureRandom.msmDegreeBudget_eq,
  Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq)
assert_axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_denClosure +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts,
  Zcash.Snark.FixtureRandom.vk_chunk_width_le,
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq,
  Zcash.Snark.FixtureRandom.msmDegreeBudget_eq,
  Zcash.Snark.FixtureRandom.msmDenBudget_eq,
  Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq)
assert_axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly_denClosure +native(
  Zcash.Snark.FixtureRandom.vkSymbolicFacts,
  Zcash.Snark.FixtureRandom.vk_chunk_width_le,
  Zcash.Snark.FixtureRandom.vk_chunks_length_eq,
  Zcash.Snark.FixtureRandom.msmDegreeBudget_eq,
  Zcash.Snark.FixtureRandom.msmDenBudget_eq,
  Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq)

/-- info: 'Zcash.Snark.FixtureRandom.competing_family_agreement_le' depends on axioms: [propext,
Classical.choice,
Quot.sound,
Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDegreeBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_2,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_3,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_4,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_5,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_6,
Zcash.Snark.FixtureRandom.vk_chunk_width_le._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vk_chunks_length_eq._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le

/-- info: 'Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly' depends on
axioms: [propext,
Classical.choice,
Quot.sound,
Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDegreeBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_2,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_3,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_4,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_5,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_6,
Zcash.Snark.FixtureRandom.vk_chunk_width_le._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vk_chunks_length_eq._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly

/-- info: 'Zcash.Snark.FixtureRandom.competing_family_agreement_le_denClosure' depends on
axioms: [propext,
Classical.choice,
Quot.sound,
Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDegreeBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDenBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_2,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_3,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_4,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_5,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_6,
Zcash.Snark.FixtureRandom.vk_chunk_width_le._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vk_chunks_length_eq._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_denClosure

/-- info: 'Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly_denClosure' depends on
axioms: [propext,
Classical.choice,
Quot.sound,
Zcash.Snark.FixtureRandom.denFactors_degree_sum_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDegreeBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.msmDenBudget_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_2,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_3,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_4,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_5,
Zcash.Snark.FixtureRandom.vkSymbolicFacts._native.native_decide.ax_1_6,
Zcash.Snark.FixtureRandom.vk_chunk_width_le._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.vk_chunks_length_eq._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.competing_family_agreement_le_challengesOnly_denClosure

/-- info: 'Zcash.Snark.FixtureRandom.capturedPoint_goodEvent' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.FixtureRandom.capturedPoint_goodEvent._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.capturedPoint_goodEvent

-- The Perm→positional bridge at this capture (`Epsilon.lean`): the captured `other` bases are
-- pairwise distinct, so the boundary match's `List.Perm` is realized by the fixed base-matching
-- re-indexing and the assembled MSM agrees with the captured one coordinate-wise — the capture's
-- membership in the positional agreement event priced above is a theorem, not audited prose.
assert_axioms Zcash.Snark.FixtureRandom.capturedMsm_other_bases_nodup +native(
  Zcash.Snark.FixtureRandom.capturedMsm_other_bases_nodup)
assert_axioms Zcash.Snark.FixtureRandom.fingerprint_matches_positional +native(
  Zcash.Snark.FixtureRandom.capturedMsm_other_bases_nodup,
  Zcash.Snark.FixtureRandom.fingerprint_matches,
  Zcash.Snark.FixtureRandom.otherLen_eq,
  Zcash.Snark.FixtureRandom.valid_capture_assembles)

/-- info: 'Zcash.Snark.FixtureRandom.fingerprint_matches_positional' depends on axioms: [propext,
Classical.choice,
Quot.sound,
Zcash.Snark.FixtureRandom.capturedMsm_other_bases_nodup._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.fingerprint_matches._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.otherLen_eq._native.native_decide.ax_1_1,
Zcash.Snark.FixtureRandom.valid_capture_assembles._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.FixtureRandom.fingerprint_matches_positional

-- The byte layer beneath the schedule (`Transcript.lean`): every captured challenge recomputed
-- from halo2's transcript encoding through BLAKE2b, and the fingerprint match restated on it.
-- `deriveChallenges_matches_blake2b` is the only new compiler-trust element; the derived-key
-- statement of record inherits it in place of the captured-table schedule check.
assert_axioms Zcash.Snark.FixtureRandom.markerSchedule_matches_blake2b +native(
  Zcash.Snark.FixtureRandom.markerSchedule_matches_blake2b)
assert_axioms Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b +native(
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b)
assert_axioms Zcash.Snark.FixtureRandom.deriveChallengesForStatement_matches_blake2b +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b)
assert_axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_blake2b +native(
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b,
  Zcash.Snark.FixtureRandom.fingerprint_matches)
assert_axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_derived_blake2b +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments,
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
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b,
  Zcash.Snark.FixtureRandom.fingerprint_matches)

-- The proof-string byte layer (`ProofBytes.lean`): the captured raw bytes decode to exactly the
-- captured typed proof and serialize back to them, plus the byte-level negatives. Point
-- decoding runs Tonelli–Shanks on `vestaBase`, whose validity certificate is upstream compiler
-- trust, so every theorem that runs the decoder names it.
assert_computable Zcash.Snark.hexDecode? +choice
assert_axioms Zcash.Snark.FixtureRandom.capturedProofHex_decodes +native(
  Zcash.Snark.FixtureRandom.capturedProofHex_decodes)
assert_axioms Zcash.Snark.FixtureRandom.capturedProofBytes_length +native(
  Zcash.Snark.FixtureRandom.capturedProofBytes_length)
assert_axioms Zcash.Snark.FixtureRandom.serializeProof_eq_capturedProofBytes +native(
  Zcash.Snark.FixtureRandom.serializeProof_eq_capturedProofBytes)
assert_axioms Zcash.Snark.FixtureRandom.capturedProofBytes_decodes +native(
  Zcash.Snark.FixtureRandom.capturedProofBytes_decodes,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.truncated_proof_rejected +native(
  Zcash.Snark.FixtureRandom.truncated_proof_rejected,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.non_canonical_scalar_rejected +native(
  Zcash.Snark.FixtureRandom.non_canonical_scalar_rejected,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.identity_point_rejected +native(
  Zcash.Snark.FixtureRandom.identity_point_rejected,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.out_of_range_coordinate_rejected +native(
  Zcash.Snark.FixtureRandom.out_of_range_coordinate_rejected,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.non_residue_x_rejected +native(
  Zcash.Snark.FixtureRandom.non_residue_x_rejected,
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms Zcash.Snark.FixtureRandom.flipped_sign_decodes_negated +native(
  Zcash.Snark.FixtureRandom.flipped_sign_decodes_negated,
  CompElliptic.Fields.Pasta.vestaBase)

-- The key digest opening the transcript, derived from the pinned key description
-- (`Fixtures/PinnedKey.lean`) instead of taken from the capture.
assert_axioms Zcash.Snark.FixtureRandom.keyDigest_eq_capturedVkTranscriptRepr +native(
  Zcash.Snark.FixtureRandom.keyDigest_eq_capturedVkTranscriptRepr)
assert_axioms Zcash.Snark.FixtureRandom.nonInteractiveFingerprint_matches_derived_keyDigest +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_ursG,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_wu,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_fixedCommitments,
  Zcash.Snark.PostNu63Fixture.randomSingle_uses_same_permutationCommonCommitments,
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
  Zcash.Snark.FixtureRandom.instance_commitments_derived,
  Zcash.Snark.FixtureRandom.deriveChallenges_matches_blake2b,
  Zcash.Snark.FixtureRandom.fingerprint_matches,
  Zcash.Snark.FixtureRandom.keyDigest_eq_capturedVkTranscriptRepr)
