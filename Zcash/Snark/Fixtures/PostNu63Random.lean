import Zcash.Snark.Fixtures.PostNu63
import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Post-NU6.3 provenance for the random match-only captures

The random captures (`Fixtures/{SingleAction,MultiAction}/Random`) run the deployed verifier on random proof strings, so no accepting
evaluation binds their URS the way `capturedMsm_eval_eq_zero` binds the honest captures'. Their
URS story is cross-capture identity: each random dump lists the same URS and verifying-key
commitment points as the honest single-action capture (the equalities below), and that capture's
URS is in turn bound by its accepting evaluation and by the Lean-derived commitments of the
boundary statements. The random families' verifying-key certificates
(`Fixtures/*/Random/VkCertificate.lean`) transport the single-action keygen certificate along these
equalities, exactly as `Fixtures/MultiAction/Honest/VkCertificate.lean` does.

This file is separate from `Fixtures/PostNu63.lean` so the honest multi-action certificate,
which imports that file, does not pick up a build dependency on the random fixture data
modules. The honest single-action capture is the shared right-hand side throughout, matching the
direction convention there.
-/

namespace Zcash.Snark.PostNu63Fixture

/-! ## The random single-action capture -/

theorem randomSingle_uses_postNu63 : FixtureRandom.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem randomSingle_uses_canonicalVk :
    FixtureRandom.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

/-- The random single-action capture lists the same `2 ^ 11` URS generators as the honest
single-action capture. -/
theorem randomSingle_uses_same_ursG : FixtureRandom.capturedUrsG = Fixture.capturedUrsG := by
  native_decide

/-- The same `w` and `u` URS points (point-table entries `2048` and `2049`). -/
theorem randomSingle_uses_same_wu :
    FixtureRandom.capturedPoint 2048 = Fixture.capturedPoint 2048 ∧
      FixtureRandom.capturedPoint 2049 = Fixture.capturedPoint 2049 := by
  native_decide

/-- The same ten Lagrange-basis points. -/
theorem randomSingle_uses_same_ursGLagrange :
    FixtureRandom.capturedUrsGLagrange = Fixture.capturedUrsGLagrange := by
  native_decide

/-- The same 29 fixed-column commitments. -/
theorem randomSingle_uses_same_fixedCommitments :
    FixtureRandom.capturedFixedCommitments = Fixture.capturedFixedCommitments := by
  native_decide

/-- The same 15 permutation commitments, compared by point value: the point-table indices shift
with the instance-commitment count, so a shared table prefix is not available. -/
theorem randomSingle_uses_same_permutationCommonCommitments :
    FixtureRandom.capturedPermutationCommonCommitments
      = Fixture.capturedPermutationCommonCommitments := by
  native_decide

/-- The same exporter-emitted pinned key description, compared by the kernel. -/
theorem randomSingle_uses_same_pinnedKeyDescription :
    FixtureRandom.capturedPinnedKeyDescription = Fixture.capturedPinnedKeyDescription := rfl

/-- The random single-action capture carries the honest single-action URS record;
`Fixtures/SingleAction/Random/VkCertificate.lean` rewrites along this equality. -/
theorem randomSingle_uses_same_urs : FixtureRandom.capturedURS = Fixture.capturedURS := by
  simp only [FixtureRandom.capturedURS, Fixture.capturedURS, randomSingle_uses_same_ursG,
    randomSingle_uses_same_wu.1, randomSingle_uses_same_wu.2]

theorem randomSingle_uses_same_vk : FixtureRandom.vk = Fixture.vk := by
  apply verifyingKey_eq_of_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext i
    simp only [FixtureRandom.vk, Fixture.vk]
    rw [randomSingle_uses_same_fixedCommitments]
  · funext i
    simp only [FixtureRandom.vk, Fixture.vk]
    rw [randomSingle_uses_same_permutationCommonCommitments]
  · rfl
  · rfl
  · rfl

/-! ## The random two-action capture -/

theorem randomMulti_uses_postNu63 : FixtureRandom2.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem randomMulti_uses_canonicalVk :
    FixtureRandom2.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

theorem randomMulti_uses_same_ursG : FixtureRandom2.capturedUrsG = Fixture.capturedUrsG := by
  native_decide

theorem randomMulti_uses_same_wu :
    FixtureRandom2.capturedPoint 2048 = Fixture.capturedPoint 2048 ∧
      FixtureRandom2.capturedPoint 2049 = Fixture.capturedPoint 2049 := by
  native_decide

theorem randomMulti_uses_same_ursGLagrange :
    FixtureRandom2.capturedUrsGLagrange = Fixture.capturedUrsGLagrange := by
  native_decide

theorem randomMulti_uses_same_fixedCommitments :
    FixtureRandom2.capturedFixedCommitments = Fixture.capturedFixedCommitments := by
  native_decide

theorem randomMulti_uses_same_permutationCommonCommitments :
    FixtureRandom2.capturedPermutationCommonCommitments
      = Fixture.capturedPermutationCommonCommitments := by
  native_decide

/-- The same exporter-emitted pinned key description, compared by the kernel. -/
theorem randomMulti_uses_same_pinnedKeyDescription :
    FixtureRandom2.capturedPinnedKeyDescription = Fixture.capturedPinnedKeyDescription := rfl

theorem randomMulti_uses_same_urs : FixtureRandom2.capturedURS = Fixture.capturedURS := by
  simp only [FixtureRandom2.capturedURS, Fixture.capturedURS, randomMulti_uses_same_ursG,
    randomMulti_uses_same_wu.1, randomMulti_uses_same_wu.2]

theorem randomMulti_uses_same_vk : FixtureRandom2.vk = Fixture.vk := by
  apply verifyingKey_eq_of_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext i
    simp only [FixtureRandom2.vk, Fixture.vk]
    rw [randomMulti_uses_same_fixedCommitments]
  · funext i
    simp only [FixtureRandom2.vk, Fixture.vk]
    rw [randomMulti_uses_same_permutationCommonCommitments]
  · rfl
  · rfl
  · rfl

end Zcash.Snark.PostNu63Fixture
