import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Post-NU6.3 fixture provenance

Cross-capture checks for the canonical Post-NU6.3 Orchard-protocol verifying key and URS. During
fixture generation, the `orchard` implementation first compares the exact `PinnedVerificationKey`
debug representation against its checked-in circuit description. The pinned `halo2` exporter then
emits both the transcript representation below and the exact compact string it hashed.

The hand-pinned scalar here makes fixture drift visible in this repository, while the Rust
regeneration assertion binds it to the full canonical pinned key. `Fixtures/PinnedKey.lean` goes
further: it hashes the exporter-emitted description with Halo2's `Halo2-Verify-Key` BLAKE2b and
reads its fields back against the captured key, so the scalar is checked rather than only pinned.

The point-level equalities below identify the two captures' URS and verifying-key commitment
points; the multi-action verifying-key certificate (`Fixtures/MultiAction/Honest/VkCertificate.lean`)
is transported from the single-action one along them.
-/

namespace Zcash.Snark.PostNu63Fixture

/-- Fieldwise extensionality for two verifying keys at the same circuit shape. -/
theorem verifyingKey_eq_of_fields
    {shape : CircuitShape} {F G : Type*}
    (left right : VerifyingKey shape F G)
    (omega : left.omega = right.omega)
    (n : left.n = right.n)
    (blindingFactors : left.blindingFactors = right.blindingFactors)
    (delta : left.delta = right.delta)
    (chunkLen : left.chunkLen = right.chunkLen)
    (gates : left.gates = right.gates)
    (instanceQueryLayout : left.instanceQueryLayout = right.instanceQueryLayout)
    (adviceQueryLayout : left.adviceQueryLayout = right.adviceQueryLayout)
    (fixedQueryLayout : left.fixedQueryLayout = right.fixedQueryLayout)
    (fixedCommitment : left.fixedCommitment = right.fixedCommitment)
    (permutationCommonCommitment :
      left.permutationCommonCommitment = right.permutationCommonCommitment)
    (permutationChunks : left.permutationChunks = right.permutationChunks)
    (lookupInputExprs : left.lookupInputExprs = right.lookupInputExprs)
    (lookupTableExprs : left.lookupTableExprs = right.lookupTableExprs) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Halo2's transcript representation of the canonical Post-NU6.3 pinned verifying key. -/
def canonicalVkTranscriptRepr : Fp :=
  (8223501628842095769 : Fp)
    + (2306373111636605627 : Fp) * (2 : Fp) ^ 64
    + (3243000079158773602 : Fp) * (2 : Fp) ^ 128
    + (370130488735545691 : Fp) * (2 : Fp) ^ 192

theorem singleAction_uses_postNu63 : Fixture.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem multiAction_uses_postNu63 : Fixture2.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem singleAction_uses_canonicalVk :
    Fixture.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

theorem multiAction_uses_canonicalVk :
    Fixture2.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

/-- Every `capturedPoint` reference used to build either captured augmented URS is backed by its
point table.  The `2^k` generators occupy indices `0, ..., 2^k - 1`, followed by `w` and `u`; this
separately guards the inner `capturedPoints.getD` from silently substituting the identity. -/
theorem captures_urs_point_references_in_bounds :
    2 ^ Fixture.shape.k + 2 ≤ Fixture.capturedPoints.length ∧
      2 ^ Fixture2.shape.k + 2 ≤ Fixture2.capturedPoints.length := by
  native_decide

/-- Both captures use the same deterministic Halo2 URS (`g`, then `w` and `u` occupy the first
`2^11 + 2` entries in each generated concrete-point table).

This detects *skew* between the two captures' generators, not the correctness of the URS itself:
both lists are emitted by the same generator, so an equally wrong URS in both would still pass. The
independent binding is elsewhere — `capturedMsm_eval_eq_zero` computes the MSM against this exact URS
and would fail with overwhelming probability for a URS that was not Halo2's deterministic one. -/
theorem captures_use_same_urs_coordinates :
    Fixture.capturedPointCoordinates.take (2 ^ 11 + 2)
      = Fixture2.capturedPointCoordinates.take (2 ^ 11 + 2) := by
  native_decide

/-- The two captures list the same `2 ^ 11` URS generators. -/
theorem captures_use_same_ursG : Fixture2.capturedUrsG = Fixture.capturedUrsG := by
  native_decide

/-- The two captures list the same `w` and `u` URS points (point-table entries `2048`
and `2049`). -/
theorem captures_use_same_wu :
    Fixture2.capturedPoint 2048 = Fixture.capturedPoint 2048 ∧
      Fixture2.capturedPoint 2049 = Fixture.capturedPoint 2049 := by
  native_decide

/-- The two captures list the same ten Lagrange-basis points. -/
theorem captures_use_same_ursGLagrange :
    Fixture2.capturedUrsGLagrange = Fixture.capturedUrsGLagrange := by
  native_decide

/-- The two captures list the same 29 fixed-column commitments. -/
theorem captures_use_same_fixedCommitments :
    Fixture2.capturedFixedCommitments = Fixture.capturedFixedCommitments := by
  native_decide

/-- The two captures list the same 15 permutation commitments. Their point-table indices are
shifted by the extra instance commitment, so this check compares the point values, not a shared
table prefix. -/
theorem captures_use_same_permutationCommonCommitments :
    Fixture2.capturedPermutationCommonCommitments
      = Fixture.capturedPermutationCommonCommitments := by
  native_decide

/-- The two captures carry one and the same URS record; the multi-action verifying-key
certificate (`Fixtures/MultiAction/Honest/VkCertificate.lean`) rewrites along this equality. -/
theorem captures_use_same_urs : Fixture2.capturedURS = Fixture.capturedURS := by
  simp only [Fixture2.capturedURS, Fixture.capturedURS, captures_use_same_ursG,
    captures_use_same_wu.1, captures_use_same_wu.2]

/-- The two captures carry the same circuit-fixed verifying key. Proof count is no longer a VK
parameter; the only non-definitional fields are the commitment families pinned above. -/
theorem captures_use_same_vk : Fixture2.vk = Fixture.vk := by
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
    simp only [Fixture2.vk, Fixture.vk]
    rw [captures_use_same_fixedCommitments]
  · funext i
    simp only [Fixture2.vk, Fixture.vk]
    rw [captures_use_same_permutationCommonCommitments]
  · rfl
  · rfl
  · rfl

-- Trust-boundary guards: fail the `FixtureCheck` build if any provenance theorem above comes to
-- rest on a `sorry` reached through some dependency (the checks are `native_decide`, so a hole
-- would otherwise only surface as a warning). Mirrors the `SingleAction`/`MultiAction` boundaries.
assert_no_sorry singleAction_uses_postNu63
assert_no_sorry multiAction_uses_postNu63
assert_no_sorry singleAction_uses_canonicalVk
assert_no_sorry multiAction_uses_canonicalVk
assert_no_sorry captures_use_same_urs_coordinates
assert_no_sorry captures_use_same_ursG
assert_no_sorry captures_use_same_wu
assert_no_sorry captures_use_same_ursGLagrange
assert_no_sorry captures_use_same_fixedCommitments
assert_no_sorry captures_use_same_permutationCommonCommitments
assert_no_sorry captures_use_same_urs
assert_no_sorry captures_use_same_vk

end Zcash.Snark.PostNu63Fixture
