import Zcash.Snark.Fixtures.MultiAction.Honest.VkCertificate
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# The captured verifying key's non-group profile

Keys with the captured scalar and layout data inherit its field support and structural
lawfulness from the keygen certificate.

Group commitments are deliberately outside that profile. In the AGM game they must be represented
over the sampled basis, so demanding literal equality with the fixture's fixed Vesta points would
leave the premise uninhabited for some bases.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The part of the captured verifying key used by the static and degree checks. The two
group-valued commitment families are intentionally absent: the AGM setup resamples the basis,
and public verifier points must therefore be supplied with representations over that basis. -/
structure CapturedVerifierKeyProfile
    (candidate : VerifyingKey shape Fp VestaG) : Prop where
  omega : candidate.omega = vk.omega
  n : candidate.n = vk.n
  delta : candidate.delta = vk.delta
  blindingFactors : candidate.blindingFactors = vk.blindingFactors
  chunkLen : candidate.chunkLen = vk.chunkLen
  gates : candidate.gates = vk.gates
  instanceQueryLayout : candidate.instanceQueryLayout = vk.instanceQueryLayout
  adviceQueryLayout : candidate.adviceQueryLayout = vk.adviceQueryLayout
  fixedQueryLayout : candidate.fixedQueryLayout = vk.fixedQueryLayout
  permutationChunks : candidate.permutationChunks = vk.permutationChunks
  lookupInputExprs : candidate.lookupInputExprs = vk.lookupInputExprs
  lookupTableExprs : candidate.lookupTableExprs = vk.lookupTableExprs

/-- The captured key itself has the captured non-group profile. -/
theorem capturedVerifierKeyProfile_vk : CapturedVerifierKeyProfile vk := by
  constructor <;> rfl

namespace CapturedVerifierKeyProfile

variable {candidate : VerifyingKey shape Fp VestaG}

theorem fieldSupport (h : CapturedVerifierKeyProfile candidate) :
    VerifyingKey.FieldSupport candidate where
  n_eq := h.n.trans VerifyingKey.FieldSupport.n_eq
  omega_eq := h.omega.trans VerifyingKey.FieldSupport.omega_eq
  delta_eq := h.delta.trans VerifyingKey.FieldSupport.delta_eq
  domainExponent_le := VerifyingKey.FieldSupport.domainExponent_le (vk := vk)
  permutationColumnCount_le := VerifyingKey.FieldSupport.permutationColumnCount_le (vk := vk)

theorem wellFormed (h : CapturedVerifierKeyProfile candidate) :
    VerifyingKey.WellFormed candidate where
  adviceQueryLayout_length := (congrArg List.length h.adviceQueryLayout).trans
    VerifyingKey.WellFormed.adviceQueryLayout_length
  instanceQueryLayout_length := (congrArg List.length h.instanceQueryLayout).trans
    VerifyingKey.WellFormed.instanceQueryLayout_length
  fixedQueryLayout_length := (congrArg List.length h.fixedQueryLayout).trans
    VerifyingKey.WellFormed.fixedQueryLayout_length
  blindingFactors_add_one_lt_n := by
    rw [h.blindingFactors, h.n]
    exact VerifyingKey.WellFormed.blindingFactors_add_one_lt_n
  chunkLen_pos := by
    rw [h.chunkLen]
    exact VerifyingKey.WellFormed.chunkLen_pos
  permutationChunks_length := by
    rw [h.permutationChunks]
    exact VerifyingKey.WellFormed.permutationChunks_length
  permutationChunks_getD_length := by
    rw [h.permutationChunks, h.chunkLen]
    exact VerifyingKey.WellFormed.permutationChunks_getD_length
  permutationChunkRoutingCoherent := by
    simpa only [PermutationChunkRoutingCoherent, PermutationColumnRef.Coherent,
      h.permutationChunks, h.adviceQueryLayout, h.instanceQueryLayout, h.fixedQueryLayout] using
      (VerifyingKey.WellFormed.permutationChunkRoutingCoherent (vk := vk))

end CapturedVerifierKeyProfile

end Zcash.Snark.Fixture2
