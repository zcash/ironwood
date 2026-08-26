import Zcash.Snark.Fixtures.MultiAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.MultiAction.Honest.Transcript
import Zcash.Snark.Fixtures.MultiAction.Honest.VkCertificate
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key (multi-action)

The statement of record for the multi-action capture: the deployed verifier's fingerprint
— `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the captured
oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS
(`VkCertificate.lean`). The dumped verifying-key record no longer enters the comparison,
and the captured challenges are derived rather than taken as given.

The instance side stays `derivedInstanceCommitment` — already a derivation, the Lagrange
commitment of the captured public inputs, pinned to the captured points by
`instance_commitments_derived` — since the multi-action capture has no
`Keygen/InstanceCapture.lean` analogue.

The byte-level form, `nonInteractiveFingerprint_matches_derived_blake2b`, is the statement of
record: it replaces the captured oracle table with the deployed hash itself, deriving every
challenge as BLAKE2b over halo2's transcript encoding (`Transcript.lean`,
`deriveChallenges_matches_blake2b`). The captured-table form stays as the diagnostic that
separates a schedule error from an encoding or hash error.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- **The fingerprint match at the derived verifying key.** The transported certificate
(`vk_eq_derived`) rewrites the dumped key out of `nonInteractiveFingerprint_matches`. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs (fun _ => capturedVkTranscriptRepr)
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  have h : vk = derivedVk := vk_eq_derived
  rw [← h]
  exact nonInteractiveFingerprint_matches

assert_no_sorry nonInteractiveFingerprint_matches_derived

/-- **The fingerprint match at the derived key, from transcript bytes.** As
`nonInteractiveFingerprint_matches_derived`, with the captured oracle table replaced by the
deployed hash: every challenge is BLAKE2b over halo2's transcript encoding of the derived prefix
and the proof. -/
theorem nonInteractiveFingerprint_matches_derived_blake2b :
    MsmMatch
      (nonInteractiveFingerprintForStatement halo2Transcript (fun _ => capturedVkTranscriptRepr)
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  have h : vk = derivedVk := vk_eq_derived
  rw [← h]
  exact nonInteractiveFingerprint_matches_blake2b

assert_no_sorry nonInteractiveFingerprint_matches_derived_blake2b

end Zcash.Snark.Fixture2
