import Zcash.Snark.Fixtures.SingleAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.SingleAction.Honest.Transcript
import Zcash.Snark.Keygen.InstanceCapture
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key

The statement of record for the single-action capture: the deployed verifier's fingerprint
— `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the captured
oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS, and, in the strongest
form, the instance commitments spelled as the circuit's commitment of the captured public
inputs. The dumped verifying-key record no longer enters the comparison, and the captured
challenges are derived rather than taken as given.

Both theorems rewrite certificate equalities into the captured match — stating the boundary
at derived artifacts costs no new evaluation.

The byte-level form, `nonInteractiveFingerprint_matches_derived_blake2b`, is the statement of
record: it replaces the captured oracle table with the deployed hash itself, deriving every
challenge as BLAKE2b over halo2's transcript encoding (`Transcript.lean`,
`deriveChallenges_matches_blake2b`). The captured-table form stays as the diagnostic that
separates a schedule error from an encoding or hash error.
`nonInteractiveFingerprint_matches_derived_keyDigest` goes one step further: the key digest that
opens the transcript is derived from the pinned key description (`Fixtures/PinnedKey.lean`), so
nothing in the Fiat–Shamir prefix is a captured value.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Circuits.Action (actionCircuit)

/-- The Action circuit's derived key at the captured URS, transported to the fixture shape. -/
def derivedVk : VerifyingKey shape Fp G :=
  Keygen.actionCircuitShape_eq_fixtureCircuitShape ▸ actionCircuit.toVerifierKey capturedURS

/-- **The fingerprint match at the derived verifying key.** The keygen certificate
(`Keygen.vk_eq_toVerifierKey`) rewrites the dumped key out of
`nonInteractiveFingerprint_matches`. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs (fun _ => capturedVkTranscriptRepr)
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  unfold derivedVk
  have h := Keygen.vk_eq_toVerifierKey
  rw [← h]
  exact nonInteractiveFingerprint_matches

/-- **The fingerprint match with the instance side also derived**: the commitments are the
circuit's commitment of the captured public inputs (`Keygen.instanceCommitment_capturedActionInputs`),
so both group-element families on the Lean side are derivations, not dump entries. -/
theorem nonInteractiveFingerprint_matches_derived_inputs :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs (fun _ => capturedVkTranscriptRepr)
        derivedVk
        (actionCircuit.instanceCommitment capturedURS Keygen.capturedActionInputs) ps)
      capturedMsm := by
  rw [Keygen.instanceCommitment_capturedActionInputs]
  exact nonInteractiveFingerprint_matches_derived

assert_no_sorry nonInteractiveFingerprint_matches_derived
assert_no_sorry nonInteractiveFingerprint_matches_derived_inputs

/-- **The fingerprint match at the derived key, from transcript bytes.** As
`nonInteractiveFingerprint_matches_derived`, with the captured oracle table replaced by the
deployed hash: every challenge is BLAKE2b over halo2's transcript encoding of the derived prefix
and the proof. -/
theorem nonInteractiveFingerprint_matches_derived_blake2b :
    MsmMatch
      (nonInteractiveFingerprintForStatement halo2Transcript (fun _ => capturedVkTranscriptRepr)
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  unfold derivedVk
  have h := Keygen.vk_eq_toVerifierKey
  rw [← h]
  exact nonInteractiveFingerprint_matches_blake2b

/-- **The strongest form**: derived key, derived instance commitments, and challenges from
transcript bytes. Nothing on the Lean side of the comparison is a dump entry or a captured
oracle value. -/
theorem nonInteractiveFingerprint_matches_derived_inputs_blake2b :
    MsmMatch
      (nonInteractiveFingerprintForStatement halo2Transcript (fun _ => capturedVkTranscriptRepr)
        derivedVk
        (actionCircuit.instanceCommitment capturedURS Keygen.capturedActionInputs) ps)
      capturedMsm := by
  rw [Keygen.instanceCommitment_capturedActionInputs]
  exact nonInteractiveFingerprint_matches_derived_blake2b

assert_no_sorry nonInteractiveFingerprint_matches_derived_blake2b
assert_no_sorry nonInteractiveFingerprint_matches_derived_inputs_blake2b

/-- **The fingerprint match with nothing captured in the Fiat–Shamir prefix.** As
`nonInteractiveFingerprint_matches_derived_blake2b`, with the key digest that opens the
transcript derived from the pinned key description (`keyDigest_eq_capturedVkTranscriptRepr`)
rather than taken from the capture. -/
theorem nonInteractiveFingerprint_matches_derived_keyDigest :
    MsmMatch
      (nonInteractiveFingerprintForStatement halo2Transcript
        (fun _ => keyDigest PinnedKey.pinnedKeyDescription)
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  rw [keyDigest_eq_capturedVkTranscriptRepr]
  exact nonInteractiveFingerprint_matches_derived_blake2b

/-- The strongest form with the derived digest: derived key, derived instance commitments,
challenges from transcript bytes, and a derived key digest opening the transcript. -/
theorem nonInteractiveFingerprint_matches_derived_inputs_keyDigest :
    MsmMatch
      (nonInteractiveFingerprintForStatement halo2Transcript
        (fun _ => keyDigest PinnedKey.pinnedKeyDescription)
        derivedVk
        (actionCircuit.instanceCommitment capturedURS Keygen.capturedActionInputs) ps)
      capturedMsm := by
  rw [Keygen.instanceCommitment_capturedActionInputs]
  exact nonInteractiveFingerprint_matches_derived_keyDigest

assert_no_sorry nonInteractiveFingerprint_matches_derived_keyDigest
assert_no_sorry nonInteractiveFingerprint_matches_derived_inputs_keyDigest

end Zcash.Snark.Fixture
