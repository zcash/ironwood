import Zcash.Snark.Fixtures.SingleAction.Random.FiatShamir
import Zcash.Snark.Verifier.KeyDigest
import Zcash.Snark.Verifier.Transcript

/-!
# Byte-level Fiat–Shamir check for the random single-action capture

`FiatShamir.lean` reaches the captured challenges through `capturedFs`, a table returning each
captured challenge at its captured typed prefix. This module reaches them with no table at all:
`halo2Transcript` recomputes every squeeze from the transcript bytes — the tagged encoding of the
typed prefix, BLAKE2b-512 personalized `Halo2-Transcript`, the digest reduced modulo `p` — and
`deriveChallenges_matches_blake2b` states that the deployed schedule run through it yields exactly
the captured `ch`. The captured-table route stays as the diagnostic that separates a schedule
error from an encoding or hash error.

`Fixture.lean` carries the exact compact pinned-key string alongside the transcript scalar, typed
proof, and challenges. Lean hashes that string and recomputes the challenges instead of trusting
the captured scalar or challenge table; the string and typed capture remain exporter inputs. On
this match-only capture the proof elements are random canonical values, so the recomputation
exercises the encoding on generic inputs rather than on a prover's structured ones.
-/

namespace Zcash.Snark.FixtureRandom

open Zcash.Snark

/-- Every captured squeeze, recomputed from bytes at its captured prefix, is the captured value:
the byte layer agrees with the capture squeeze by squeeze, independently of the schedule. -/
theorem markerSchedule_matches_blake2b :
    markerScheduleEntries.all (fun e => decide (halo2Transcript.squeeze e.1 = e.2)) = true := by
  native_decide

/-- **The deployed byte-level schedule reaches the captured challenges.** Running the typed
schedule through BLAKE2b over halo2's transcript encoding reproduces all 22 captured challenges. -/
theorem deriveChallenges_matches_blake2b :
    deriveChallenges halo2Transcript capturedInit ps = ch := by
  native_decide

/-- The statement-bound entry point reaches the captured challenges from bytes. -/
theorem deriveChallengesForStatement_matches_blake2b :
    deriveChallengesForStatement halo2Transcript capturedVkTranscriptRepr
      derivedInstanceCommitment ps = ch := by
  rw [deriveChallengesForStatement, ← capturedInit_eq_initialTranscript]
  exact deriveChallenges_matches_blake2b

/-- The captured key digest is the digest of the exact pinned-key string the exporter hashed. -/
theorem keyDigest_eq_capturedVkTranscriptRepr :
    keyDigest capturedPinnedKeyDescription = capturedVkTranscriptRepr := by
  native_decide

/-- The fingerprint match with every challenge recomputed from transcript bytes. -/
theorem nonInteractiveFingerprint_matches_blake2b :
    MsmMatch (nonInteractiveFingerprintForStatement halo2Transcript
      (fun _ => capturedVkTranscriptRepr) vk derivedInstanceCommitment ps) capturedMsm := by
  unfold nonInteractiveFingerprintForStatement
  rw [deriveChallengesForStatement_matches_blake2b]
  exact fingerprint_matches

end Zcash.Snark.FixtureRandom
