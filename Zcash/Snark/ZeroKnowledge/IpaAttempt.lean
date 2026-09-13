import Zcash.Snark.ZeroKnowledge.IpaFresh

/-!
# The visible IPA attempt, including partial output and terminal failures

The point codec can fail before appending any bytes. Each round writes its left point,
then its right point, then receives a challenge and stops with a panic if it is
zero. The final two scalars are emitted only after all rounds succeed. This is
the `write_point` / inverse-unwrap order in the Common release recorded in
`Zakura/PROVENANCE.md`. The observer never requests a retry.

Codecs are supplied parameters. The distribution theorem covers their complete output,
including errors, but does not certify a concrete Rust codec or Fiat–Shamir hash state.
The recorded prefix is a stronger observation than a caller that discards it on error.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The IPA either completes, fails to encode a point, or panics on a zero round challenge. -/
inductive IpaAttemptStatus where
  | complete
  | identityPoint
  | zeroChallengePanic
  deriving DecidableEq

/-- Retain emitted bytes, received challenges, and the result, even when the attempt fails. -/
structure IpaAttemptResult where
  proof : List UInt8
  received : List Fp
  status : IpaAttemptStatus

/-- Observe the rounds in order, stopping immediately at a failed point encoding or zero challenge. -/
def observeIpaRounds {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (c f : Fp) : List (Fp × G × G) → IpaAttemptResult
  | [] => ⟨scalarCodec c ++ scalarCodec f, [], .complete⟩
  | (challenge, left, right) :: rounds =>
    match pointCodec left with
    | none => ⟨[], [], .identityPoint⟩
    | some leftBytes =>
      match pointCodec right with
      | none => ⟨leftBytes, [], .identityPoint⟩
      | some rightBytes =>
        if challenge = 0 then ⟨leftBytes ++ rightBytes, [challenge], .zeroChallengePanic⟩
        else
          let rest := observeIpaRounds pointCodec scalarCodec c f rounds
          ⟨leftBytes ++ rightBytes ++ rest.proof, challenge :: rest.received, rest.status⟩

/-- Start with the mask commitment, receive `xi` and `z`, and observe the computed IPA rounds. -/
def observeIpaAttempt {k : ℕ} {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (view : IpaFreshView k G) : IpaAttemptResult :=
  match pointCodec view.2.maskCommitment with
  | none => ⟨[], [], .identityPoint⟩
  | some maskBytes =>
    let rest := observeIpaRounds pointCodec scalarCodec view.2.scalar view.2.blind
      (List.ofFn fun j => (view.1 j.succ.succ, view.2.messages j))
    ⟨maskBytes ++ rest.proof, view.1 0 :: view.1 1 :: rest.received, rest.status⟩

/-- Keep the verifier's entire private tape as well as its visible interaction with the prover. -/
def ipaAttemptObservation {k : ℕ} {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (view : IpaFreshView k G) :
    IpaChallengeTape k Fp × IpaAttemptResult :=
  (view.1, observeIpaAttempt pointCodec scalarCodec view)

/-- Failure to encode `S` emits no IPA bytes and receives no IPA challenges. -/
theorem observeIpaAttempt_mask_failure {k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : IpaFreshView k G) (h : pointCodec view.2.maskCommitment = none) :
    observeIpaAttempt pointCodec scalarCodec view = ⟨[], [], .identityPoint⟩ := by
  simp [observeIpaAttempt, h]

/-- A failed right-point encoding retains the left bytes and has not received the round challenge. -/
theorem observeIpaRounds_right_failure {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (c f challenge : Fp) (left right : G)
    (rounds : List (Fp × G × G)) (leftBytes : List UInt8)
    (hleft : pointCodec left = some leftBytes) (hright : pointCodec right = none) :
    observeIpaRounds pointCodec scalarCodec c f ((challenge, left, right) :: rounds) =
      ⟨leftBytes, [], .identityPoint⟩ := by
  simp [observeIpaRounds, hleft, hright]

/-- A zero round challenge is checked after both point writes and before any later output. -/
theorem observeIpaRounds_zero_challenge {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (c f : Fp) (left right : G)
    (rounds : List (Fp × G × G)) (leftBytes rightBytes : List UInt8)
    (hleft : pointCodec left = some leftBytes) (hright : pointCodec right = some rightBytes) :
    observeIpaRounds pointCodec scalarCodec c f ((0, left, right) :: rounds) =
      ⟨leftBytes ++ rightBytes, [0], .zeroChallengePanic⟩ := by
  simp [observeIpaRounds, hleft, hright]

section Distribution

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Any supplied codecs preserve the complete joint simulation bound, including failed attempts.

The theorem compares unconditioned laws. No successful-attempt normalization or repeated
retry loop is hidden in this observation function. -/
theorem observedIpa_simulation_error_bound {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    PMFEventBiasLE
        ((freshSampledIpaProver law pub coefficients rho).map (ipaAttemptObservation pointCodec scalarCodec))
        ((freshIpaSimulator law pub).map (ipaAttemptObservation pointCodec scalarCodec))
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} +
          ipaSampleCount k * challenge255Bias) ∧
      PMFEventBiasLE
        ((freshIpaSimulator law pub).map (ipaAttemptObservation pointCodec scalarCodec))
        ((freshSampledIpaProver law pub coefficients rho).map (ipaAttemptObservation pointCodec scalarCodec))
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} +
          ipaSampleCount k * challenge255Bias) := by
  have h := freshIpa_simulation_error_bound law pub coefficients rho hW hcommit hv
  exact ⟨eventBias_map h.1 _, eventBias_map h.2 _⟩

/-- The concrete interactive bound survives partial serialization and `RetryRandomness`.

Both the private prover coins and the independent verifier coins use wide reduction.
The bound is `12/p + 47 × bias` for the pinned eleven-round IPA stage. -/
theorem wideObservedIpa_simulation_error_bound {k : ℕ}
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    PMFEventBiasLE
        ((freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho).map
          (ipaAttemptObservation pointCodec scalarCodec))
        ((freshIpaSimulator (wideIpaChallenges k) pub).map (ipaAttemptObservation pointCodec scalarCodec))
        (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE
        ((freshIpaSimulator (wideIpaChallenges k) pub).map (ipaAttemptObservation pointCodec scalarCodec))
        ((freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho).map
          (ipaAttemptObservation pointCodec scalarCodec))
        (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := wideFreshIpa_simulation_error_bound pub coefficients rho hW hcommit hv
  exact ⟨eventBias_map h.1 _, eventBias_map h.2 _⟩

end Distribution

end Zcash.Snark.ZeroKnowledge
