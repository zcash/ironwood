import Zcash.Snark.ZeroKnowledge.StatefulRetryResources
import Zcash.Snark.ZeroKnowledge.CallerRetryPolicy
import Zcash.Snark.ZeroKnowledge.OracleCachePreservation
import Zcash.Snark.ZeroKnowledge.ProverAttempt

/-!
# Observed retry decisions and the retained oracle state

Only a terminal failure selected by the additional caller policy continues.
This caller is not part of the released Orchard proof call.
Completion, the coincident-opening error, and simulator programming failure all
stop. An observation always returns the cache to be used by any continuation;
programming failure returns the unchanged prior cache.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- The specified retry decision, with explicit simulator programming failure terminal. -/
def oracleRetryRequested : Option ProverAttemptResult → Bool
  | none => false
  | some attempt => callerRetryAfterFailure attempt.status

/-- The retry set has a computational decision procedure inherited from its Boolean predicate. -/
abbrev oracleRetrySet : Set (Option ProverAttemptResult) := {attempt | oracleRetryRequested attempt = true}

/-- Programming failure never requests another attempt. -/
theorem oracleRetryRequested_none : oracleRetryRequested none = false := rfl

/-- The auxiliary caller makes its decision from the attempt's terminal status. -/
theorem oracleRetryRequested_some (attempt : ProverAttemptResult) :
    oracleRetryRequested (some attempt) = true ↔ callerRetryAfterFailure attempt.status = true := by
  simp [oracleRetryRequested]

/-- Completed output is terminal, without asserting verifier acceptance. -/
theorem oracleRetryRequested_complete (proof : List UInt8) (received : List Zcash.Arithmetic.Fp) :
    oracleRetryRequested (some ⟨proof, received, .complete⟩) = false := by
  simp [oracleRetryRequested]

/-- A coincident-opening error is terminal even when earlier attempts requested fresh randomness. -/
theorem oracleRetryRequested_coincident (proof : List UInt8) (received : List Zcash.Arithmetic.Fp) :
    oracleRetryRequested (some ⟨proof, received, .failed .coincidentOpeningQueries⟩) = false := by
  simp [oracleRetryRequested]

/-- Separate the public attempt observation from its retained state, keeping the prior cache on failure. -/
def oracleAttemptState {Query Reply Attempt : Type*} (cache : OracleCache Query Reply)
    (observation : Option (Attempt × OracleCache Query Reply)) : Option Attempt × OracleCache Query Reply :=
  (observation.map Prod.fst, oracleAttemptCache cache observation)

/-- A programming failure exposes no attempt and keeps the previous cache exactly. -/
theorem oracleAttemptState_none {Query Reply Attempt : Type*} (cache : OracleCache Query Reply) :
    oracleAttemptState (Attempt := Attempt) cache none = (none, cache) := rfl

/-- An ordinary attempt carries its emitted prefix and returned cache into the retry policy. -/
theorem oracleAttemptState_some {Query Reply Attempt : Type*} (cache nextCache : OracleCache Query Reply)
    (attempt : Attempt) :
    oracleAttemptState cache (some (attempt, nextCache)) = (some attempt, nextCache) := rfl

/-- Expose an attempt kernel in the state-passing form required by retained retries. -/
noncomputable def oracleRetryTransition {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (cache : OracleCache Query Reply) : PMF (Option ProverAttemptResult × OracleCache Query Reply) :=
  (attempt cache).map (oracleAttemptState cache)

/-- The complete finite retry experiment retains every observed attempt and its final oracle cache. -/
noncomputable def oracleRetries {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (budget : ℕ) (cache : OracleCache Query Reply) :
    PMF (RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply) :=
  statefulRetries (oracleRetryTransition attempt) oracleRetrySet budget cache

end Zcash.Snark.ZeroKnowledge
