import Zcash.Snark.ZeroKnowledge.OracleRetry

/-!
# Cache resources and persistent answers across oracle retries

The final cache grows by at most the per-attempt budget times the number of
attempts actually retained. Every previously stored answer survives the entire
execution when it survives each supported attempt.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Lift an attempt's cache-growth bound through its public observation adapter. -/
theorem oracleRetryTransition_growth {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (growth : ℕ)
    (hstep : ∀ cache observation, observation ∈ (attempt cache).support →
      (oracleAttemptCache cache observation).length ≤ cache.length + growth)
    (cache : OracleCache Query Reply) (observation : Option ProverAttemptResult × OracleCache Query Reply)
    (hobs : observation ∈ (oracleRetryTransition attempt cache).support) :
    observation.2.length ≤ cache.length + growth := by
  rw [oracleRetryTransition, PMF.mem_support_map_iff] at hobs
  obtain ⟨raw, hraw, rfl⟩ := hobs
  exact hstep cache raw hraw

/-- The retained history follows the exact stop/exhaustion policy on its observed attempts. -/
theorem oracleRetries_policy {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (budget : ℕ) (cache : OracleCache Query Reply)
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply)
    (houtput : output ∈ (oracleRetries attempt budget cache).support) :
    runRetryHistory oracleRetrySet output.1.attempts = output.1 :=
  statefulRetries_policy _ _ budget cache output houtput

/-- Histories, exhaustion, and cache growth obey the actual number of retained attempts. -/
theorem oracleRetries_resources {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (growth : ℕ)
    (hstep : ∀ cache observation, observation ∈ (attempt cache).support →
      (oracleAttemptCache cache observation).length ≤ cache.length + growth)
    (budget : ℕ) (cache : OracleCache Query Reply)
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply)
    (houtput : output ∈ (oracleRetries attempt budget cache).support) :
    output.1.attempts.length ≤ budget ∧
      (output.1.exhausted = true → output.1.attempts.length = budget) ∧
      output.2.length ≤ cache.length + growth * output.1.attempts.length :=
  statefulRetries_resources _ oracleRetrySet List.length growth
    (oracleRetryTransition_growth attempt growth hstep) budget cache output houtput

/-- The finite attempt budget gives a uniform bound on the final oracle table. -/
theorem oracleRetries_cache_length_le {Query Reply : Type*}
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (growth : ℕ)
    (hstep : ∀ cache observation, observation ∈ (attempt cache).support →
      (oracleAttemptCache cache observation).length ≤ cache.length + growth)
    (budget : ℕ) (cache : OracleCache Query Reply)
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply)
    (houtput : output ∈ (oracleRetries attempt budget cache).support) :
    output.2.length ≤ cache.length + growth * budget :=
  statefulRetries_state_size_le _ oracleRetrySet List.length growth
    (oracleRetryTransition_growth attempt growth hstep) budget cache output houtput

/-- Every previously stored answer survives all supported retry transitions, including explicit programming failure. -/
theorem oracleRetries_keeps {Query Reply : Type*} [DecidableEq Query]
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (hstep : ∀ cache observation, observation ∈ (attempt cache).support →
      ∀ query reply, oracleCacheLookup cache query = some reply →
        oracleCacheLookup (oracleAttemptCache cache observation) query = some reply)
    (budget : ℕ) (cache : OracleCache Query Reply)
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply)
    (houtput : output ∈ (oracleRetries attempt budget cache).support)
    (query : Query) (reply : Reply) (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup output.2 query = some reply := by
  apply statefulRetries_invariant (oracleRetryTransition attempt) oracleRetrySet
    (fun cache => oracleCacheLookup cache query = some reply) _ budget cache hstored output houtput
  intro cache hcache observation hobs
  rw [oracleRetryTransition, PMF.mem_support_map_iff] at hobs
  obtain ⟨raw, hraw, rfl⟩ := hobs
  exact hstep cache raw hraw query reply hcache

/-- Every supported independent attempt-tape list has exactly the requested length. -/
theorem retryAttemptTape_support_length {Tape : Type*} (tapeLaw : PMF Tape) (budget : ℕ)
    (tapes : List Tape) (htapes : tapes ∈ (retryAttemptTape tapeLaw budget).support) :
    tapes.length = budget := by
  induction budget generalizing tapes with
  | zero =>
    rw [retryAttemptTape, PMF.mem_support_pure_iff] at htapes
    subst tapes
    rfl
  | succ budget ih =>
    rw [retryAttemptTape, PMF.mem_support_bind_iff] at htapes
    obtain ⟨tape, _, htapes⟩ := htapes
    rw [PMF.mem_support_map_iff] at htapes
    obtain ⟨later, hlater, rfl⟩ := htapes
    simpa only [List.length_cons] using congrArg Nat.succ (ih later hlater)

end Zcash.Snark.ZeroKnowledge
