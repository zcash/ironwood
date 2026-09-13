import Zcash.Snark.ZeroKnowledge.OracleRetry
import Zcash.Snark.ZeroKnowledge.StatefulRetrySimulation

/-!
# Shared-oracle retained-history composition

This theorem carries a cache-dependent one-attempt comparison through the
actual retry policy. Cache growth controls the subsequent comparison costs;
no fresh-oracle or independent-failure assumption is introduced.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- A cache-size-dependent attempt bound composes through finite retries retaining all observations and state. -/
theorem oracleRetries_simulation_error_bound {Query Reply : Type*}
    (actual ideal : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (growth : ℕ) (error : ℕ → ℝ≥0∞)
    (hstep : ∀ bound cache, cache.length ≤ bound →
      PMFEventBiasLE (actual cache) (ideal cache) (error bound) ∧
        PMFEventBiasLE (ideal cache) (actual cache) (error bound))
    (hgrowth : ∀ cache observation, observation ∈ (actual cache).support →
      (oracleAttemptCache cache observation).length ≤ cache.length + growth)
    (budget bound : ℕ) (cache : OracleCache Query Reply) (hcache : cache.length ≤ bound) :
    PMFEventBiasLE (oracleRetries actual budget cache) (oracleRetries ideal budget cache)
        (statefulRetryError error growth bound budget) ∧
      PMFEventBiasLE (oracleRetries ideal budget cache) (oracleRetries actual budget cache)
        (statefulRetryError error growth bound budget) := by
  apply statefulRetries_simulation_error_bound
    (oracleRetryTransition actual) (oracleRetryTransition ideal) oracleRetrySet List.length growth error
  · intro bound cache hcache
    have h := hstep bound cache hcache
    exact ⟨eventBias_map h.1 (oracleAttemptState cache), eventBias_map h.2 (oracleAttemptState cache)⟩
  · intro cache observation hobs
    rw [oracleRetryTransition, PMF.mem_support_map_iff] at hobs
    obtain ⟨raw, hraw, rfl⟩ := hobs
    exact hgrowth cache raw hraw
  · exact hcache

end Zcash.Snark.ZeroKnowledge
