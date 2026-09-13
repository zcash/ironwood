import Zcash.Snark.ZeroKnowledge.StatefulRetry
import Zcash.Snark.ZeroKnowledge.OracleContinuation

/-!
# Finite simulation with state-dependent attempt laws

An attempt's error may depend on a bound on retained state size. Each retry can
increase that bound by a known amount. The proof compares continuations under
the real attempt law, so only its supported state-growth property is needed;
the simulator retains the same full history and final state.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Sum the successive comparison costs as the retained-state budget grows. -/
noncomputable def statefulRetryError (error : ℕ → ℝ≥0∞) (growth : ℕ) : ℕ → ℕ → ℝ≥0∞
  | _, 0 => 0
  | size, budget + 1 => error size + statefulRetryError error growth (size + growth) budget

/-- Changing a retry continuation preserves its bound while retaining the previous observation. -/
theorem statefulRetryNext_error_bound {A State : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {left right : State → PMF (RetryHistory A × State)}
    (observation : A × State) {error : ℝ≥0∞}
    (h : observation.1 ∈ retry → PMFEventBiasLE (left observation.2) (right observation.2) error) :
    PMFEventBiasLE (statefulRetryNext retry left observation) (statefulRetryNext retry right observation) error := by
  by_cases hretry : observation.1 ∈ retry
  · simpa only [statefulRetryNext, hretry, if_true] using
      eventBias_map (h hretry) (prependStatefulRetry observation.1)
  · simp only [statefulRetryNext, hretry, if_false]
    intro event
    exact le_self_add

/-- The retained histories and final states have a two-sided finite-budget comparison. -/
theorem statefulRetries_simulation_error_bound {A State : Type*}
    (actual ideal : State → PMF (A × State)) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (size : State → ℕ) (growth : ℕ)
    (error : ℕ → ℝ≥0∞)
    (hstep : ∀ bound state, size state ≤ bound →
      PMFEventBiasLE (actual state) (ideal state) (error bound) ∧
        PMFEventBiasLE (ideal state) (actual state) (error bound))
    (hgrowth : ∀ state observation, observation ∈ (actual state).support →
      size observation.2 ≤ size state + growth)
    (budget bound : ℕ) (state : State) (hsize : size state ≤ bound) :
    PMFEventBiasLE (statefulRetries actual retry budget state) (statefulRetries ideal retry budget state)
        (statefulRetryError error growth bound budget) ∧
      PMFEventBiasLE (statefulRetries ideal retry budget state) (statefulRetries actual retry budget state)
        (statefulRetryError error growth bound budget) := by
  induction budget generalizing bound state with
  | zero => constructor <;> intro event <;> simp [statefulRetries, statefulRetryError]
  | succ budget ih =>
    have hcontinuation (observation : A × State) (hobs : observation ∈ (actual state).support) :=
      ih (bound + growth) observation.2 ((hgrowth state observation hobs).trans (Nat.add_le_add_right hsize growth))
    have hf := eventBias_bind_support (actual state) (fun observation hobs =>
      statefulRetryNext_error_bound retry observation (fun _ => (hcontinuation observation hobs).1))
    have hr := eventBias_bind_support (actual state) (fun observation hobs =>
      statefulRetryNext_error_bound retry observation (fun _ => (hcontinuation observation hobs).2))
    have hsource := hstep bound state hsize
    have hsf := eventBias_bind_kernel hsource.1
      (statefulRetryNext retry (statefulRetries ideal retry budget))
    have hsr := eventBias_bind_kernel hsource.2
      (statefulRetryNext retry (statefulRetries ideal retry budget))
    exact ⟨hf.trans hsf, by simpa only [statefulRetries, statefulRetryError, add_comm] using hsr.trans hr⟩

end Zcash.Snark.ZeroKnowledge
