import Zcash.Snark.ZeroKnowledge.StatefulRetrySimulation

/-!
# Geometric comparison with a retained state

The simulator supplies the continuation probability in this hybrid. Its retry
bound is uniform in the retained state; the real process need not have
independent retry decisions, or even terminate almost surely. A state-dependent
potential pays the next comparison and the retry-weighted future comparisons.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Average bounds only on the support of the common outer experiment. -/
theorem eventBias_bind_average_support {A B : Type*} (law : PMF A)
    {actual ideal : A → PMF B} {cost : A → ℝ≥0∞}
    (h : ∀ value ∈ law.support, PMFEventBiasLE (actual value) (ideal value) (cost value)) :
    PMFEventBiasLE (law.bind actual) (law.bind ideal) (∑' value, law value * cost value) := by
  intro event
  simp only [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' value, law value * ((ideal value).toOuterMeasure event + cost value) := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hz : law value = 0
      · simp only [hz, zero_mul, le_refl]
      · exact mul_le_mul_right (h value hz event) _
    _ = _ := by simp only [mul_add, ENNReal.tsum_add]

/-- Retaining an attempt and its new state charges continuation error only on a retry. -/
theorem statefulRetryNext_average_error_bound {A State : Type*} (law : PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    {left right : State → PMF (RetryHistory A × State)} {error : ℝ≥0∞}
    (h : ∀ observation ∈ law.support, observation.1 ∈ retry →
      PMFEventBiasLE (left observation.2) (right observation.2) error) :
    PMFEventBiasLE (law.bind (statefulRetryNext retry left))
      (law.bind (statefulRetryNext retry right))
      (law.toOuterMeasure {observation | observation.1 ∈ retry} * error) := by
  have hmass : (∑' observation, law observation * (if observation.1 ∈ retry then error else 0)) =
      law.toOuterMeasure {observation | observation.1 ∈ retry} * error := by
    rw [law.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro observation
    by_cases hr : observation.1 ∈ retry <;> simp [hr, Set.indicator]
  rw [← hmass]
  apply eventBias_bind_average_support
  intro observation hs
  by_cases hr : observation.1 ∈ retry
  · simpa only [if_pos hr] using statefulRetryNext_error_bound retry observation (h observation hs)
  · simp only [statefulRetryNext, hr, if_false]
    intro event
    simp

/-- A state-dependent potential bounds every finite history, using only the simulator's retry rate. -/
theorem statefulRetries_potential_error_bound {A State : Type*}
    (actual ideal : State → PMF (A × State)) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (size : State → ℕ) (growth : ℕ)
    (error potential : ℕ → ℝ≥0∞) (rate : ℝ≥0∞)
    (hstep : ∀ bound state, size state ≤ bound →
      PMFEventBiasLE (actual state) (ideal state) (error bound) ∧
        PMFEventBiasLE (ideal state) (actual state) (error bound))
    (hgrowth : ∀ state observation, observation ∈ (ideal state).support →
      size observation.2 ≤ size state + growth)
    (hrate : ∀ state, (ideal state).toOuterMeasure {observation | observation.1 ∈ retry} ≤ rate)
    (hpotential : ∀ bound, error bound + rate * potential (bound + growth) ≤ potential bound)
    (budget bound : ℕ) (state : State) (hsize : size state ≤ bound) :
    PMFEventBiasLE (statefulRetries actual retry budget state) (statefulRetries ideal retry budget state)
        (potential bound) ∧
      PMFEventBiasLE (statefulRetries ideal retry budget state) (statefulRetries actual retry budget state)
        (potential bound) := by
  induction budget generalizing bound state with
  | zero => constructor <;> intro event <;> exact le_self_add
  | succ budget ih =>
    have hcontinuation (observation : A × State) (hs : observation ∈ (ideal state).support) :=
      ih (bound + growth) observation.2 ((hgrowth state observation hs).trans
        (Nat.add_le_add_right hsize growth))
    have hf := statefulRetryNext_average_error_bound (ideal state) retry
      (fun observation hs _ => (hcontinuation observation hs).1)
    have hr := statefulRetryNext_average_error_bound (ideal state) retry
      (fun observation hs _ => (hcontinuation observation hs).2)
    have hsource := hstep bound state hsize
    have hsf := eventBias_bind_kernel hsource.1
      (statefulRetryNext retry (statefulRetries actual retry budget))
    have hsr := eventBias_bind_kernel hsource.2
      (statefulRetryNext retry (statefulRetries actual retry budget))
    have hcost := (add_le_add le_rfl
      (mul_le_mul_left (hrate state) (potential (bound + growth)))).trans (hpotential bound)
    constructor
    · intro event
      have h := (hsf.trans hf) event
      exact h.trans (add_le_add le_rfl (by simpa only [add_comm] using hcost))
    · intro event
      exact ((hr.trans hsr) event).trans (add_le_add le_rfl hcost)

/-- The simulator's state-uniform retry bound gives a geometric exhaustion tail. -/
theorem statefulRetries_exhaustion_le {A State : Type*}
    (attempt : State → PMF (A × State)) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (rate : ℝ≥0∞)
    (hrate : ∀ state, (attempt state).toOuterMeasure {observation | observation.1 ∈ retry} ≤ rate)
    (budget : ℕ) (state : State) :
    (statefulRetries attempt retry budget state).toOuterMeasure
      {output | output.1.exhausted = true} ≤ rate ^ budget := by
  induction budget generalizing state with
  | zero => simp [statefulRetries]
  | succ budget ih =>
    rw [statefulRetries, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' observation, attempt state observation *
          (if observation.1 ∈ retry then rate ^ budget else 0) := by
        apply ENNReal.tsum_le_tsum
        intro observation
        apply mul_le_mul_right
        by_cases hr : observation.1 ∈ retry
        · simpa only [statefulRetryNext, hr, if_true, PMF.toOuterMeasure_map_apply,
            Set.preimage_setOf_eq, prependStatefulRetry, RetryHistory.prepend] using ih observation.2
        · simp [statefulRetryNext, hr, RetryHistory.stopped]
      _ = (attempt state).toOuterMeasure {observation | observation.1 ∈ retry} * rate ^ budget := by
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro observation
        by_cases hr : observation.1 ∈ retry <;> simp [hr, Set.indicator]
      _ ≤ rate * rate ^ budget := mul_le_mul_left (hrate state) _
      _ = rate ^ (budget + 1) := (pow_succ' rate budget).symm

end Zcash.Snark.ZeroKnowledge
