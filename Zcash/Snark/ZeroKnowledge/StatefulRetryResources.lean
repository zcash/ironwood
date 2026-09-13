import Zcash.Snark.ZeroKnowledge.StatefulRetry

/-!
# Retained-history policy and state-growth bounds

Every supported execution follows the stated retry policy. The retained history
has at most the attempt budget, exhaustion uses the entire budget, and final
state growth is bounded by the number of attempts actually observed.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Any invariant preserved by one supported transition is preserved through the full retry history. -/
theorem statefulRetries_invariant {A State : Type*} (attempt : State → PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (invariant : State → Prop)
    (hstep : ∀ state, invariant state → ∀ observation, observation ∈ (attempt state).support →
      invariant observation.2)
    (budget : ℕ) (state : State) (hstate : invariant state) (output : RetryHistory A × State)
    (houtput : output ∈ (statefulRetries attempt retry budget state).support) :
    invariant output.2 := by
  induction budget generalizing state output with
  | zero =>
    rw [statefulRetries, PMF.mem_support_pure_iff] at houtput
    subst output
    exact hstate
  | succ budget ih =>
    rw [statefulRetries, PMF.mem_support_bind_iff] at houtput
    obtain ⟨observation, hobs, houtput⟩ := houtput
    have hnext := hstep state hstate observation hobs
    by_cases hretry : observation.1 ∈ retry
    · rw [statefulRetryNext, if_pos hretry, PMF.mem_support_map_iff] at houtput
      obtain ⟨later, hlater, rfl⟩ := houtput
      exact ih observation.2 hnext later hlater
    · rw [statefulRetryNext, if_neg hretry, PMF.mem_support_pure_iff] at houtput
      subst output
      exact hnext

/-- Retrying the observed history itself reproduces its exact stop or exhaustion status. -/
theorem statefulRetries_policy {A State : Type*} (attempt : State → PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (state : State)
    (output : RetryHistory A × State) (houtput : output ∈ (statefulRetries attempt retry budget state).support) :
    runRetryHistory retry output.1.attempts = output.1 := by
  induction budget generalizing state output with
  | zero =>
    rw [statefulRetries, PMF.mem_support_pure_iff] at houtput
    subst output
    rfl
  | succ budget ih =>
    rw [statefulRetries, PMF.mem_support_bind_iff] at houtput
    obtain ⟨observation, _, houtput⟩ := houtput
    by_cases hretry : observation.1 ∈ retry
    · rw [statefulRetryNext, if_pos hretry, PMF.mem_support_map_iff] at houtput
      obtain ⟨later, hlater, rfl⟩ := houtput
      simpa only [prependStatefulRetry, RetryHistory.prepend, runRetryHistory, hretry, if_true] using
        congrArg (RetryHistory.prepend observation.1) (ih observation.2 later hlater)
    · rw [statefulRetryNext, if_neg hretry, PMF.mem_support_pure_iff] at houtput
      subst output
      simp [RetryHistory.stopped, runRetryHistory, hretry]

/-- Every supported execution obeys its history length, exhaustion, and per-attempt growth budgets. -/
theorem statefulRetries_resources {A State : Type*} (attempt : State → PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (size : State → ℕ) (growth : ℕ)
    (hstep : ∀ state observation, observation ∈ (attempt state).support →
      size observation.2 ≤ size state + growth)
    (budget : ℕ) (state : State) (output : RetryHistory A × State)
    (houtput : output ∈ (statefulRetries attempt retry budget state).support) :
    output.1.attempts.length ≤ budget ∧
      (output.1.exhausted = true → output.1.attempts.length = budget) ∧
      size output.2 ≤ size state + growth * output.1.attempts.length := by
  induction budget generalizing state output with
  | zero =>
    rw [statefulRetries, PMF.mem_support_pure_iff] at houtput
    subst output
    simp
  | succ budget ih =>
    rw [statefulRetries, PMF.mem_support_bind_iff] at houtput
    obtain ⟨observation, hobs, houtput⟩ := houtput
    have hgrowth := hstep state observation hobs
    by_cases hretry : observation.1 ∈ retry
    · rw [statefulRetryNext, if_pos hretry, PMF.mem_support_map_iff] at houtput
      obtain ⟨later, hlater, rfl⟩ := houtput
      obtain ⟨hlength, hexhausted, hsize⟩ := ih observation.2 later hlater
      dsimp only [prependStatefulRetry, RetryHistory.prepend]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      exact ⟨by omega, fun h => by rw [hexhausted h], by omega⟩
    · rw [statefulRetryNext, if_neg hretry, PMF.mem_support_pure_iff] at houtput
      subst output
      simpa only [RetryHistory.stopped, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.mul_one, Bool.false_eq_true, false_implies, and_true, true_and] using
        And.intro (show 1 ≤ budget + 1 by omega) hgrowth

/-- The final state also satisfies the uniform budget obtained from the maximum attempt count. -/
theorem statefulRetries_state_size_le {A State : Type*} (attempt : State → PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (size : State → ℕ) (growth : ℕ)
    (hstep : ∀ state observation, observation ∈ (attempt state).support →
      size observation.2 ≤ size state + growth)
    (budget : ℕ) (state : State) (output : RetryHistory A × State)
    (houtput : output ∈ (statefulRetries attempt retry budget state).support) :
    size output.2 ≤ size state + growth * budget := by
  have h := statefulRetries_resources attempt retry size growth hstep budget state output houtput
  exact h.2.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left growth h.1) (size state))

end Zcash.Snark.ZeroKnowledge
