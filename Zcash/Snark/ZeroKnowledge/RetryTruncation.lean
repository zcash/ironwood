import Zcash.Snark.ZeroKnowledge.RetryTape

/-!
# Finite observations of a stopped retry history

Truncation runs the same policy on the first requested number of attempts.
It reports exhaustion only when that prefix has not already stopped.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Replaying exactly the retained attempts reproduces the original policy result. -/
theorem runRetryHistory_idempotent {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape : List A) :
    runRetryHistory retry (runRetryHistory retry tape).attempts = runRetryHistory retry tape := by
  induction tape with
  | nil => rfl
  | cons value tape ih =>
    by_cases hv : value ∈ retry <;>
      simp [runRetryHistory, hv, RetryHistory.prepend, RetryHistory.stopped, ih]

/-- A sequence of retry requests stops at the following terminal observation. -/
theorem runRetryHistory_append_terminal {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape : List A) (terminal : A)
    (hbefore : ∀ value ∈ tape, value ∈ retry) (hterminal : terminal ∉ retry) :
    runRetryHistory retry (tape ++ [terminal]) = ⟨tape ++ [terminal], false⟩ := by
  induction tape with
  | nil => simp [runRetryHistory, hterminal, RetryHistory.stopped]
  | cons value tape ih =>
    have hv := hbefore value (by simp)
    have ht : ∀ v ∈ tape, v ∈ retry := fun v h => hbefore v (by simp [h])
    simp [runRetryHistory, hv, ih ht, RetryHistory.prepend]

/-- Observe at most `budget` of a history's attempts through the existing retry policy. -/
def truncateRetryHistory {A : Type*} (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (history : RetryHistory A) : RetryHistory A :=
  runRetryHistory retry (history.attempts.take budget)

/-- A zero budget always reports exhaustion before emitting any attempt. -/
theorem truncateRetryHistory_zero {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (history : RetryHistory A) :
    truncateRetryHistory retry 0 history = ⟨[], true⟩ := by
  simp [truncateRetryHistory, runRetryHistory]

/-- Truncation exposes the same first retry decision and continues with one less attempt. -/
theorem truncateRetryHistory_succ_prepend {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (value : A) (history : RetryHistory A) :
    truncateRetryHistory retry (budget + 1) (history.prepend value) =
      if value ∈ retry then (truncateRetryHistory retry budget history).prepend value
      else RetryHistory.stopped value := by
  simp [truncateRetryHistory, RetryHistory.prepend, runRetryHistory]

/-- Every positive budget retains a terminal first attempt and stops immediately. -/
theorem truncateRetryHistory_succ_stopped {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (value : A) (hvalue : value ∉ retry) :
    truncateRetryHistory retry (budget + 1) (RetryHistory.stopped value) =
      RetryHistory.stopped value := by
  simp [truncateRetryHistory, RetryHistory.stopped, runRetryHistory, hvalue]

/-- Truncating a replay-stable history beyond its length leaves the history unchanged. -/
theorem truncateRetryHistory_of_length_le {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (history : RetryHistory A)
    (hstable : runRetryHistory retry history.attempts = history) (hlength : history.attempts.length ≤ budget) :
    truncateRetryHistory retry budget history = history := by
  rw [truncateRetryHistory, List.take_of_length_le hlength, hstable]

/-- Once a truncated prefix stops, replay stability identifies it with the whole stopped history. -/
theorem truncateRetryHistory_eq_of_stopped {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (history : RetryHistory A)
    (hstable : runRetryHistory retry history.attempts = history)
    (hstop : (truncateRetryHistory retry budget history).exhausted = false) :
    truncateRetryHistory retry budget history = history := by
  have h := runRetryHistory_append_of_stopped retry (history.attempts.take budget)
    (history.attempts.drop budget) hstop
  rw [List.take_append_drop, hstable] at h
  exact h.symm

end Zcash.Snark.ZeroKnowledge
