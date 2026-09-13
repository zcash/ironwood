import Zcash.Common.Probability.Retry

/-!
# Independent retries with every attempt retained

Unlike `boundedRetries`, this experiment keeps the earlier failed observations.
Only membership in the supplied retry set requests another attempt; every other
outcome is terminal. An exhausted budget is represented explicitly. Each new
attempt uses the same law independently of the complete preceding history.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- All attempts in order, and whether another requested attempt exceeded the budget. -/
structure RetryHistory (A : Type*) where
  attempts : List A
  exhausted : Bool

/-- Preserve a preceding retry observation and the continuation's final status. -/
def RetryHistory.prepend {A : Type*} (a : A) (history : RetryHistory A) : RetryHistory A :=
  ⟨a :: history.attempts, history.exhausted⟩

/-- Stop immediately after an outcome which does not request a retry. -/
def RetryHistory.stopped {A : Type*} (a : A) : RetryHistory A := ⟨[a], false⟩

/-- Apply the actual observer to every retained attempt. -/
def RetryHistory.map {A B : Type*} (observe : A → B) (history : RetryHistory A) : RetryHistory B :=
  ⟨history.attempts.map observe, history.exhausted⟩

/-- Execute the retry policy on a finite tape of independently prepared attempts. -/
def runRetryHistory {A : Type*} (retry : Set A) [DecidablePred (fun a => a ∈ retry)] :
    List A → RetryHistory A
  | [] => ⟨[], true⟩
  | a :: rest =>
    if a ∈ retry then (runRetryHistory retry rest).prepend a else .stopped a

/-- The output contains exactly a prefix of the attempt tape, never a reordered history. -/
theorem runRetryHistory_prefix {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape : List A) :
    (runRetryHistory retry tape).attempts <+: tape := by
  induction tape with
  | nil => exact ⟨[], rfl⟩
  | cons a tape ih =>
    by_cases ha : a ∈ retry
    · obtain ⟨suffix, hs⟩ := ih
      exact ⟨suffix, by simp [runRetryHistory, ha, RetryHistory.prepend, hs]⟩
    · exact ⟨tape, by simp [runRetryHistory, ha, RetryHistory.stopped]⟩

/-- Exhaustion occurs precisely when every supplied outcome requested another attempt. -/
theorem runRetryHistory_exhausted_iff {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape : List A) :
    (runRetryHistory retry tape).exhausted = true ↔ ∀ a ∈ tape, a ∈ retry := by
  induction tape with
  | nil => simp [runRetryHistory]
  | cons a tape ih =>
    by_cases ha : a ∈ retry <;>
      simp [runRetryHistory, ha, RetryHistory.prepend, RetryHistory.stopped, ih]

/-- If every outcome requests a retry, the complete tape is retained with exhaustion. -/
theorem runRetryHistory_of_all_retry {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape : List A) (h : ∀ a ∈ tape, a ∈ retry) :
    runRetryHistory retry tape = ⟨tape, true⟩ := by
  induction tape with
  | nil => rfl
  | cons a tape ih =>
    have ha : a ∈ retry := h a (by simp)
    have ht : ∀ b ∈ tape, b ∈ retry := fun b hb => h b (by simp [hb])
    simp [runRetryHistory, ha, ih ht, RetryHistory.prepend]

/-- Once the policy stops, appending unused future attempts cannot change the history. -/
theorem runRetryHistory_append_of_stopped {A : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (tape later : List A)
    (h : (runRetryHistory retry tape).exhausted = false) :
    runRetryHistory retry (tape ++ later) = runRetryHistory retry tape := by
  induction tape with
  | nil => simp [runRetryHistory] at h
  | cons a tape ih =>
    by_cases ha : a ∈ retry
    · simp only [List.cons_append, runRetryHistory, if_pos ha]
      rw [ih (by simpa [runRetryHistory, ha, RetryHistory.prepend] using h)]
    · simp [runRetryHistory, ha]

/-- An observation that preserves retry decisions commutes with running the policy. -/
theorem runRetryHistory_map {A B : Type*} (retryA : Set A) (retryB : Set B)
    [DecidablePred (fun a => a ∈ retryA)] [DecidablePred (fun b => b ∈ retryB)]
    (observe : A → B) (h : ∀ a, observe a ∈ retryB ↔ a ∈ retryA) (tape : List A) :
    runRetryHistory retryB (tape.map observe) = (runRetryHistory retryA tape).map observe := by
  induction tape with
  | nil => rfl
  | cons a tape ih =>
    by_cases ha : a ∈ retryA
    · have hb := (h a).mpr ha
      simp [runRetryHistory, ha, hb, ih, RetryHistory.prepend, RetryHistory.map]
    · have hb : observe a ∉ retryB := fun hb => ha ((h a).mp hb)
      simp [runRetryHistory, ha, hb, RetryHistory.stopped, RetryHistory.map]

/-- One fresh attempt, retaining its value even when it requests the continuation. -/
noncomputable def retainedRetryStep {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : PMF (RetryHistory A)) : PMF (RetryHistory A) :=
  law.bind fun a =>
    if a ∈ retry then next.map (RetryHistory.prepend a) else PMF.pure (.stopped a)

/-- Run at most the given number of attempts, preserving all preceding retry observations. -/
noncomputable def retainedRetries {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] : ℕ → PMF (RetryHistory A)
  | 0 => PMF.pure ⟨[], true⟩
  | n + 1 => retainedRetryStep law retry (retainedRetries law retry n)

/-- The same independent law supplies every entry of the finite attempt tape. -/
noncomputable def retryAttemptTape {A : Type*} (law : PMF A) : ℕ → PMF (List A)
  | 0 => PMF.pure []
  | n + 1 => law.bind fun a => (retryAttemptTape law n).map (List.cons a)

/-- The probability experiment is the deterministic retry program run on that tape. -/
theorem retainedRetries_fromTape {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (n : ℕ) :
    (retryAttemptTape law n).map (runRetryHistory retry) = retainedRetries law retry n := by
  induction n with
  | zero => exact PMF.pure_map (runRetryHistory retry) []
  | succ n ih =>
    simp only [retryAttemptTape, PMF.map_bind, PMF.map_comp, Function.comp_def,
      retainedRetries, retainedRetryStep]
    congr 1
    funext a
    by_cases ha : a ∈ retry
    · simp only [runRetryHistory, if_pos ha]
      change (retryAttemptTape law n).map ((RetryHistory.prepend a) ∘ runRetryHistory retry) = _
      rw [← PMF.map_comp, ih]
    · simp only [runRetryHistory, if_neg ha]
      exact PMF.map_const _ _

/-- A retry step exhausts exactly when it retries and its continuation exhausts. -/
theorem retainedRetryStep_exhausted {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : PMF (RetryHistory A)) :
    (retainedRetryStep law retry next).toOuterMeasure {history | history.exhausted = true} =
      law.toOuterMeasure retry * next.toOuterMeasure {history | history.exhausted = true} := by
  classical
  rw [retainedRetryStep, PMF.toOuterMeasure_bind_apply, law.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ retry <;>
    simp [ha, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply,
      Set.indicator, RetryHistory.prepend, RetryHistory.stopped]

/-- Exhaustion has exactly the probability that all independent attempts request a retry. -/
theorem retainedRetries_exhausted {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (n : ℕ) :
    (retainedRetries law retry n).toOuterMeasure {history | history.exhausted = true} =
      law.toOuterMeasure retry ^ n := by
  induction n with
  | zero => simp [retainedRetries, PMF.toOuterMeasure_pure_apply]
  | succ n ih => rw [retainedRetries, retainedRetryStep_exhausted, ih, pow_succ']

end Zcash.Common.Probability
