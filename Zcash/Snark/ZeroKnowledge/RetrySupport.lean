import Zcash.Snark.ZeroKnowledge.RetryTruncation

/-!
# Every supported unlimited history obeys the retry policy

Positive stopped-tape weight forces every preceding attempt to request a retry
and the last attempt to be terminal. Replaying the retained attempts therefore
returns the same nonempty, nonexhausted history.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open scoped ENNReal

/-- A positive retry-tape weight requires every entry to request another attempt. -/
theorem retryTapeWeight_mem {A : Type*} (law : PMF A) (retry : Set A) (count : ℕ) :
    ∀ tape, retryTapeWeight law retry count tape ≠ 0 → ∀ i, tape i ∈ retry := by
  classical
  induction count with
  | zero => intro tape h i; exact Fin.elim0 i
  | succ count ih =>
    intro tape h i
    have hhead : tape 0 ∈ retry := by
      by_contra hn
      exact h (by simp [retryTapeWeight, Set.indicator, hn])
    have htail : retryTapeWeight law retry count (Fin.tail tape) ≠ 0 := by
      intro hz
      exact h (by simp [retryTapeWeight, hz])
    exact Fin.cases hhead (fun j => ih (Fin.tail tape) htail j) i

/-- The positive-weight tape is exactly a sequence of retry requests followed by a terminal observation. -/
theorem stoppedRetryTapes_replay {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1)
    (tape : StoppedRetryTape A) (hs : tape ∈ (stoppedRetryTapes law retry hrate).support) :
    runRetryHistory retry (stoppedRetryTapeHistory tape).attempts = stoppedRetryTapeHistory tape := by
  classical
  change stoppedRetryWeight law retry tape ≠ 0 at hs
  have hw : retryTapeWeight law retry tape.1 tape.2.1 ≠ 0 := by
    intro hz
    exact hs (by simp [stoppedRetryWeight, hz])
  have hlast : tape.2.2 ∉ retry := by
    intro hl
    exact hs (by simp [stoppedRetryWeight, Set.indicator, hl])
  have hbefore : ∀ value ∈ List.ofFn tape.2.1, value ∈ retry := by
    intro value hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact retryTapeWeight_mem law retry tape.1 tape.2.1 hw i
  exact runRetryHistory_append_terminal retry _ _ hbefore hlast

/-- Supported unlimited histories are replay-stable, nonexhausted, and nonempty. -/
theorem unlimitedRetainedRetries_supported {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1)
    (history : RetryHistory A) (hs : history ∈ (unlimitedRetainedRetries law retry hrate).support) :
    runRetryHistory retry history.attempts = history ∧ history.exhausted = false ∧
      0 < history.attempts.length := by
  rw [unlimitedRetainedRetries, PMF.mem_support_map_iff] at hs
  obtain ⟨tape, ht, rfl⟩ := hs
  refine ⟨stoppedRetryTapes_replay law retry hrate tape ht, rfl, ?_⟩
  simp [stoppedRetryTapeHistory]

end Zcash.Snark.ZeroKnowledge
