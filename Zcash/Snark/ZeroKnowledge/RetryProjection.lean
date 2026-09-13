import Zcash.Snark.ZeroKnowledge.RetryFlow
import Zcash.Snark.ZeroKnowledge.RetrySupport

/-!
# Exact finite observations of the unlimited retry law

Observing the first `budget` attempts of the normalized stopped-history law is
exactly the existing finite-budget policy on independent attempt tapes.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open scoped ENNReal

/-- Every finite truncation has exactly the independently executed finite-budget law. -/
theorem unlimitedRetainedRetries_truncate {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1) (budget : ℕ) :
    (unlimitedRetainedRetries law retry hrate).map (truncateRetryHistory retry budget) =
      retainedRetries law retry budget := by
  induction budget with
  | zero =>
    simpa only [truncateRetryHistory_zero, retainedRetries] using
      PMF.map_const (unlimitedRetainedRetries law retry hrate) (⟨[], true⟩ : RetryHistory A)
  | succ budget ih =>
    rw [unlimitedRetainedRetries_renewal law retry hrate, retainedRetryStep, PMF.map_bind]
    change law.bind _ = law.bind _
    congr 1
    funext value
    by_cases hv : value ∈ retry
    · simp only [if_pos hv, PMF.map_comp, Function.comp_def,
        truncateRetryHistory_succ_prepend]
      change (unlimitedRetainedRetries law retry hrate).map
        ((RetryHistory.prepend value) ∘ truncateRetryHistory retry budget) = _
      rw [← PMF.map_comp, ih]
    · simp only [if_neg hv, PMF.pure_map, truncateRetryHistory_succ_stopped retry budget value hv]

/-- Under a complete stopped law, finite-budget exhaustion is exactly an unobserved later attempt. -/
theorem unlimitedRetainedRetries_truncate_exhausted_iff {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1)
    (budget : ℕ) (history : RetryHistory A)
    (hs : history ∈ (unlimitedRetainedRetries law retry hrate).support) :
    (truncateRetryHistory retry budget history).exhausted = true ↔ budget < history.attempts.length := by
  obtain ⟨hstable, hstop, _⟩ := unlimitedRetainedRetries_supported law retry hrate history hs
  constructor
  · intro he
    by_contra hn
    have ht := truncateRetryHistory_of_length_le retry budget history hstable (Nat.le_of_not_gt hn)
    rw [ht, hstop] at he
    contradiction
  · intro hl
    by_contra hn
    have he : (truncateRetryHistory retry budget history).exhausted = false := by
      cases h : (truncateRetryHistory retry budget history).exhausted <;> simp_all
    have ht := truncateRetryHistory_eq_of_stopped retry budget history hstable he
    have hlen := (runRetryHistory_prefix retry (history.attempts.take budget)).length_le
    change (truncateRetryHistory retry budget history).attempts.length ≤ _ at hlen
    rw [ht] at hlen
    exact (Nat.not_le_of_gt hl) (hlen.trans (List.length_take_le budget history.attempts))

/-- The complete history has the exact geometric tail for its number of attempts. -/
theorem unlimitedRetainedRetries_length_tail {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1) (budget : ℕ) :
    (unlimitedRetainedRetries law retry hrate).toOuterMeasure
      {history | budget < history.attempts.length} = law.toOuterMeasure retry ^ budget := by
  rw [← retainedRetries_exhausted law retry budget, ← unlimitedRetainedRetries_truncate law retry hrate,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext history
  constructor
  · intro ⟨hl, hs⟩
    exact ⟨(unlimitedRetainedRetries_truncate_exhausted_iff law retry hrate budget history hs).mpr hl, hs⟩
  · intro ⟨he, hs⟩
    exact ⟨(unlimitedRetainedRetries_truncate_exhausted_iff law retry hrate budget history hs).mp he, hs⟩

end Zcash.Snark.ZeroKnowledge
