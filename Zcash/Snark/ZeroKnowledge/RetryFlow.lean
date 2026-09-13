import Zcash.Snark.ZeroKnowledge.RetryTape

/-!
# The renewal equation for complete stopped retry tapes

The normalized tape law follows the actual policy: one fresh attempt either
stops, or its complete observation is prepended to an independent continuation.
This connects the countable sum of stopped tapes to an executable retry step.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Prepend one additional retry observation to a stopped tape. -/
def stoppedRetryTapePrepend {A : Type*} (value : A) (tape : StoppedRetryTape A) : StoppedRetryTape A :=
  ⟨tape.1 + 1, Fin.cons value tape.2.1, tape.2.2⟩

/-- Observing a prepended tape preserves the same ordered history. -/
theorem stoppedRetryTapeHistory_prepend {A : Type*} (value : A) (tape : StoppedRetryTape A) :
    stoppedRetryTapeHistory (stoppedRetryTapePrepend value tape) =
      (stoppedRetryTapeHistory tape).prepend value := by
  rcases tape with ⟨count, tape, terminal⟩
  simp [stoppedRetryTapeHistory, stoppedRetryTapePrepend, RetryHistory.prepend, List.ofFn_succ]

/-- Split a sum over stopped tapes into immediate termination and one retained retry. -/
theorem stoppedRetryWeight_renewal {A : Type*} (law : PMF A) (retry : Set A)
    (test : StoppedRetryTape A → ℝ≥0∞) :
    (∑' tape, stoppedRetryWeight law retry tape * test tape) =
      (∑' value, retryᶜ.indicator law value * test ⟨0, Fin.elim0, value⟩) +
        ∑' value, retry.indicator law value *
          ∑' tape, stoppedRetryWeight law retry tape * test (stoppedRetryTapePrepend value tape) := by
  let family (count : ℕ) := ∑' pair : (Fin count → A) × A,
    stoppedRetryWeight law retry ⟨count, pair⟩ * test ⟨count, pair⟩
  let next (value : A) (count : ℕ) := ∑' pair : (Fin count → A) × A,
    stoppedRetryWeight law retry ⟨count, pair⟩ * test (stoppedRetryTapePrepend value ⟨count, pair⟩)
  have hz : family 0 = ∑' value, retryᶜ.indicator law value * test ⟨0, Fin.elim0, value⟩ := by
    dsimp only [family]
    rw [ENNReal.tsum_prod']
    rw [tsum_eq_single Fin.elim0 (fun tape h => (h (funext fun i => Fin.elim0 i)).elim)]
    simp only [stoppedRetryWeight, retryTapeWeight, one_mul]
  have hs (count : ℕ) : family (count + 1) = ∑' value, retry.indicator law value * next value count := by
    let e := Fin.consEquiv (fun _ : Fin (count + 1) => A)
    dsimp only [family]
    rw [ENNReal.tsum_prod']
    rw [← e.tsum_eq]
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro value
    dsimp only [next]
    rw [ENNReal.tsum_prod']
    change (∑' tape : Fin count → A, ∑' terminal : A,
      stoppedRetryWeight law retry ⟨count + 1, Fin.cons value tape, terminal⟩ *
        test ⟨count + 1, Fin.cons value tape, terminal⟩) =
      retry.indicator law value * ∑' tape : Fin count → A, ∑' terminal : A,
        stoppedRetryWeight law retry ⟨count, tape, terminal⟩ *
          test (stoppedRetryTapePrepend value ⟨count, tape, terminal⟩)
    simp only [stoppedRetryWeight, retryTapeWeight, stoppedRetryTapePrepend,
      Fin.cons_zero, Fin.tail_cons, mul_assoc, ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_sigma', tsum_eq_zero_add' ENNReal.summable]
  change family 0 + (∑' count, family (count + 1)) = _
  rw [hz]
  congr 1
  simp_rw [hs]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro value
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_sigma']

/-- A deterministic observation of the unlimited law has the specified stopped-tape weights. -/
theorem unlimitedRetainedRetries_map_apply {A B : Type*} (law : PMF A) (retry : Set A)
    (hrate : law.toOuterMeasure retry < 1) (observe : RetryHistory A → B) (value : B) :
    ((unlimitedRetainedRetries law retry hrate).map observe) value =
      ∑' tape, stoppedRetryWeight law retry tape *
        (PMF.pure (observe (stoppedRetryTapeHistory tape))) value := by
  rw [unlimitedRetainedRetries, PMF.map_comp]
  rfl

/-- The countable stopped-tape construction obeys the actual one-step retry policy. -/
theorem unlimitedRetainedRetries_renewal {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1) :
    unlimitedRetainedRetries law retry hrate =
      retainedRetryStep law retry (unlimitedRetainedRetries law retry hrate) := by
  classical
  apply PMF.ext
  intro history
  change (∑' tape, stoppedRetryWeight law retry tape * (PMF.pure (stoppedRetryTapeHistory tape)) history) = _
  rw [stoppedRetryWeight_renewal, retainedRetryStep, PMF.bind_apply, ← ENNReal.tsum_add]
  apply tsum_congr
  intro value
  by_cases hv : value ∈ retry
  · have hm : retry.indicator law value = law value := by simp [Set.indicator, hv]
    have hn : retryᶜ.indicator law value = 0 := by simp [Set.indicator, hv]
    rw [hm, hn, zero_mul, zero_add, if_pos hv, unlimitedRetainedRetries_map_apply]
    apply congrArg (fun x => law value * x)
    apply tsum_congr
    intro tape
    rw [stoppedRetryTapeHistory_prepend]
  · have hm : retry.indicator law value = 0 := by simp [Set.indicator, hv]
    have hn : retryᶜ.indicator law value = law value := by simp [Set.indicator, hv]
    rw [hm, hn, zero_mul, add_zero, if_neg hv]
    rfl

end Zcash.Snark.ZeroKnowledge
