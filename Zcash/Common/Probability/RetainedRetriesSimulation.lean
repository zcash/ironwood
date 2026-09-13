import Zcash.Common.Probability.RetainedRetries
import Zcash.Common.Probability.DistributionKernel

/-!
# Simulation of retained retry histories

A new attempt costs the original simulation error. The continuation's error is
paid only when the real attempt requests a retry, even though its entire value
is retained. This gives a geometric error budget, uniformly bounded by
`epsilon / (1 - failure)` when the retry probability is strictly below one.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- Changing one attempt's law costs its bias under the same observable retry policy. -/
theorem retainedRetryStep_source_bias {A : Type*}
    {actual ideal : PMF A} {ε : ℝ≥0∞} (h : PMFEventBiasLE actual ideal ε)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (next : PMF (RetryHistory A)) :
    PMFEventBiasLE (retainedRetryStep actual retry next) (retainedRetryStep ideal retry next) ε :=
  eventBias_bind_kernel h _

/-- Retaining the first attempt does not remove the retry-probability factor on continuation error. -/
theorem retainedRetryStep_continuation_error_bound {A : Type*}
    (law : PMF A) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    {left right : PMF (RetryHistory A)} {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE left right ε) (reverse : PMFEventBiasLE right left ε) :
    PMFEventBiasLE (retainedRetryStep law retry left) (retainedRetryStep law retry right)
        (law.toOuterMeasure retry * ε) ∧
      PMFEventBiasLE (retainedRetryStep law retry right) (retainedRetryStep law retry left)
        (law.toOuterMeasure retry * ε) := by
  have hmass : (∑' a, law a * (if a ∈ retry then ε else 0)) = law.toOuterMeasure retry * ε := by
    rw [law.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases ha : a ∈ retry <;> simp [ha, Set.indicator]
  have liftBias {p q : PMF (RetryHistory A)} (h : PMFEventBiasLE p q ε) (a : A) :
      PMFEventBiasLE
        (if a ∈ retry then p.map (RetryHistory.prepend a) else PMF.pure (.stopped a))
        (if a ∈ retry then q.map (RetryHistory.prepend a) else PMF.pure (.stopped a))
        (if a ∈ retry then ε else 0) := by
    by_cases ha : a ∈ retry
    · simpa only [if_pos ha] using eventBias_map h (RetryHistory.prepend a)
    · simp only [if_neg ha]
      intro event
      simp
  exact ⟨hmass ▸ eventBias_bind_average_tsum law (liftBias forward),
    hmass ▸ eventBias_bind_average_tsum law (liftBias reverse)⟩

/-- The error for a bounded sequence, charging later comparisons only after an earlier retry. -/
noncomputable def retainedRetryError (ε rate : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => ε + rate * retainedRetryError ε rate n

/-- The recurrence is the stated geometric partial sum. -/
theorem retainedRetryError_eq_sum (ε rate : ℝ≥0∞) (n : ℕ) :
    retainedRetryError ε rate n = ∑ j ∈ Finset.range n, rate ^ j * ε := by
  induction n with
  | zero => simp [retainedRetryError]
  | succ n ih =>
    simp [retainedRetryError, ih, Finset.sum_range_succ', pow_succ', Finset.mul_sum, mul_assoc, add_comm]

/-- A strict retry bound uniformly controls the whole geometric error budget. -/
theorem retainedRetryError_le (ε rate : ℝ≥0∞) (hrate : rate < 1) (n : ℕ) :
    retainedRetryError ε rate n ≤ ε / (1 - rate) := by
  have hd0 : 1 - rate ≠ 0 := (tsub_pos_iff_lt.mpr hrate).ne'
  have hdt : 1 - rate ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hfixed : ε + rate * (ε / (1 - rate)) = ε / (1 - rate) := by
    calc
      _ = (ε / (1 - rate)) * ((1 - rate) + rate) := by
        rw [mul_add, ENNReal.div_mul_cancel hd0 hdt, mul_comm (ε / (1 - rate)) rate]
      _ = _ := by rw [tsub_add_cancel_of_le hrate.le, mul_one]
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    exact (add_le_add le_rfl (mul_le_mul_right ih rate)).trans_eq hfixed

/-- Every bounded history, including failed prefixes and terminal errors, has the geometric comparison. -/
theorem retainedRetries_simulation_error_bound {A : Type*}
    {actual ideal : PMF A} {ε failure : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (hfailure : actual.toOuterMeasure retry ≤ failure) (n : ℕ) :
    PMFEventBiasLE (retainedRetries actual retry n) (retainedRetries ideal retry n)
        (retainedRetryError ε failure n) ∧
      PMFEventBiasLE (retainedRetries ideal retry n) (retainedRetries actual retry n)
        (retainedRetryError ε failure n) := by
  induction n with
  | zero =>
    constructor <;> intro event <;> simp [retainedRetries, retainedRetryError]
  | succ n ih =>
    have hc := retainedRetryStep_continuation_error_bound actual retry ih.1 ih.2
    have hs := retainedRetryStep_source_bias forward retry (retainedRetries ideal retry n)
    have hr := retainedRetryStep_source_bias reverse retry (retainedRetries ideal retry n)
    have hcost : actual.toOuterMeasure retry * retainedRetryError ε failure n ≤
        failure * retainedRetryError ε failure n := mul_le_mul_left hfailure _
    have hf := hc.1.trans hs
    have hb := hr.trans hc.2
    constructor
    · intro event
      exact (hf event).trans (add_le_add le_rfl (add_le_add le_rfl hcost))
    · intro event
      have h := (hb event).trans (add_le_add le_rfl (add_le_add hcost le_rfl))
      simpa only [retainedRetries, retainedRetryError, add_comm] using h

/-- One bound covers every finite retry budget while retaining the complete history. -/
theorem retainedRetries_uniform_error_bound {A : Type*}
    {actual ideal : PMF A} {ε failure : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (hfailure : actual.toOuterMeasure retry ≤ failure) (hrate : failure < 1) (n : ℕ) :
    PMFEventBiasLE (retainedRetries actual retry n) (retainedRetries ideal retry n)
        (ε / (1 - failure)) ∧
      PMFEventBiasLE (retainedRetries ideal retry n) (retainedRetries actual retry n)
        (ε / (1 - failure)) := by
  have h := retainedRetries_simulation_error_bound forward reverse retry hfailure n
  have hcost := retainedRetryError_le ε failure hrate n
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hcost),
    fun event => (h.2 event).trans (add_le_add le_rfl hcost)⟩

/-- The retry-probability bound controls exhaustion at every finite budget. -/
theorem retainedRetries_exhausted_le {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {failure : ℝ≥0∞}
    (hfailure : law.toOuterMeasure retry ≤ failure) (n : ℕ) :
    (retainedRetries law retry n).toOuterMeasure {history | history.exhausted = true} ≤ failure ^ n := by
  rw [retainedRetries_exhausted]
  gcongr

/-- The probability of needing more attempts tends to zero, without discarding failed prefixes. -/
theorem retainedRetries_exhausted_tendsto {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {failure : ℝ≥0∞}
    (hfailure : law.toOuterMeasure retry ≤ failure) (hrate : failure < 1) :
    Filter.Tendsto (fun n =>
      (retainedRetries law retry n).toOuterMeasure {history | history.exhausted = true})
      Filter.atTop (nhds 0) := by
  simpa only [retainedRetries_exhausted] using
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hfailure.trans_lt hrate)

end Zcash.Common.Probability
