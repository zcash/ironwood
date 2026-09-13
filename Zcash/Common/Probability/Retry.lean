import Zcash.Common.Probability.Conditioning
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Independent retries and the successful-attempt law

Each retry samples the same attempt law afresh and discards failed outputs. The finite
execution reports `none` when its attempt budget is exhausted. Its comparison with the
conditioned law charges exactly the probability that every attempt failed. This model
does not cover a caller that reuses coins, carries a transcript state across attempts,
or reveals failed attempts as part of its output.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- Success and failure have total probability one. -/
theorem event_mass_add_compl {A : Type*} (law : PMF A) (success : Set A) :
    law.toOuterMeasure success + law.toOuterMeasure successᶜ = 1 := by
  classical
  rw [law.toOuterMeasure_apply success, law.toOuterMeasure_apply successᶜ,
    ← ENNReal.tsum_add, ← law.tsum_coe]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ success <;> simp [Set.indicator, ha]

/-- An upper bound on failure gives a lower bound on the success normalizer. -/
theorem success_mass_lower_bound {A : Type*} (law : PMF A) (success : Set A) {failure : ℝ≥0∞}
    (h : law.toOuterMeasure successᶜ ≤ failure) : 1 - failure ≤ law.toOuterMeasure success := by
  apply tsub_le_iff_right.mpr
  rw [← event_mass_add_compl law success]
  exact add_le_add le_rfl h

/-- One fresh attempt, falling back to the supplied continuation on failure. -/
noncomputable def retryStep {A B : Type*} (law : PMF A) (success : Set A)
    [DecidablePred (fun a => a ∈ success)] (respond : A → B) (next : PMF B) : PMF B :=
  law.bind fun a => if a ∈ success then PMF.pure (respond a) else next

/-- Keep trying with independent draws, reporting budget exhaustion explicitly. -/
noncomputable def boundedRetries {A : Type*} (law : PMF A) (success : Set A)
    [DecidablePred (fun a => a ∈ success)] : ℕ → PMF (Option A)
  | 0 => PMF.pure none
  | n + 1 => retryStep law success some (boundedRetries law success n)

/-- A step's event probability is its successful part plus the failed-attempt continuation. -/
theorem retryStep_event_mass {A B : Type*} (law : PMF A) (success : Set A)
    [DecidablePred (fun a => a ∈ success)] (respond : A → B) (next : PMF B) (event : Set B) :
    (retryStep law success respond next).toOuterMeasure event =
      law.toOuterMeasure (respond ⁻¹' event ∩ success) +
        law.toOuterMeasure successᶜ * next.toOuterMeasure event := by
  classical
  rw [retryStep, PMF.toOuterMeasure_bind_apply,
    law.toOuterMeasure_apply (respond ⁻¹' event ∩ success),
    law.toOuterMeasure_apply successᶜ, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro a
  by_cases hs : a ∈ success <;> by_cases he : respond a ∈ event <;>
    simp [hs, he, Set.indicator, PMF.toOuterMeasure_pure_apply]

/-- The conditioned law is a fixed point of one independent retry step. -/
theorem conditioned_retry_fixedpoint {A B : Type*} (law : PMF A) (success : Set A)
    [DecidablePred (fun a => a ∈ success)] (respond : A → B)
    (h : ∃ a ∈ success, a ∈ law.support) :
    retryStep law success respond ((law.filter success h).map respond) =
      (law.filter success h).map respond := by
  apply PMF.toOuterMeasure_injective
  ext event
  rw [retryStep_event_mass, PMF.toOuterMeasure_map_apply,
    ← conditioned_event_mul_mass law success h (respond ⁻¹' event),
    mul_comm (law.toOuterMeasure successᶜ), ← mul_add, event_mass_add_compl, mul_one]

/-- Only failed first attempts expose a difference in the continuation laws. -/
theorem retryStep_error_bound {A B : Type*}
    (law : PMF A) (success : Set A) [DecidablePred (fun a => a ∈ success)] (respond : A → B)
    {left right : PMF B} {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE left right ε) (reverse : PMFEventBiasLE right left ε) :
    PMFEventBiasLE (retryStep law success respond left) (retryStep law success respond right)
        (law.toOuterMeasure successᶜ * ε) ∧
      PMFEventBiasLE (retryStep law success respond right) (retryStep law success respond left)
        (law.toOuterMeasure successᶜ * ε) := by
  have step {l r : PMF B} (h : PMFEventBiasLE l r ε) :
      PMFEventBiasLE (retryStep law success respond l) (retryStep law success respond r)
        (law.toOuterMeasure successᶜ * ε) := by
    intro event
    simp only [retryStep_event_mass]
    calc
      _ ≤ law.toOuterMeasure (respond ⁻¹' event ∩ success) +
          law.toOuterMeasure successᶜ * (r.toOuterMeasure event + ε) :=
        add_le_add le_rfl (mul_le_mul_right (h event) _)
      _ = _ := by rw [mul_add, add_assoc]
  exact ⟨step forward, step reverse⟩

/-- Finite independent retries approach the conditioned law with the geometric failure bound. -/
theorem boundedRetries_error_bound {A : Type*}
    (law : PMF A) (success : Set A) [DecidablePred (fun a => a ∈ success)]
    (h : ∃ a ∈ success, a ∈ law.support) (n : ℕ) :
    PMFEventBiasLE (boundedRetries law success n) ((law.filter success h).map some)
        (law.toOuterMeasure successᶜ ^ n) ∧
      PMFEventBiasLE ((law.filter success h).map some) (boundedRetries law success n)
        (law.toOuterMeasure successᶜ ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ⟨eventBias_le_one _ _, eventBias_le_one _ _⟩
  | succ n ih =>
    have hs := retryStep_error_bound law success some ih.1 ih.2
    rw [conditioned_retry_fixedpoint law success some h] at hs
    simpa only [boundedRetries, pow_succ, mul_comm] using hs

/-- Exhausting the budget has exactly the probability that all independent attempts fail. -/
theorem boundedRetries_exhausted {A : Type*} (law : PMF A) (success : Set A)
    [DecidablePred (fun a => a ∈ success)] (n : ℕ) :
    (boundedRetries law success n).toOuterMeasure {none} = law.toOuterMeasure successᶜ ^ n := by
  have hempty : ((some : A → Option A) ⁻¹' {none}) ∩ success = ∅ := by ext; simp
  induction n with
  | zero => simp [boundedRetries, PMF.toOuterMeasure_pure_apply]
  | succ n ih =>
    rw [boundedRetries, retryStep_event_mass, hempty]
    simp only [MeasureTheory.measure_empty, zero_add, ih, pow_succ']

/-- Positive success mass makes the independent failure probability strictly less than one. -/
theorem failure_mass_lt_one {A : Type*} (law : PMF A) (success : Set A)
    (h : ∃ a ∈ success, a ∈ law.support) : law.toOuterMeasure successᶜ < 1 := by
  have hfinite : law.toOuterMeasure successᶜ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (law.toOuterMeasure_apply_le_one successᶜ)
  have hlt := ENNReal.lt_add_right hfinite (conditioning_mass_ne_zero law success h)
  simpa only [add_comm, event_mass_add_compl] using hlt

/-- Every event in the independent-retry experiment converges to its conditioned probability. -/
theorem boundedRetries_tendsto {A : Type*}
    (law : PMF A) (success : Set A) [DecidablePred (fun a => a ∈ success)]
    (h : ∃ a ∈ success, a ∈ law.support) (event : Set (Option A)) :
    Filter.Tendsto (fun n => (boundedRetries law success n).toOuterMeasure event) Filter.atTop
      (nhds (((law.filter success h).map some).toOuterMeasure event)) := by
  apply tendsto_toOuterMeasure_of_eventBiasLE
    (fun n => (boundedRetries_error_bound law success h n).1)
    (fun n => (boundedRetries_error_bound law success h n).2)
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (failure_mass_lt_one law success h)

/-- A strict failure bound supplies the support witness required to condition on success. -/
theorem exists_success_of_failure_lt_one {A : Type*} (law : PMF A) (success : Set A)
    (hfailure : law.toOuterMeasure successᶜ < 1) : ∃ a ∈ success, a ∈ law.support := by
  classical
  by_contra hnone
  have hzero : law.toOuterMeasure success = 0 := by
    rw [law.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro a hs ha
    exact hnone ⟨a, ha, hs⟩
  have hmass := event_mass_add_compl law success
  rw [hzero, zero_add] at hmass
  exact hfailure.ne hmass

end Zcash.Common.Probability
