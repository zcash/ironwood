import Zcash.Common.Probability.Distribution

/-!
# Randomized observations on arbitrary probability mass functions

Event bias bounds all bounded probabilistic tests, including on the countable
space of byte strings or stopped retry histories. Thus randomized observations
preserve the simulation error without requiring a finite output type.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- An event bound controls every `[0,1]`-valued test, without a finite-type premise. -/
theorem eventBias_weighted_tsum {A : Type*} {actual ideal : PMF A} {ε : ℝ≥0∞}
    (h : PMFEventBiasLE actual ideal ε) (weight : A → ℝ≥0∞) (hw : ∀ a, weight a ≤ 1) :
    (∑' a, actual a * weight a) ≤ (∑' a, ideal a * weight a) + ε := by
  classical
  let positive : Set A := {a | ideal a < actual a}
  let excess : A → ℝ≥0∞ := fun a => if a ∈ positive then actual a - ideal a else 0
  have hmass : ideal.toOuterMeasure positive ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ideal.toOuterMeasure_apply_le_one positive)
  have hsplit : (∑' a, excess a) + ideal.toOuterMeasure positive =
      actual.toOuterMeasure positive := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases ha : a ∈ positive
    · simp only [excess, if_pos ha, Set.indicator_of_mem ha]
      exact tsub_add_cancel_of_le (show ideal a ≤ actual a from le_of_lt ha)
    · simp [excess, ha]
  have hexcess : (∑' a, excess a) ≤ ε := by
    apply (ENNReal.add_le_add_iff_right hmass).mp
    rw [hsplit]
    simpa only [add_comm] using h positive
  have hpoint (a : A) : actual a * weight a ≤ ideal a * weight a + excess a := by
    by_cases ha : a ∈ positive
    · simp only [excess, if_pos ha]
      calc
        _ = (ideal a + (actual a - ideal a)) * weight a := by
          rw [add_tsub_cancel_of_le (show ideal a ≤ actual a from le_of_lt ha)]
        _ = ideal a * weight a + (actual a - ideal a) * weight a := add_mul _ _ _
        _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' (hw a))
    · simp only [excess, if_neg ha, add_zero]
      exact mul_le_mul_left (not_lt.mp (show ¬ ideal a < actual a from ha)) _
  calc
    _ ≤ ∑' a, (ideal a * weight a + excess a) := ENNReal.tsum_le_tsum hpoint
    _ = (∑' a, ideal a * weight a) + ∑' a, excess a := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl hexcess

/-- A common probabilistic continuation preserves event bias on any discrete sample space. -/
theorem eventBias_bind_kernel {A B : Type*} {actual ideal : PMF A} {ε : ℝ≥0∞}
    (h : PMFEventBiasLE actual ideal ε) (observe : A → PMF B) :
    PMFEventBiasLE (actual.bind observe) (ideal.bind observe) ε := by
  intro event
  simp only [PMF.toOuterMeasure_bind_apply]
  exact eventBias_weighted_tsum h (fun a => (observe a).toOuterMeasure event)
    (fun a => (observe a).toOuterMeasure_apply_le_one event)

/-- A common outer law averages pointwise continuation bounds on any discrete space. -/
theorem eventBias_bind_average_tsum {A B : Type*} (law : PMF A)
    {actual ideal : A → PMF B} {cost : A → ℝ≥0∞}
    (h : ∀ a, PMFEventBiasLE (actual a) (ideal a) (cost a)) :
    PMFEventBiasLE (law.bind actual) (law.bind ideal) (∑' a, law a * cost a) := by
  intro event
  simp only [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' a, law a * ((ideal a).toOuterMeasure event + cost a) :=
      ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a event) _)
    _ = _ := by simp only [mul_add, ENNReal.tsum_add]

end Zcash.Common.Probability
