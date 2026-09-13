import Zcash.Common.Oracle.Model

/-!
# Transporting simulation through observations and exceptional events

Deterministic observations may retain an emitted prefix and an error, so a simulation
bound need not discard failed executions. Exact agreement off an exceptional event gives
a two-sided bound by that event's probability under the common outer sampling law.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- Applying the same observation function cannot increase event bias. -/
theorem eventBias_map {A B : Type*} {actual ideal : PMF A} {ε : ℝ≥0∞}
    (h : PMFEventBiasLE actual ideal ε) (observe : A → B) :
    PMFEventBiasLE (actual.map observe) (ideal.map observe) ε := by
  intro event
  simpa only [PMF.toOuterMeasure_map_apply] using h (observe ⁻¹' event)

/-- Without any agreement premise, the event bias between probability laws is at most one. -/
theorem eventBias_le_one {A : Type*} (actual ideal : PMF A) :
    PMFEventBiasLE actual ideal 1 := by
  intro event
  exact (actual.toOuterMeasure_apply_le_one event).trans (le_add_self)

/-- Identical conditional laws outside a bad event differ by at most the bad event's mass.

The outer draw is the same on both sides. The bad branches may be arbitrary; neither law
is conditioned on success or on the complement of the bad event. -/
theorem mixedLaws_error_bound {C A : Type*}
    (coins : PMF C) (actual ideal : C → PMF A) (good : C → Prop) [DecidablePred good]
    (hgood : ∀ c, good c → actual c = ideal c) :
    PMFEventBiasLE (coins.bind actual) (coins.bind ideal)
        (coins.toOuterMeasure {c | ¬ good c}) ∧
      PMFEventBiasLE (coins.bind ideal) (coins.bind actual)
        (coins.toOuterMeasure {c | ¬ good c}) := by
  have hdirection (f g : C → PMF A) (hfg : ∀ c, good c → f c = g c) :
      PMFEventBiasLE (coins.bind f) (coins.bind g) (coins.toOuterMeasure {c | ¬ good c}) := by
    intro event
    have hpoint (c : C) : (f c).toOuterMeasure event ≤
        (g c).toOuterMeasure event + (if good c then 0 else 1) := by
      by_cases hc : good c
      · rw [if_pos hc, hfg c hc, add_zero]
      · rw [if_neg hc]
        exact eventBias_le_one (f c) (g c) event
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' c, coins c * ((g c).toOuterMeasure event + (if good c then 0 else 1)) :=
        ENNReal.tsum_le_tsum fun c => mul_le_mul_right (hpoint c) (coins c)
      _ = _ := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        congr 1
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro c
        by_cases hc : good c <;> simp [hc]
  exact ⟨hdirection actual ideal hgood,
    hdirection ideal actual (fun c hc => (hgood c hc).symm)⟩

end Zcash.Common.Probability
