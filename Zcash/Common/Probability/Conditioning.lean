import Zcash.Common.Probability.Distribution

/-!
# Simulation bounds after conditioning on successful attempts

Conditioning changes the normalizing mass. This file retains that cost explicitly instead
of transferring an unconditioned simulation bound unchanged to the successful-proof law.
The success event is the same observable predicate in the real and simulated experiments.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- A conditioning event with a supported outcome has positive mass. -/
theorem conditioning_mass_ne_zero {A : Type*} (law : PMF A) (success : Set A)
    (h : ∃ a ∈ success, a ∈ law.support) : law.toOuterMeasure success ≠ 0 := by
  rw [Ne, law.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  obtain ⟨a, ha, hs⟩ := h
  exact fun hd => hd hs ha

/-- The event law after conditioning, with its actual success probability in the denominator. -/
theorem conditioned_event_mass {A : Type*} (law : PMF A) (success : Set A)
    (h : ∃ a ∈ success, a ∈ law.support) (event : Set A) :
    (law.filter success h).toOuterMeasure event =
      law.toOuterMeasure (event ∩ success) / law.toOuterMeasure success := by
  classical
  rw [(law.filter success h).toOuterMeasure_apply event,
    law.toOuterMeasure_apply (event ∩ success), div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  by_cases he : a ∈ event <;> by_cases hs : a ∈ success <;>
    simp [PMF.filter_apply, Set.indicator, he, hs, law.toOuterMeasure_apply success]

/-- Multiplying the conditioned event mass by success probability recovers its original mass. -/
theorem conditioned_event_mul_mass {A : Type*} (law : PMF A) (success : Set A)
    (h : ∃ a ∈ success, a ∈ law.support) (event : Set A) :
    (law.filter success h).toOuterMeasure event * law.toOuterMeasure success =
      law.toOuterMeasure (event ∩ success) := by
  rw [conditioned_event_mass, ENNReal.div_mul_cancel
    (conditioning_mass_ne_zero law success h)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (law.toOuterMeasure_apply_le_one success))]

/-- The forward conditional comparison charges both the event and normalization errors. -/
theorem conditioned_eventBias {A : Type*} {actual ideal : PMF A} {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (success : Set A)
    (ha : ∃ a ∈ success, a ∈ actual.support) (hi : ∃ a ∈ success, a ∈ ideal.support) :
    PMFEventBiasLE (actual.filter success ha) (ideal.filter success hi)
      ((ε + ε) / actual.toOuterMeasure success) := by
  intro event
  have hfinite : actual.toOuterMeasure success ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (actual.toOuterMeasure_apply_le_one success)
  have hprob : (ideal.filter success hi).toOuterMeasure event * ε ≤ ε := by
    simpa using mul_le_mul_left ((ideal.filter success hi).toOuterMeasure_apply_le_one event) ε
  rw [conditioned_event_mass actual success ha event]
  apply (ENNReal.div_le_iff (conditioning_mass_ne_zero actual success ha)
    hfinite).2
  calc
    actual.toOuterMeasure (event ∩ success)
        ≤ ideal.toOuterMeasure (event ∩ success) + ε := forward _
    _ = (ideal.filter success hi).toOuterMeasure event * ideal.toOuterMeasure success + ε := by
      rw [conditioned_event_mul_mass]
    _ ≤ (ideal.filter success hi).toOuterMeasure event *
        (actual.toOuterMeasure success + ε) + ε :=
      add_le_add (mul_le_mul_right (reverse success) _) le_rfl
    _ = (ideal.filter success hi).toOuterMeasure event * actual.toOuterMeasure success +
        (ideal.filter success hi).toOuterMeasure event * ε + ε := by rw [mul_add]
    _ ≤ (ideal.filter success hi).toOuterMeasure event * actual.toOuterMeasure success + ε + ε :=
      add_le_add (add_le_add le_rfl hprob) le_rfl
    _ = ((ideal.filter success hi).toOuterMeasure event +
        (ε + ε) / actual.toOuterMeasure success) * actual.toOuterMeasure success := by
      rw [add_mul, ENNReal.div_mul_cancel (conditioning_mass_ne_zero actual success ha)
        hfinite, add_assoc]

/-- Both directions after conditioning, with the actual normalizing masses left explicit. -/
theorem conditioned_simulation_error_bound {A : Type*} {actual ideal : PMF A} {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (success : Set A)
    (ha : ∃ a ∈ success, a ∈ actual.support) (hi : ∃ a ∈ success, a ∈ ideal.support) :
    PMFEventBiasLE (actual.filter success ha) (ideal.filter success hi)
        ((ε + ε) / actual.toOuterMeasure success) ∧
      PMFEventBiasLE (ideal.filter success hi) (actual.filter success ha)
        ((ε + ε) / ideal.toOuterMeasure success) :=
  ⟨conditioned_eventBias forward reverse success ha hi,
    conditioned_eventBias reverse forward success hi ha⟩

/-- A common lower bound on both success probabilities gives one conditional error budget. -/
theorem conditioned_common_error_bound {A : Type*} {actual ideal : PMF A} {ε lower : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (success : Set A)
    (ha : ∃ a ∈ success, a ∈ actual.support) (hi : ∃ a ∈ success, a ∈ ideal.support)
    (haLower : lower ≤ actual.toOuterMeasure success) (hiLower : lower ≤ ideal.toOuterMeasure success) :
    PMFEventBiasLE (actual.filter success ha) (ideal.filter success hi) ((ε + ε) / lower) ∧
      PMFEventBiasLE (ideal.filter success hi) (actual.filter success ha) ((ε + ε) / lower) := by
  have h := conditioned_simulation_error_bound forward reverse success ha hi
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl (ENNReal.div_le_div_left haLower _)),
    fun event => (h.2 event).trans (add_le_add le_rfl (ENNReal.div_le_div_left hiLower _))⟩

end Zcash.Common.Probability
