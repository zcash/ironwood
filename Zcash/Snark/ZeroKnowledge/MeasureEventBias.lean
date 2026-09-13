import Zcash.Common.Probability.Distribution
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# Event comparison for complete infinite observations

Infinite streams need probability measures rather than probability mass
functions. A uniform event bound on all finite cylinders extends to every
measurable event of the stream, including events about nontermination.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory Zcash.Common
open scoped ENNReal symmDiff

/-- One direction of the statistical event bound on a measurable observation space. -/
def MeasureEventBiasLE {A : Type*} [MeasurableSpace A] (actual ideal : Measure A)
    (error : ℝ≥0∞) : Prop :=
  ∀ event, MeasurableSet event → actual event ≤ ideal event + error

/-- The existing discrete comparison also bounds all measurable events of the associated measures. -/
theorem eventBias_toMeasure {A : Type*} [MeasurableSpace A] {actual ideal : PMF A} {error : ℝ≥0∞}
    (h : PMFEventBiasLE actual ideal error) : MeasureEventBiasLE actual.toMeasure ideal.toMeasure error := by
  intro event hm
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  exact h event

/-- A common measurable observation cannot increase the measure-level event bound. -/
theorem measureEventBias_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {actual ideal : Measure A} {error : ℝ≥0∞} (h : MeasureEventBiasLE actual ideal error)
    (observe : A → B) (hm : Measurable observe) :
    MeasureEventBiasLE (actual.map observe) (ideal.map observe) error := by
  intro event he
  rw [Measure.map_apply hm he, Measure.map_apply hm he]
  exact h _ (he.preimage hm)

/-- Approximating an event changes its probability by at most the symmetric-difference mass. -/
theorem measure_event_le_approximation {A : Type*} [MeasurableSpace A] (law : Measure A)
    (event approximation : Set A) : law event ≤ law approximation + law (approximation ∆ event) := by
  apply (measure_mono (show event ⊆ approximation ∪ (approximation ∆ event) from ?_)).trans
    (measure_union_le _ _)
  intro value hv
  by_cases ha : value ∈ approximation
  · exact Or.inl ha
  · exact Or.inr (by simp [Set.mem_symmDiff, ha, hv])

/-- Uniform comparison of every finite cylinder controls every measurable event of the complete product space. -/
theorem measureEventBias_of_cylinders {Index : Type*} {A : Index → Type*}
    [∀ i, MeasurableSpace (A i)] (actual ideal : Measure (∀ i, A i))
    [IsFiniteMeasure actual] [IsFiniteMeasure ideal] (error : ℝ≥0∞)
    (h : ∀ event ∈ measurableCylinders A, actual event ≤ ideal event + error) :
    MeasureEventBiasLE actual ideal error := by
  intro event he
  apply ENNReal.le_of_forall_pos_le_add
  intro tolerance ht _
  have hcover : ∃ D : Set (Set (∀ i, A i)), D.Countable ∧ D ⊆ measurableCylinders A ∧
      (actual + ideal) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      exact hs ▸ univ_mem_measurableCylinders A
    · simp
  obtain ⟨approximation, ha, hclose⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := actual + ideal) isSetRing_measurableCylinders hcover
      generateFrom_measurableCylinders.symm he (ε := (tolerance : ℝ≥0∞)) (by exact_mod_cast ht)
  have htotal : actual (approximation ∆ event) + ideal (approximation ∆ event) ≤ tolerance := by
    simpa only [Measure.add_apply] using hclose.le
  calc
    actual event ≤ actual approximation + actual (approximation ∆ event) :=
      measure_event_le_approximation actual event approximation
    _ ≤ (ideal approximation + error) + actual (approximation ∆ event) :=
      add_le_add (h approximation ha) le_rfl
    _ ≤ ((ideal event + ideal (approximation ∆ event)) + error) + actual (approximation ∆ event) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [symmDiff_comm] using measure_event_le_approximation ideal approximation event
        · exact le_rfl
      · exact le_rfl
    _ = (ideal event + error) + (actual (approximation ∆ event) + ideal (approximation ∆ event)) := by ring
    _ ≤ _ := add_le_add le_rfl htotal

end Zcash.Snark.ZeroKnowledge
