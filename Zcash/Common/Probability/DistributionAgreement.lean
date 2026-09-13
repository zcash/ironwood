import Zcash.Common.Probability.DistributionKernel

/-!
# Bias from disagreement on a common discrete probability space

The exceptional-event argument applies to arbitrary discrete source spaces,
including the countable support of a law of finite stopped histories.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- Two observations agreeing on the supported good event differ by at most its complement's mass. -/
theorem eventBias_map_of_agree {A B : Type*} (law : PMF A) (left right : A → B) (bad : Set A)
    (hagree : ∀ a ∈ law.support, a ∉ bad → left a = right a) :
    PMFEventBiasLE (law.map left) (law.map right) (law.toOuterMeasure bad) := by
  intro event
  simp only [PMF.toOuterMeasure_map_apply]
  have hsub : (left ⁻¹' event) ∩ law.support ⊆ (right ⁻¹' event) ∪ bad := by
    intro a ⟨ha, hs⟩
    by_cases hb : a ∈ bad
    · exact Or.inr hb
    · exact Or.inl (by simpa only [Set.mem_preimage, ← hagree a hs hb] using ha)
  exact (law.toOuterMeasure_mono hsub).trans (MeasureTheory.measure_union_le _ _)

end Zcash.Common.Probability
