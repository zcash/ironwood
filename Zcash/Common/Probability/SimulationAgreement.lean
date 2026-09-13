import Zcash.Common.Probability.DistributionAgreement

/-!
# Simulation with an exceptional observation map

The real observation may differ from the simulated observation on an exceptional
set of projected views. One event comparison suffices: the final error is the
existing simulation error plus the simulator's exceptional-set probability.
This avoids charging the same distribution replacement a second time merely
to move an exceptional-event bound from the simulator to the prover.
-/

namespace Zcash.Common.Probability

open scoped ENNReal

/-- Transfer a simulation through observations that agree away from an exceptional projected view. -/
theorem simulation_map_of_agree {Source View Output : Type*}
    (source : PMF Source) (project : Source → View) (ideal : PMF View)
    (actualOutput : Source → Output) (idealOutput : View → Output) (bad : Set View) {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE (source.map project) ideal ε)
    (reverse : PMFEventBiasLE ideal (source.map project) ε)
    (hagree : ∀ sample ∈ source.support, project sample ∉ bad → actualOutput sample = idealOutput (project sample)) :
    PMFEventBiasLE (source.map actualOutput) (ideal.map idealOutput) (ε + ideal.toOuterMeasure bad) ∧
      PMFEventBiasLE (ideal.map idealOutput) (source.map actualOutput) (ε + ideal.toOuterMeasure bad) := by
  constructor
  · intro event
    simp only [PMF.toOuterMeasure_map_apply]
    have hsubset : (actualOutput ⁻¹' event) ∩ source.support ⊆
        project ⁻¹' ((idealOutput ⁻¹' event) ∪ bad) := by
      intro sample ⟨hactual, hs⟩
      by_cases hb : project sample ∈ bad
      · exact Or.inr hb
      · exact Or.inl (by simpa only [Set.mem_preimage, ← hagree sample hs hb] using hactual)
    calc
      _ ≤ source.toOuterMeasure (project ⁻¹' ((idealOutput ⁻¹' event) ∪ bad)) :=
        source.toOuterMeasure_mono hsubset
      _ ≤ ideal.toOuterMeasure ((idealOutput ⁻¹' event) ∪ bad) + ε := by
        simpa only [PMF.toOuterMeasure_map_apply] using forward ((idealOutput ⁻¹' event) ∪ bad)
      _ ≤ (ideal.toOuterMeasure (idealOutput ⁻¹' event) + ideal.toOuterMeasure bad) + ε :=
        add_le_add (MeasureTheory.measure_union_le _ _) le_rfl
      _ = _ := by ac_rfl
  · intro event
    simp only [PMF.toOuterMeasure_map_apply]
    let goodEvent := (idealOutput ⁻¹' event) \ bad
    have hcover : (idealOutput ⁻¹' event) ∩ ideal.support ⊆ goodEvent ∪ bad := by
      intro view ⟨hevent, _⟩
      by_cases hb : view ∈ bad
      · exact Or.inr hb
      · exact Or.inl ⟨hevent, hb⟩
    have hsubset : (project ⁻¹' goodEvent) ∩ source.support ⊆ actualOutput ⁻¹' event := by
      intro sample ⟨⟨hevent, hgood⟩, hs⟩
      simpa only [Set.mem_preimage, hagree sample hs hgood] using hevent
    calc
      _ ≤ ideal.toOuterMeasure (goodEvent ∪ bad) := ideal.toOuterMeasure_mono hcover
      _ ≤ ideal.toOuterMeasure goodEvent + ideal.toOuterMeasure bad := MeasureTheory.measure_union_le _ _
      _ ≤ ((source.map project).toOuterMeasure goodEvent + ε) + ideal.toOuterMeasure bad :=
        add_le_add (reverse goodEvent) le_rfl
      _ ≤ (source.toOuterMeasure (actualOutput ⁻¹' event) + ε) + ideal.toOuterMeasure bad := by
        rw [PMF.toOuterMeasure_map_apply]
        exact add_le_add (add_le_add (source.toOuterMeasure_mono hsubset) le_rfl) le_rfl
      _ = _ := by ac_rfl

end Zcash.Common.Probability
