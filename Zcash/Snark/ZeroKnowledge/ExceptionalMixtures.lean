import Zcash.Snark.ZeroKnowledge.Distribution

/-!
# Exceptional branches under an arbitrary private-state law

Private material contains lists of row vectors, so its ambient type need not be finite.
The PMF still assigns total mass one. Agreement outside an exceptional set therefore
gives the same simulation bound by that set's probability, without conditioning it away.
Approximate conditional agreement adds the average of its state-dependent error bounds.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open scoped ENNReal

/-- Average conditional simulation errors and charge the probability of exceptional branches. -/
theorem variableMixedLaws_error_bound {C A : Type*}
    (coins : PMF C) (actual ideal : C → PMF A) (good : C → Prop) [DecidablePred good]
    (error : C → ℝ≥0∞)
    (hgood : ∀ c, good c → PMFEventBiasLE (actual c) (ideal c) (error c) ∧
      PMFEventBiasLE (ideal c) (actual c) (error c)) :
    PMFEventBiasLE (coins.bind actual) (coins.bind ideal)
        ((∑' c, coins c * error c) + coins.toOuterMeasure {c | ¬ good c}) ∧
      PMFEventBiasLE (coins.bind ideal) (coins.bind actual)
        ((∑' c, coins c * error c) + coins.toOuterMeasure {c | ¬ good c}) := by
  have hdirection (f g : C → PMF A)
      (hfg : ∀ c, good c → PMFEventBiasLE (f c) (g c) (error c)) :
      PMFEventBiasLE (coins.bind f) (coins.bind g)
        ((∑' c, coins c * error c) + coins.toOuterMeasure {c | ¬ good c}) := by
    intro event
    have hpoint (c : C) : (f c).toOuterMeasure event ≤
        (g c).toOuterMeasure event + (error c + if good c then 0 else 1) := by
      by_cases hc : good c
      · simpa only [if_pos hc, add_zero] using hfg c hc event
      · rw [if_neg hc]
        exact (eventBias_le_one (f c) (g c) event).trans
          (add_le_add le_rfl le_add_self)
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' c, coins c * ((g c).toOuterMeasure event + (error c + if good c then 0 else 1)) :=
        ENNReal.tsum_le_tsum fun c => mul_le_mul_right (hpoint c) (coins c)
      _ = _ := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
        congr 2
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro c
        by_cases hc : good c <;> simp [hc]
  exact ⟨hdirection actual ideal (fun c hc => (hgood c hc).1),
    hdirection ideal actual (fun c hc => (hgood c hc).2)⟩

end Zcash.Snark.ZeroKnowledge
