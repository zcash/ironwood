import Zcash.Snark.ZeroKnowledge.OracleResources
import Zcash.Common.Probability.DistributionKernel

/-!
# Oracle preprocessing and continuation

Query-bounded preprocessing produces a correspondingly bounded cache on every
supported execution. A common randomized continuation preserves a simulation
bound, including when it queries the cache adaptively after receiving a proof.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- A common outer experiment preserves a uniform continuation bound on its supported outcomes. -/
theorem eventBias_bind_support {A B : Type*} (law : PMF A)
    {actual ideal : A → PMF B} {error : ℝ≥0∞}
    (h : ∀ value ∈ law.support, PMFEventBiasLE (actual value) (ideal value) error) :
    PMFEventBiasLE (law.bind actual) (law.bind ideal) error := by
  intro event
  simp only [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' value, law value * ((ideal value).toOuterMeasure event + error) := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hz : law value = 0
      · simp only [hz, zero_mul, le_refl]
      · exact mul_le_mul_right (h value hz event) (law value)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- Every supported lazy-oracle execution respects the concrete cache-growth budget. -/
theorem cachedOracleLaw_cache_length_le {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (hbudget : comp.QueryBound budget) (cache : OracleCache Query Reply)
    (view : Value × OracleCache Query Reply) (hview : view ∈ (cachedOracleLaw answerLaw comp cache).support) :
    view.2.length ≤ cache.length + budget := by
  have hsome : some view ∈ ((independentTapeLaw answerLaw budget).map
      (cachedOracleRunTape budget comp cache)).support := by
    rw [cachedOracleRunTape_law answerLaw hbudget cache]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨view, hview, rfl⟩
  obtain ⟨tape, _, hrun⟩ := (PMF.mem_support_map_iff _ _ _).mp hsome
  exact cachedOracleRunTape_cache_length_le budget comp cache tape view hrun

/-- Oracle postprocessing sees the attempt status and continues with the same oracle table.

Programming failure is exposed as `none` and leaves the prior cache unchanged.
An ordinary prover failure is still a `some` attempt carrying its retained prefix.
-/
noncomputable def oracleAttemptContinue {Query Reply Attempt Output : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) (priorCache : OracleCache Query Reply)
    (after : Option Attempt → OracleComp Query Reply Output)
    (observation : Option (Attempt × OracleCache Query Reply)) : PMF (Output × OracleCache Query Reply) :=
  match observation with
  | none => cachedOracleLaw answerLaw (after none) priorCache
  | some (attempt, cache) => cachedOracleLaw answerLaw (after (some attempt)) cache

/-- Adaptive queries after the attempt preserve every two-sided event comparison. -/
theorem oracleAttemptContinue_error_bound {Query Reply Attempt Output : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) (priorCache : OracleCache Query Reply)
    (after : Option Attempt → OracleComp Query Reply Output)
    {actual ideal : PMF (Option (Attempt × OracleCache Query Reply))} {error : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal error) (reverse : PMFEventBiasLE ideal actual error) :
    PMFEventBiasLE (actual.bind (oracleAttemptContinue answerLaw priorCache after))
        (ideal.bind (oracleAttemptContinue answerLaw priorCache after)) error ∧
      PMFEventBiasLE (ideal.bind (oracleAttemptContinue answerLaw priorCache after))
        (actual.bind (oracleAttemptContinue answerLaw priorCache after)) error :=
  ⟨eventBias_bind_kernel forward _, eventBias_bind_kernel reverse _⟩

end Zcash.Snark.ZeroKnowledge
