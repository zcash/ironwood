import Zcash.Snark.ZeroKnowledge.ActionOracleRetryTail
import Zcash.Snark.ZeroKnowledge.ActionOracleRetryResources
import Zcash.Snark.ZeroKnowledge.OracleRetryPotential

/-!
# A comparison uniform in the shared-oracle retry budget

The simulator's cache-independent retry rate pays the later comparisons
geometrically. For rate at most one half, every finite budget has error at most
`2 * Gamma(m, q + 22)`. Exhaustion is at most `b^n` for the simulator and
`b^n + 2 * Gamma(m, q + 22)` for the real shared-oracle process. In particular,
this does not silently assume that the real process terminates almost surely.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The simulator retry budget is no larger than twice its zero-prior-query simulation budget. -/
theorem actionOracleRetryRate_le_twice_error (actions : ℕ) :
    actionOracleRetryRate actions ≤ 2 * plonkBitSimulationErrorBound actions 0 := by
  have hf : plonkAttemptFailureBound actions ≤ plonkSimulationErrorBound actions := by
    unfold plonkAttemptFailureBound plonkSimulationErrorBound
    apply add_le_add
    · apply ENNReal.div_le_div_right
      exact_mod_cast (show 22 * actions + 45 ≤ 42882 * actions + 4113 by omega)
    · apply mul_le_mul_left
      exact_mod_cast (show 148 * actions + 68 ≤ 148 * actions + 70 by omega)
  simp only [actionOracleRetryRate, plonkCommonFailureBound, plonkBitSimulationErrorBound,
    Nat.cast_zero, ENNReal.zero_div, add_zero]
  calc
    _ ≤ (plonkSimulationErrorBound actions + plonkSimulationErrorBound actions) +
        (132 * actions + 36 : ℕ) * challenge255Bias := add_le_add (add_le_add hf le_rfl) le_rfl
    _ ≤ _ := by
      have he : plonkSimulationErrorBound actions ≤ plonkSimulationErrorBound actions +
          (132 * actions + 36 : ℕ) * challenge255Bias := le_self_add
      simpa only [two_mul, add_assoc] using add_le_add he
        (le_rfl (a := plonkSimulationErrorBound actions + (132 * actions + 36 : ℕ) * challenge255Bias))

set_option exponentiation.threshold 1024 in
/-- The already documented finite arithmetic range makes the uniform retry rate smaller than one half. -/
theorem actionOracleRetryRate_lt_half {actions : ℕ} (hpositive : 1 ≤ actions) (hsize : actions ≤ 65535) :
    actionOracleRetryRate actions < 1 / 2 := by
  have hbit := plonkBitSimulationErrorBound_lt_actions_mul_two_pow hpositive 0
  simp only [Nat.cast_zero, ENNReal.zero_div, add_zero] at hbit
  apply (actionOracleRetryRate_le_twice_error actions).trans_lt
  apply ((ENNReal.mul_lt_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).2 hbit).trans_le
  calc
    _ ≤ 2 * ((65535 : ℝ≥0∞) * (1 / 2 ^ 238)) := by gcongr; exact_mod_cast hsize
    _ ≤ 1 / 2 := by
      have hp0 : (2 : ℝ≥0∞) ^ 238 ≠ 0 := pow_ne_zero _ (by norm_num)
      have hpt : (2 : ℝ≥0∞) ^ 238 ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      apply (ENNReal.mul_le_mul_iff_left hp0 hpt).1
      rw [mul_assoc, mul_assoc, ENNReal.div_mul_cancel hp0 hpt, mul_one]
      have ht : (2 : ℝ≥0∞) ^ 238 = 2 * 2 ^ 237 := pow_succ' _ _
      rw [ht, ← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul]
      exact_mod_cast (show 2 * 65535 ≤ 2 ^ 237 by decide)

/-- The complete retained-history comparison is bounded independently of the available attempt budget. -/
theorem actionOracleRetries_uniform_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMFEventBiasLE (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache)
        (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache)
        (oracleRetryPotential actions cache.length) ∧
      PMFEventBiasLE (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache)
        (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache)
        (oracleRetryPotential actions cache.length) := by
  apply statefulRetries_potential_error_bound
    (oracleRetryTransition (actionOracleProver urs hk inputs witness vkTranscriptRepr))
    (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr))
    oracleRetrySet List.length 22 (plonkBitSimulationErrorBound actions)
    (oracleRetryPotential actions) (actionOracleRetryRate actions)
  · intro bound prior hprior
    have h := actionOracleBit_simulation_error_bound urs hk inputs witness hvalid hpositive hW vkTranscriptRepr prior
    have he := plonkBitSimulationErrorBound_mono_queries actions hprior
    exact ⟨eventBias_map (fun event => (h.1 event).trans (add_le_add le_rfl he)) (oracleAttemptState prior),
      eventBias_map (fun event => (h.2 event).trans (add_le_add le_rfl he)) (oracleAttemptState prior)⟩
  · intro prior observation hobs
    rw [oracleRetryTransition, PMF.mem_support_map_iff] at hobs
    obtain ⟨raw, hraw, rfl⟩ := hobs
    exact actionOracleBitSimulator_cache_length_le urs hk inputs vkTranscriptRepr prior raw hraw
  · exact actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr
  · exact fun bound => oracleRetryPotential_step actions bound hhalf
  · exact le_rfl

/-- Real shared-oracle exhaustion has the simulator's geometric tail plus the uniform comparison loss. -/
theorem actionOracleRetries_exhaustion_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache).toOuterMeasure
      {output | output.1.exhausted = true} ≤
        actionOracleRetryRate actions ^ budget + oracleRetryPotential actions cache.length := by
  have h := (actionOracleRetries_uniform_error_bound urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache).1 {output | output.1.exhausted = true}
  exact h.trans (add_le_add (actionOracleBitRetries_exhaustion_le urs hk inputs witness hvalid hW
    vkTranscriptRepr budget cache) le_rfl)

end Zcash.Snark.ZeroKnowledge
