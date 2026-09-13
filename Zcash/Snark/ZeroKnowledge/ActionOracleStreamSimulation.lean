import Zcash.Snark.ZeroKnowledge.ActionOracleStream
import Zcash.Snark.ZeroKnowledge.ActionOracleRetryGeometric
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamLimit

/-!
# Statistical simulation of the complete shared-oracle Action history

The same retained-state potential bounds every measurable test of the entire
stream. The observation includes each attempted result and cache update, and
retains infinite failed histories. The simulator is the existing public bit
program. Its uniform retry bound is used in the hybrid; real termination is
not assumed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Every finite history retains its full comparison when all intermediate caches are also observed. -/
theorem actionOracleRetryRecorded_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) :
    PMFEventBiasLE
        (statefulRetryRecorded (oracleRetryTransition (actionOracleProver urs hk inputs witness vkTranscriptRepr)) oracleRetrySet budget cache)
        (statefulRetryRecorded (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr)) oracleRetrySet budget cache)
        (oracleRetryPotential actions cache.length) ∧
      PMFEventBiasLE
        (statefulRetryRecorded (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr)) oracleRetrySet budget cache)
        (statefulRetryRecorded (oracleRetryTransition (actionOracleProver urs hk inputs witness vkTranscriptRepr)) oracleRetrySet budget cache)
        (oracleRetryPotential actions cache.length) := by
  apply statefulRetryRecorded_potential_error_bound
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

/-- Every measurable event of the full shared-oracle history has the same two-sided uniform comparison. -/
theorem actionOracleRetryStream_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    MeasureEventBiasLE (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache) (oracleRetryPotential actions cache.length) ∧
      MeasureEventBiasLE (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache)
        (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache) (oracleRetryPotential actions cache.length) := by
  apply statefulRetryStreamLaw_simulation_error_bound _ _ oracleRetrySet cache
  intro budget
  simp_rw [actionRawOracleStep_law, actionBitOracleStep_law]
  exact actionOracleRetryRecorded_error_bound urs hk inputs witness hvalid hpositive hW hhalf vkTranscriptRepr budget cache

/-- The concrete arithmetic certificate supplies the shared-oracle potential's numerical premise. -/
theorem wideUnlimitedActionOracle_simulation_capstone [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 1 ≤ actions) (hsize : actions ≤ 65535) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    MeasureEventBiasLE (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache) (oracleRetryPotential actions cache.length) ∧
      MeasureEventBiasLE (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache)
        (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache) (oracleRetryPotential actions cache.length) :=
  actionOracleRetryStream_simulation_error_bound urs hk inputs witness hvalid hpositive hW
    (actionOracleRetryRate_lt_half hpositive hsize).le vkTranscriptRepr cache

end Zcash.Snark.ZeroKnowledge
