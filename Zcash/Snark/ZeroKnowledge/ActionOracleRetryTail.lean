import Zcash.Snark.ZeroKnowledge.ActionOracleBits
import Zcash.Snark.ZeroKnowledge.ActionRetryBounds
import Zcash.Snark.ZeroKnowledge.PlonkRawObservation
import Zcash.Snark.ZeroKnowledge.OracleRetryTail
import Zcash.Snark.ZeroKnowledge.StatefulRetryGeometric

/-!
# A retry bound uniform in the existing oracle cache

Programming conflicts stop the simulator. They cannot increase its retry rate.
Consequently its retry rate is bounded by the independent simulator's failure
budget plus the cost of reducing its own private field tape. This bound holds
for every preceding cache, even one produced by earlier failed attempts.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The uniform retry budget of the fixed-bit simulator, including its private sampling bias. -/
noncomputable def actionOracleRetryRate (actions : ℕ) : ℝ≥0∞ :=
  plonkCommonFailureBound actions + (132 * actions + 36 : ℕ) * challenge255Bias

/-- Erasing the raw trace recovers the original simulator's complete encoded attempt. -/
theorem actionZkDigestSimulator_observed [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (initial : List (TranscriptElt Fp VestaG)) :
    (actionZkDigestSimulator urs hk inputs).map
        (fun view => (plonkRawOracleView initial view.1 view.2.2).1) =
      (actionZkSimulator urs hk inputs).map Prod.snd := by
  rw [actionZkDigestSimulator_raw_law]
  have h := rawDigestChallengeExperiment_observed
    (idealPlonkVerifierSimulator urs
      (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionPublicPolynomials inputs)) initial
  simpa only [actionZkSimulator, freshPlonkVerifierSimulator, PMF.map_comp, Function.comp_def] using h

set_option maxRecDepth 4096 in
/-- Cache programming can only remove retries from the independent simulator experiment. -/
theorem actionOracleSimulator_retry_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (oracleRetryTransition (actionOracleSimulator urs hk inputs vkTranscriptRepr) cache).toOuterMeasure
      {observation | observation.1 ∈ oracleRetrySet} ≤ plonkCommonFailureBound actions := by
  let law := actionZkDigestSimulator urs hk inputs
  have hprogram := programOracleView_retry_le law cache
    (fun view => plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) view.1 view.2.2)
  dsimp only [law] at hprogram
  rw [actionZkDigestSimulator_observed] at hprogram
  have hbound : ((actionZkSimulator urs hk inputs).map Prod.snd).toOuterMeasure
      {attempt | callerRetryAfterFailure attempt.status = true} ≤ plonkCommonFailureBound actions := by
    simpa only [PMF.toOuterMeasure_map_apply, plonkObservedRetrySet, Set.preimage_setOf_eq] using
      wideActionZkSimulator_retry_le urs hk inputs witness hvalid hW
  have h := hprogram.trans hbound
  simpa only [oracleRetryTransition, actionOracleSimulator, PMF.map_comp, Function.comp_def,
    actionOracleProgramView] using h

/-- The simulator's retry rate stays bounded independently of the retained cache. -/
theorem actionOracleBitSimulator_retry_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) cache).toOuterMeasure
      {observation | observation.1 ∈ oracleRetrySet} ≤ actionOracleRetryRate actions := by
  have h := actionOracleWideSimulator_error_bound urs hk inputs vkTranscriptRepr cache
  rw [← actionOracleBitSimulator_law,
    actionOracleSimulatorProgram_law urs hk inputs hW vkTranscriptRepr cache] at h
  have hb := eventBias_map h.1 (oracleAttemptState cache)
    {observation | observation.1 ∈ oracleRetrySet}
  have hr := actionOracleSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr cache
  exact hb.trans (by
    simpa only [hk, plonkSimulatorSampleCount_eleven, actionOracleRetryRate] using add_le_add hr le_rfl)

/-- Every finite simulator retry budget has the same geometric exhaustion bound, despite the shared cache. -/
theorem actionOracleBitRetries_exhaustion_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (oracleRetries (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) budget cache).toOuterMeasure
      {output | output.1.exhausted = true} ≤ actionOracleRetryRate actions ^ budget :=
  statefulRetries_exhaustion_le _ oracleRetrySet (actionOracleRetryRate actions)
    (actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr) budget cache

end Zcash.Snark.ZeroKnowledge
