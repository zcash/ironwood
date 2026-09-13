import Zcash.Snark.ZeroKnowledge.ActionReductionSource

/-!
# The seeded reference prover with its resource condition discharged

The remaining PRNG premise is security of the generated prefix against the
specified operational program class at the derived time and verifier-bit
budgets. The actual reduction's class membership is proved from the complete
implementation; it is not an additional hypothesis. The test is an executable
Boolean circuit over the full public history and stored auxiliary data.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal
attribute [local irreducible] actionReferenceKey

/-- Finite generated-prefix observations inherit simulation with the full real-prover/test runtime already proved. -/
theorem costedActionOracleRecordPrng_test_error_bound [Fintype VestaG] (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
      rfl (fun i : Fin inputs.length => inputs[i.val]) witness)
    (hpositive : 0 < inputs.length) (hW : W ≠ 0) (hhalf : actionOracleRetryRate inputs.length ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateRetryTape inputs.length budget) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (PMF.pure ())
      (actionReductionAdmissible prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) budget
        (recordedPrngTimeBound prices (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
          program budget)) η) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let actual := (actionOracleRecordFromSource urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
      (uniformSeedTapeSource seedBits generate) cache).map (recordedViewTest program auxiliary)
    let ideal := (statefulRetryRecorded (oracleRetryTransition (actionOracleBitSimulator urs rfl
      (fun i : Fin inputs.length => inputs[i.val]) vkTranscriptRepr)) oracleRetrySet budget cache).map (recordedViewTest program auxiliary)
    PMFEventBiasLE actual ideal (oracleRetryPotential inputs.length cache.length + η) ∧
      PMFEventBiasLE ideal actual (oracleRetryPotential inputs.length cache.length + η) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let publicInputs := fun i : Fin inputs.length => inputs[i.val]
  let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
  let admitted := actionReductionAdmissible prices data budget (recordedPrngTimeBound prices data program budget)
  have hmember := actionOracleRecordPrngReduction_mem_ownBudget prices inputs generators W U witness vkTranscriptRepr cache auxiliary program budget
  have hp := actionOracleRecordPrng_test_error_bound urs rfl publicInputs witness vkTranscriptRepr budget cache seedBits generate
    (recordedViewTest program auxiliary) admitted η secure hmember
  have hs := actionOracleRetryRecorded_error_bound urs rfl publicInputs witness hvalid hpositive hW hhalf vkTranscriptRepr budget cache
  rewrite [← actionOracleRecordFromSource_uniform urs rfl publicInputs witness vkTranscriptRepr budget cache] at hs
  exact ⟨hp.1.trans (eventBias_map hs.1 (recordedViewTest program auxiliary)),
    by simpa only [add_comm] using (eventBias_map hs.2 (recordedViewTest program auxiliary)).trans hp.2⟩

/-- The actual generated exhaustion test belongs to the same proved program class. -/
theorem costedActionOracleRecordPrng_exhaustion_le [Fintype VestaG] (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
      rfl (fun i : Fin inputs.length => inputs[i.val]) witness)
    (hpositive : 0 < inputs.length) (hW : W ≠ 0) (hhalf : actionOracleRetryRate inputs.length ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateRetryTape inputs.length budget) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (PMF.pure ())
      (actionReductionAdmissible prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) budget
        (recordedPrngViewAndTailTimeBound prices
          (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) program budget)) η) :
    (actionOracleRecordFromSource ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
      (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr (uniformSeedTapeSource seedBits generate) cache).toOuterMeasure
        {output | output.1.exhausted = true} ≤
      actionOracleRetryRate inputs.length ^ budget + oracleRetryPotential inputs.length cache.length + η := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
  let admitted := actionReductionAdmissible prices data budget (recordedPrngViewAndTailTimeBound prices data program budget)
  have hmember := actionOracleRecordPrngReduction_mem_costed prices inputs generators W U witness vkTranscriptRepr cache auxiliary
    recordedExhaustionTest budget (recordedPrngViewAndTailTimeBound prices data program budget) (Nat.le_max_right _ _)
  exact actionOracleRecordPrng_exhaustion_le urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness
    hvalid hpositive hW hhalf vkTranscriptRepr budget cache seedBits generate admitted η secure hmember

end Zcash.Snark.ZeroKnowledge
