import Zcash.Snark.ZeroKnowledge.ActionGeneratorStream
import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedPrng
import Zcash.Snark.ZeroKnowledge.ActionOracleStreamTermination
import Zcash.Snark.ZeroKnowledge.MeasureBiasComposition

/-!
# Computational simulation of the complete seeded Action retry stream

Two admitted finite reductions suffice: the test of the clipped complete view,
and the actual finite exhaustion bit. The latter controls the seeded execution's
truncation loss, without assuming independent generated blocks or almost-sure
termination of the seeded prover. One whole-prefix PRNG bound is charged twice.
The simulator is the existing witness-free fixed-bit shared-oracle stream.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open MeasureTheory Zcash.Common
open scoped ENNReal

/-- Testing a clipped seeded stream is exactly the finite generated-prefix view test. -/
theorem actionGeneratedOracleRetryStream_test_truncate {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState)
    (test : (ℕ → ActionRetryStreamEntry) → Bool) (hmeasurable : Measurable test) :
    ((actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache).map
      (truncateRetryStream budget)).map test =
      ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
        (uniformSeedTapeSource seedBits (fun seed => actionGeneratorRetryTape next actions budget (initState seed)))
        cache).map (fun output => test (fun index => output.1.attempts[index]?))).toMeasure := by
  rw [actionGeneratedOracleRetryStream_truncate, pmfObservedMeasure_map _ _ test hmeasurable]

/-- The fixed-bit simulator's clipped test is the same test of its finite recorded history. -/
theorem actionOracleBitRetryStream_test_truncate {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState)
    (test : (ℕ → ActionRetryStreamEntry) → Bool) (hmeasurable : Measurable test) :
    ((actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map (truncateRetryStream budget)).map test =
      ((statefulRetryRecorded (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr))
        oracleRetrySet budget cache).map (fun output => test (fun index => output.1.attempts[index]?))).toMeasure := by
  have h := congrArg (fun law : Measure (ℕ → ActionRetryStreamEntry) => law.map test)
    (statefulRetryStreamLaw_truncate (actionBitOracleStep urs hk inputs vkTranscriptRepr)
      oracleRetrySet budget cache)
  dsimp only at h
  rw [pmfObservedMeasure_map _ _ test hmeasurable] at h
  simp_rw [actionBitOracleStep_law] at h
  exact h

/-- The uniform private-prefix test is statistically simulated with the budget-independent potential. -/
theorem actionOracleRecord_uniform_test_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState)
    (test : (ℕ → ActionRetryStreamEntry) → Bool) (hmeasurable : Measurable test) :
    let actual := ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
      (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache).map
        (fun output => test (fun index => output.1.attempts[index]?))).toMeasure
    let ideal := ((actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map (truncateRetryStream budget)).map test
    MeasureEventBiasLE actual ideal (oracleRetryPotential actions cache.length) ∧
      MeasureEventBiasLE ideal actual (oracleRetryPotential actions cache.length) := by
  dsimp only
  rw [actionOracleBitRetryStream_test_truncate urs hk inputs vkTranscriptRepr budget cache test hmeasurable]
  have h := actionOracleRetryRecorded_error_bound urs hk inputs witness hvalid hpositive hW hhalf vkTranscriptRepr budget cache
  rw [← actionOracleRecordFromSource_uniform urs hk inputs witness vkTranscriptRepr budget cache] at h
  exact ⟨eventBias_toMeasure (eventBias_map h.1 (fun output => test (fun index => output.1.attempts[index]?))),
    eventBias_toMeasure (eventBias_map h.2 (fun output => test (fun index => output.1.attempts[index]?)))⟩

/-- The complete seeded history is simulated under the two displayed whole-prefix PRNG reductions. -/
theorem generatedUnlimitedActionOracle_test_error_bound [Fintype VestaG] {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (next : Generator → Fin challengeDigestCard × Generator)
    (seedBits : ℕ) (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState)
    (test : (ℕ → ActionRetryStreamEntry) → Bool) (hmeasurable : Measurable test)
    (admissible : Set (Unit → RawPrivateRetryTape actions budget → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits
      (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) (PMF.pure ()) admissible η)
    (hview : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => test (fun index => output.1.attempts[index]?)) ∈ admissible)
    (htail : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => output.1.exhausted) ∈ admissible) :
    let actual := (actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache).map test
    let ideal := (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map test
    let error := 2 * (oracleRetryPotential actions cache.length + actionOracleRetryRate actions ^ budget + η)
    MeasureEventBiasLE actual ideal error ∧ MeasureEventBiasLE ideal actual error := by
  dsimp only
  have htailBound := actionOracleRecordPrng_exhaustion_le urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache seedBits
    (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) admissible η secure htail
  have htruncate := actionGeneratedOracleRetryStream_truncation_error_bound urs hk inputs witness vkTranscriptRepr
    next seedBits initState budget cache
  have hfirst := measureEventBias_map (htruncate.1.mono htailBound) test hmeasurable
  have hfirstReverse := measureEventBias_map (htruncate.2.mono htailBound) test hmeasurable
  rw [actionGeneratedOracleRetryStream_test_truncate urs hk inputs witness vkTranscriptRepr
    next seedBits initState budget cache test hmeasurable] at hfirst hfirstReverse
  have hsource := actionOracleRecordPrng_test_error_bound urs hk inputs witness vkTranscriptRepr budget cache seedBits
    (fun seed => actionGeneratorRetryTape next actions budget (initState seed))
    (fun output => test (fun index => output.1.attempts[index]?)) admissible η secure hview
  have hsimulate := actionOracleRecord_uniform_test_simulation_error_bound urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache test hmeasurable
  have hlast := actionOracleBitRetryStream_truncation_error_bound urs hk inputs witness hvalid hW
    vkTranscriptRepr budget cache
  have hf := hfirst.trans ((eventBias_toMeasure hsource.1).trans
    (hsimulate.1.trans (measureEventBias_map hlast.2 test hmeasurable)))
  have hr := (measureEventBias_map hlast.1 test hmeasurable).trans
    (hsimulate.2.trans ((eventBias_toMeasure hsource.2).trans hfirstReverse))
  constructor
  · simpa only [two_mul, add_assoc, add_comm, add_left_comm] using hf
  · simpa only [two_mul, add_assoc, add_comm, add_left_comm] using hr

/-- The Action-count certificate supplies the numerical retry premise for the unlimited seeded reduction. -/
theorem generatedUnlimitedActionOracle_simulation_capstone [Fintype VestaG] {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 1 ≤ actions) (hsize : actions ≤ 65535) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp) (next : Generator → Fin challengeDigestCard × Generator)
    (seedBits : ℕ) (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState)
    (test : (ℕ → ActionRetryStreamEntry) → Bool) (hmeasurable : Measurable test)
    (admissible : Set (Unit → RawPrivateRetryTape actions budget → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits
      (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) (PMF.pure ()) admissible η)
    (hview : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => test (fun index => output.1.attempts[index]?)) ∈ admissible)
    (htail : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => output.1.exhausted) ∈ admissible) :
    let actual := (actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache).map test
    let ideal := (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map test
    let error := 2 * (oracleRetryPotential actions cache.length + actionOracleRetryRate actions ^ budget + η)
    MeasureEventBiasLE actual ideal error ∧ MeasureEventBiasLE ideal actual error :=
  generatedUnlimitedActionOracle_test_error_bound urs hk inputs witness hvalid hpositive hW
    (actionOracleRetryRate_lt_half hpositive hsize).le vkTranscriptRepr next seedBits initState budget cache
    test hmeasurable admissible η secure hview htail

end Zcash.Snark.ZeroKnowledge
