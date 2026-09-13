import Zcash.Snark.ZeroKnowledge.IpaFailures
import Zcash.Common.Probability.Retry

/-!
# Simulating successful IPA attempts

The attempt observer determines success on both sides of the simulation comparison.
Its normalizing probability remains explicit. For the eleven-round protocol we prove
that both honest and simulated success probabilities are positive, rather than assuming
the filter is defined. Independent retries converge to these conditioned laws.

This is the IPA experiment with a fixed public opening. A complete prover may restart
earlier PLONK stages too; its retry behavior still requires that full attempt model.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The raw transcript is a finite tuple of its actual fields. -/
def ipaTranscriptEquiv {k : ℕ} {F G : Type*} :
    IpaTranscript k F G ≃ (G × (Fin k → G × G) × F × F) where
  toFun view := (view.maskCommitment, view.messages, view.scalar, view.blind)
  invFun parts := ⟨parts.1, parts.2.1, parts.2.2.1, parts.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {k : ℕ} {F G : Type*} [Fintype F] [Fintype G] : Fintype (IpaTranscript k F G) :=
  Fintype.ofEquiv (G × (Fin k → G × G) × F × F) ipaTranscriptEquiv.symm

instance {k : ℕ} {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) :
    DecidablePred (fun view : IpaFreshView k G => view ∈ ipaSuccessSet pointCodec scalarCodec) :=
  fun view => inferInstanceAs (Decidable ((observeIpaAttempt pointCodec scalarCodec view).status = .complete))

/-- Observe the encoded view of a successful attempt, using its actual conditioning mass. -/
noncomputable def successfulIpaView {k : ℕ} {G : Type*} (law : PMF (IpaFreshView k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (h : ∃ view ∈ ipaSuccessSet pointCodec scalarCodec, view ∈ law.support) :
    PMF (IpaChallengeTape k Fp × IpaAttemptResult) :=
  (law.filter (ipaSuccessSet pointCodec scalarCodec) h).map (ipaAttemptObservation pointCodec scalarCodec)

/-- A common upper bound on honest and simulated failure, before any normalization. -/
noncomputable def ipaRetryFailureBound (k : ℕ) : ℝ≥0∞ :=
  ((4 * k + 2 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
    ((2 * (4 * k + 3) : ℕ) : ℝ≥0∞) * challenge255Bias

set_option exponentiation.threshold 1024 in
/-- The pinned eleven-round common failure bound is strictly less than one. -/
theorem ipaRetryFailureBound_eleven_lt_one : ipaRetryFailureBound 11 < 1 := by
  calc
    _ ≤ (46 : ℝ≥0∞) / scalarFieldOrder + 94 * (1 / 2 ^ 260) := by
      change (46 : ℝ≥0∞) / scalarFieldOrder + 94 * challenge255Bias ≤ _
      exact add_le_add le_rfl (mul_le_mul_right fieldSample_bias_le 94)
    _ < 1 := by
      have hp0 : (scalarFieldOrder : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
      have hpt : (scalarFieldOrder : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hb0 : (2 : ℝ≥0∞) ^ 260 ≠ 0 := pow_ne_zero _ (by simp)
      have hbt : (2 : ℝ≥0∞) ^ 260 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have hnum : (46 : ℝ≥0∞) * 2 ^ 260 + 94 * scalarFieldOrder <
          scalarFieldOrder * 2 ^ 260 := by
        exact_mod_cast (show 46 * 2 ^ 260 + 94 * scalarFieldOrder < scalarFieldOrder * 2 ^ 260 by decide)
      apply (ENNReal.mul_lt_mul_iff_left hp0 hpt).1
      apply (ENNReal.mul_lt_mul_iff_left hb0 hbt).1
      calc
        _ = ((46 : ℝ≥0∞) / scalarFieldOrder * scalarFieldOrder) * 2 ^ 260 +
            94 * scalarFieldOrder * ((1 / 2 ^ 260) * 2 ^ 260) := by ring
        _ = 46 * 2 ^ 260 + 94 * scalarFieldOrder := by
          rw [ENNReal.div_mul_cancel hp0 hpt, ENNReal.div_mul_cancel hb0 hbt, mul_one]
        _ < _ := by simpa only [one_mul] using hnum

section Simulation

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Successful encoded views inherit the simulation bound, divided by their respective masses. -/
theorem successfulIpa_simulation_error_bound {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value)
    (ha : ∃ view ∈ ipaSuccessSet pointCodec scalarCodec,
      view ∈ (freshSampledIpaProver law pub coefficients rho).support)
    (hi : ∃ view ∈ ipaSuccessSet pointCodec scalarCodec, view ∈ (freshIpaSimulator law pub).support) :
    let ε := law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} +
      ipaSampleCount k * challenge255Bias
    PMFEventBiasLE
        (successfulIpaView (freshSampledIpaProver law pub coefficients rho) pointCodec scalarCodec ha)
        (successfulIpaView (freshIpaSimulator law pub) pointCodec scalarCodec hi)
        ((ε + ε) / (freshSampledIpaProver law pub coefficients rho).toOuterMeasure
          (ipaSuccessSet pointCodec scalarCodec)) ∧
      PMFEventBiasLE
        (successfulIpaView (freshIpaSimulator law pub) pointCodec scalarCodec hi)
        (successfulIpaView (freshSampledIpaProver law pub coefficients rho) pointCodec scalarCodec ha)
        ((ε + ε) / (freshIpaSimulator law pub).toOuterMeasure (ipaSuccessSet pointCodec scalarCodec)) := by
  have h := freshIpa_simulation_error_bound law pub coefficients rho hW hcommit hv
  have hc := conditioned_simulation_error_bound h.1 h.2 (ipaSuccessSet pointCodec scalarCodec) ha hi
  exact ⟨eventBias_map hc.1 _, eventBias_map hc.2 _⟩

/-- Both unconditioned experiments obey the stated common failure bound. -/
theorem wideIpa_retry_failure_le {k : ℕ}
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    (freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho).toOuterMeasure
        (ipaSuccessSet pointCodec scalarCodec)ᶜ ≤ ipaRetryFailureBound k ∧
      (freshIpaSimulator (wideIpaChallenges k) pub).toOuterMeasure
        (ipaSuccessSet pointCodec scalarCodec)ᶜ ≤ ipaRetryFailureBound k := by
  have ha := wideFreshIpa_failure_le pub coefficients rho pointCodec scalarCodec hcodec hW
  have hs := (wideFreshIpa_simulation_error_bound pub coefficients rho hW hcommit hv).2
  have hi := event_measure_le_of_bias hs _ ha
  have hbudget :
      (((3 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) +
      (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) = ipaRetryFailureBound k := by
    simp only [ipaRetryFailureBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
    ring
  constructor
  · exact ha.trans ((le_self_add).trans_eq hbudget)
  · exact hi.trans_eq hbudget

/-- The fixed eleven-round honest and simulated IPA laws both have supported successful outputs. -/
theorem wideIpa_eleven_success_support
    (pub : IpaPublic 11 Fp G) (coefficients : Fin (2 ^ 11) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation 11 pub.point coefficients = pub.value) :
    (∃ view ∈ ipaSuccessSet pointCodec scalarCodec,
      view ∈ (freshSampledIpaProver (wideIpaChallenges 11) pub coefficients rho).support) ∧
      (∃ view ∈ ipaSuccessSet pointCodec scalarCodec,
        view ∈ (freshIpaSimulator (wideIpaChallenges 11) pub).support) := by
  have h := wideIpa_retry_failure_le pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv
  exact ⟨exists_success_of_failure_lt_one _ _ (h.1.trans_lt ipaRetryFailureBound_eleven_lt_one),
    exists_success_of_failure_lt_one _ _ (h.2.trans_lt ipaRetryFailureBound_eleven_lt_one)⟩

omit [Fintype G] in
/-- Every public commitment has an opening of its claimed value as an existence fact.

This uses surjectivity of the blinding map only inside a proof. It supplies the simulator's
positive-success certificate; it does not give the simulator a discrete-log algorithm. -/
theorem IpaPublic.exists_opening {k : ℕ} (pub : IpaPublic k Fp G)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    ∃ coefficients : Fin (2 ^ k) → Fp, ∃ rho : Fp,
      pub.commitment = commitGen pub.generators coefficients + rho • pub.W ∧
        coefficientEvaluation k pub.point coefficients = pub.value := by
  classical
  let coefficients : Fin (2 ^ k) → Fp := Pi.single 0 pub.value
  obtain ⟨rho, hrho⟩ := hW.2 (pub.commitment - commitGen pub.generators coefficients)
  change rho • pub.W = pub.commitment - commitGen pub.generators coefficients at hrho
  refine ⟨coefficients, rho, ?_, ?_⟩
  · rw [hrho]
    abel
  · unfold coefficientEvaluation
    rw [Finset.sum_eq_single 0]
    · simp [coefficients]
    · intro i _ hi
      simp [coefficients, Pi.single_eq_of_ne hi]
    · simp

/-- The public-input simulator can succeed without being supplied an honest witness. -/
theorem wideIpaSimulator_success_support (pub : IpaPublic 11 Fp G)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    ∃ view ∈ ipaSuccessSet pointCodec scalarCodec,
      view ∈ (freshIpaSimulator (wideIpaChallenges 11) pub).support := by
  obtain ⟨coefficients, rho, hcommit, hv⟩ := pub.exists_opening hW
  exact (wideIpa_eleven_success_support pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv).2

/-- The successful wide-reduced honest IPA law, with its normalizer proved positive. -/
noncomputable def wideSuccessfulIpaProver (pub : IpaPublic 11 Fp G)
    (coefficients : Fin (2 ^ 11) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation 11 pub.point coefficients = pub.value) :
    PMF (IpaChallengeTape 11 Fp × IpaAttemptResult) :=
  successfulIpaView (freshSampledIpaProver (wideIpaChallenges 11) pub coefficients rho)
    pointCodec scalarCodec
    (wideIpa_eleven_success_support pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv).1

/-- The successful public-input IPA simulator, with no witness or commitment blind argument. -/
noncomputable def wideSuccessfulIpaSimulator (pub : IpaPublic 11 Fp G)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    PMF (IpaChallengeTape 11 Fp × IpaAttemptResult) :=
  successfulIpaView (freshIpaSimulator (wideIpaChallenges 11) pub) pointCodec scalarCodec
    (wideIpaSimulator_success_support pub pointCodec scalarCodec hcodec hW)

/-- Joint simulation of successful eleven-round IPA views under the implemented field law.

For `ε = 12/p + 47 × bias` and `B = 46/p + 94 × bias`, both event-bias directions are
at most `2ε/(1-B)`. The denominator is positive by `ipaRetryFailureBound_eleven_lt_one`.
The simulator depends only on the public opening, codecs, and parameter certificates. -/
theorem wideSuccessfulIpa_simulation_capstone
    (pub : IpaPublic 11 Fp G) (coefficients : Fin (2 ^ 11) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation 11 pub.point coefficients = pub.value) :
    let ε := (12 : ℝ≥0∞) / scalarFieldOrder + 47 * challenge255Bias
    PMFEventBiasLE
        (wideSuccessfulIpaProver pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv)
        (wideSuccessfulIpaSimulator pub pointCodec scalarCodec hcodec hW)
        (2 * ε / (1 - ipaRetryFailureBound 11)) ∧
      PMFEventBiasLE
        (wideSuccessfulIpaSimulator pub pointCodec scalarCodec hcodec hW)
        (wideSuccessfulIpaProver pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv)
        (2 * ε / (1 - ipaRetryFailureBound 11)) := by
  have h := wideFreshIpa_simulation_error_bound pub coefficients rho hW hcommit hv
  have hf := wideIpa_retry_failure_le pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv
  have ha := (wideIpa_eleven_success_support pub coefficients rho pointCodec scalarCodec hcodec hW hcommit hv).1
  have hi := wideIpaSimulator_success_support pub pointCodec scalarCodec hcodec hW
  have hc := conditioned_common_error_bound h.1 h.2 (ipaSuccessSet pointCodec scalarCodec) ha hi
    (success_mass_lower_bound _ _ hf.1) (success_mass_lower_bound _ _ hf.2)
  exact ⟨by simpa only [two_mul] using eventBias_map hc.1 (ipaAttemptObservation pointCodec scalarCodec),
    by simpa only [two_mul] using eventBias_map hc.2 (ipaAttemptObservation pointCodec scalarCodec)⟩

omit [AddCommGroup G] [Module Fp G] [Fintype G] in
/-- Independent retries of the encoded IPA experiment converge to its successful-attempt law. -/
theorem encodedIpa_retries_tendsto {k : ℕ} (law : PMF (IpaFreshView k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (h : ∃ view ∈ ipaSuccessSet pointCodec scalarCodec, view ∈ law.support)
    (event : Set (Option (IpaChallengeTape k Fp × IpaAttemptResult))) :
    Filter.Tendsto (fun n =>
      ((boundedRetries law (ipaSuccessSet pointCodec scalarCodec) n).map
        (Option.map (ipaAttemptObservation pointCodec scalarCodec))).toOuterMeasure event)
      Filter.atTop (nhds (((successfulIpaView law pointCodec scalarCodec h).map some).toOuterMeasure event)) := by
  have hlimit := boundedRetries_tendsto law (ipaSuccessSet pointCodec scalarCodec) h
    ((Option.map (ipaAttemptObservation pointCodec scalarCodec)) ⁻¹' event)
  simpa only [PMF.toOuterMeasure_map_apply, successfulIpaView, Set.preimage_preimage,
    Function.comp_def, Option.map_some] using hlimit

end Simulation

end Zcash.Snark.ZeroKnowledge
