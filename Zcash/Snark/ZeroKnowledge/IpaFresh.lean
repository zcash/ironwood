import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaChallenges
import Zcash.Common.Probability.Distribution

/-!
# Joint IPA simulation with fresh verifier challenges

The verifier's challenge tape is sampled independently of the prover's masks and blinds,
and is retained in the view. The comparison includes zero-challenge executions: their
probability is added to the bound rather than conditioned away. These are interactive
coin experiments, not Fiat–Shamir experiments.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The view retains all verifier coins, including coins unused after an eventual abort. -/
abbrev IpaFreshView (k : ℕ) (G : Type*) := IpaChallengeTape k Fp × IpaTranscript k Fp G

/-- The ideal honest computation with an independent verifier tape. -/
noncomputable def freshIdealIpaProver {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) :
    PMF (IpaFreshView k G) :=
  law.bind fun challenges =>
    (idealIpaProver (pub.withChallenges challenges) coefficients rho).map (Prod.mk challenges)

/-- The same joint computation with the implemented prover sampling law. -/
noncomputable def freshSampledIpaProver {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) :
    PMF (IpaFreshView k G) :=
  law.bind fun challenges =>
    (sampledIpaProver (pub.withChallenges challenges) coefficients rho).map (Prod.mk challenges)

/-- The simulator uses the same verifier tape law and the existing public-input IPA simulator. -/
noncomputable def freshIpaSimulator {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) : PMF (IpaFreshView k G) :=
  law.bind fun challenges =>
    (idealIpaSimulator (pub.withChallenges challenges)).map (Prod.mk challenges)

/-- Ideal masks give a joint simulation bound equal to the actual zero-challenge probability. -/
theorem freshIdealIpa_simulation_error_bound {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    PMFEventBiasLE (freshIdealIpaProver law pub coefficients rho) (freshIpaSimulator law pub)
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges}) ∧
      PMFEventBiasLE (freshIpaSimulator law pub) (freshIdealIpaProver law pub coefficients rho)
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges}) := by
  apply mixedLaws_error_bound law _ _ IpaChallengesNonzero
  intro challenges hgood
  rw [idealIpa_simulation_capstone (pub.withChallenges challenges) coefficients rho
    hW hgood.1 hcommit hv hgood.2]

/-- Changing only the prover's coins costs `3k+1` sample biases for every verifier tape. -/
theorem freshIpa_sampling_error_bound {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) :
    PMFEventBiasLE (freshSampledIpaProver law pub coefficients rho)
        (freshIdealIpaProver law pub coefficients rho) (ipaSampleCount k * challenge255Bias) ∧
      PMFEventBiasLE (freshIdealIpaProver law pub coefficients rho)
        (freshSampledIpaProver law pub coefficients rho) (ipaSampleCount k * challenge255Bias) := by
  constructor
  · apply PMFEventBiasLE.bind_same
    intro challenges
    exact eventBias_map (sampledIpaProver_ideal_error_bound
      (pub.withChallenges challenges) coefficients rho).1 (Prod.mk challenges)
  · apply PMFEventBiasLE.bind_same
    intro challenges
    exact eventBias_map (sampledIpaProver_ideal_error_bound
      (pub.withChallenges challenges) coefficients rho).2 (Prod.mk challenges)

/-- Joint simulation with actual prover samples and no nonzero-challenge premise. -/
theorem freshIpa_simulation_error_bound {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    PMFEventBiasLE (freshSampledIpaProver law pub coefficients rho) (freshIpaSimulator law pub)
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} +
          ipaSampleCount k * challenge255Bias) ∧
      PMFEventBiasLE (freshIpaSimulator law pub) (freshSampledIpaProver law pub coefficients rho)
        (law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} +
          ipaSampleCount k * challenge255Bias) := by
  have hs := freshIpa_sampling_error_bound law pub coefficients rho
  have hi := freshIdealIpa_simulation_error_bound law pub coefficients rho hW hcommit hv
  exact ⟨hs.1.trans hi.1, by simpa [add_comm] using hi.2.trans hs.2⟩

/-- A concrete bound when the independent verifier tape also uses wide reduction.

At `k = 11` this is `12/p + 47 × bias`. It includes zero challenges and the actual prover
sampling law, but still assumes independent interactive verifier coins. -/
theorem wideFreshIpa_simulation_error_bound {k : ℕ}
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W))
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    PMFEventBiasLE (freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho)
        (freshIpaSimulator (wideIpaChallenges k) pub)
        (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (freshIpaSimulator (wideIpaChallenges k) pub)
        (freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho)
        (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := freshIpa_simulation_error_bound (wideIpaChallenges k) pub coefficients rho hW hcommit hv
  have hbound : (wideIpaChallenges k).toOuterMeasure
      {challenges | ¬ IpaChallengesNonzero challenges} + ipaSampleCount k * challenge255Bias ≤
        ((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias := by
    calc
      _ ≤ (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((k + 2 : ℕ) : ℝ≥0∞) * challenge255Bias) + ipaSampleCount k * challenge255Bias :=
        add_le_add (wideIpaChallenges_bad_le k) le_rfl
      _ = _ := by
        rw [add_assoc, ← add_mul, ← Nat.cast_add]
        congr 3
        rw [ipaSampleCount_eq]
        omega
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hbound),
    fun event => (h.2 event).trans (add_le_add le_rfl hbound)⟩

end Zcash.Snark.ZeroKnowledge
