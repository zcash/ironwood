import Zcash.Snark.ZeroKnowledge.PlonkConsistency
import Zcash.Snark.ZeroKnowledge.PlonkChallenges

/-!
# Joint PLONK and IPA simulation with fresh verifier challenges

The view retains the entire challenge tape and the existing verifier's `ProofString`.
Prover coins are sampled independently of that tape. Exceptional challenges and invalid
row states remain in the experiment, with their probabilities charged to the bound.
The row constructor may depend on the challenges, as lookup and product rows must.

This is an offline description of an interactive random-tape experiment. Connecting it
to the actual message schedule, codecs, whole-prover retries, and Fiat–Shamir hashing
requires further results. In particular, independent fresh coins are not a model of
hash outputs conditioned on the eventual proof.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The complete challenge tape is retained alongside the algebraic proof. -/
abbrev PlonkFreshView (actions k : ℕ) (G : Type*) :=
  Challenges k Fp × ProofString (plonkProofShape actions k) Fp G

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Sample independent public challenges, then run the prover with its wide-reduced tape. -/
noncomputable def freshSampledPlonkVerifierProver {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions) :
    PMF (PlonkFreshView actions urs.k G) :=
  law.bind fun ch =>
    (sampledPlonkVerifierProver (construct ch) history urs vk pub ch).map (Prod.mk ch)

/-- The simulator uses only the public input and the same verifier challenge law. -/
noncomputable def freshPlonkVerifierSimulator {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions) :
    PMF (PlonkFreshView actions urs.k G) :=
  law.bind fun ch => (idealPlonkVerifierSimulator urs vk pub ch).map (Prod.mk ch)

/-- Average invalid-row probability under the public challenge law and ideal private row law. -/
noncomputable def freshPlonkInvalidRowMass {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions) : ℝ≥0∞ :=
  ∑' ch, law ch * plonkInvalidRowMass (construct ch) history vk pub ch

/-- Joint simulation with no row-correctness or fixed-good-challenge premise.

The bound retains the two exceptional probabilities for the supplied row algorithms
and challenge law. PlonkFreshBounds and PlonkConstructedSimulation bound those terms
for the reference construction without conditioning away exceptional executions. -/
theorem freshPlonkVerifier_simulation_error_bound {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    PMFEventBiasLE (freshSampledPlonkVerifierProver urs law construct history vk pub)
        (freshPlonkVerifierSimulator urs law vk pub)
        (law.toOuterMeasure {ch | ¬ PlonkChallengesGood ch} +
          freshPlonkInvalidRowMass urs law construct history vk pub +
          (fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (freshPlonkVerifierSimulator urs law vk pub)
        (freshSampledPlonkVerifierProver urs law construct history vk pub)
        (law.toOuterMeasure {ch | ¬ PlonkChallengesGood ch} +
          freshPlonkInvalidRowMass urs law construct history vk pub +
          (fieldSampleCount actions : ℕ) * challenge255Bias) := by
  classical
  let actual := fun ch =>
    (sampledPlonkVerifierProver (construct ch) history urs vk pub ch).map (Prod.mk ch)
  let simulate := fun ch => (idealPlonkVerifierSimulator urs vk pub ch).map (Prod.mk ch)
  let error := fun ch => plonkInvalidRowMass (construct ch) history vk pub ch +
    (fieldSampleCount actions : ℕ) * challenge255Bias
  have hgood (ch : Challenges urs.k Fp) (hc : PlonkChallengesGood ch) :
      PMFEventBiasLE (actual ch) (simulate ch) (error ch) ∧
        PMFEventBiasLE (simulate ch) (actual ch) (error ch) := by
    obtain ⟨hxi, hu, hx, hpoints, haway⟩ := hc
    have h := sampledPlonkVerifier_consistency_error_bound (construct ch) history urs hk vk pub ch
      profile homega hn hblind hinstance hfixed hsigma hW hxi hu hx hpoints haway
    exact ⟨eventBias_map h.1 (Prod.mk ch), eventBias_map h.2 (Prod.mk ch)⟩
  have h := variableMixedLaws_error_bound law actual simulate PlonkChallengesGood error hgood
  have haverage : (∑' ch, law ch * error ch) =
      freshPlonkInvalidRowMass urs law construct history vk pub +
        (fieldSampleCount actions : ℕ) * challenge255Bias := by
    dsimp only [error, freshPlonkInvalidRowMass]
    simp_rw [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, law.tsum_coe, one_mul]
  rw [haverage] at h
  simpa only [freshSampledPlonkVerifierProver, freshPlonkVerifierSimulator, actual, simulate,
    add_assoc, add_comm, add_left_comm] using h

end Zcash.Snark.ZeroKnowledge
