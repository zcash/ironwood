import Zcash.Snark.ZeroKnowledge.PlonkConstraints
import Zcash.Snark.ZeroKnowledge.QuotientPieces
import Zcash.Snark.ZeroKnowledge.PlonkSampling

/-!
# Simulation with the computed quotient and actual verifier constraint function

The prover in this module constructs the constraint numerator, divides it by the row
domain polynomial, cuts the eight quotient pieces, and projects its joint output to
the existing `ProofString`. The simulator uses `allExpressions` and `expectedHEval`.
Neither an arbitrary quotient constructor nor an arbitrary inferred-value callback
is supplied to these experiments.

The remaining private-state premises are concrete: the honest row construction must
produce a numerator divisible by `X^2048 - 1` and within the quotient's capacity.
Public polynomial degree bounds and the supplied-challenge premises also remain.
Failures, challenge generation, full verifier grouping, and Rust refinement are not
discharged by this algebraic output-distribution theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly
open Zcash.Common
open Zcash.Common.Probability

section Quotient

variable {G : Type*} [Zero G]

/-- The eight pieces computed from the actual verifier-compatible constraint numerator. -/
def plonkHonestQuotientPieces {actions k : ℕ}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) : Fin 8 → CPoly :=
  plonkQuotientPieces (plonkConstraintNumerator vk pub ch rows)

/-- Divisibility and capacity imply the exact quotient agreement needed by joint simulation. -/
theorem plonkHonestQuotient_agrees {actions k : ℕ}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hx : ch.x ^ 2048 ≠ 1)
    (hdegree : (plonkConstraintNumerator vk pub ch rows).natDegree < 9 * 2048)
    (hdiv : (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows) :
    (plonkCollapsedQuotient ch.x (plonkHonestQuotientPieces vk pub ch rows)).eval ch.x =
      plonkVerifierHx vk pub ch (privateColumnView (observeColumnRows (omegaOf 11)
        (plonkObservationPoints (omegaOf 11) ch.x ch.x3) rows)) := by
  rw [plonkHonestQuotientPieces, plonkQuotientPieces_eval _ _ hdegree hdiv hx]
  exact plonkConstraintNumerator_eval_div vk pub ch rows ch.x3 homega hn hblind hx

end Quotient

section Simulation

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The existing joint construction and proof projection on one complete private field tape. -/
def plonkVerifierProofFromTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (tape : Fin (plonkJointSampleCount construct urs.k) → Fp) :
    ProofString (plonkProofShape actions urs.k) Fp G :=
  plonkProofFromJointView pub ch.x ch.x1
    (plonkJointViewFromTape construct history urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
      ch.ipaRound (plonkHonestQuotientPieces vk pub ch) tape)

/-- The complete algebraic proof law with the computed constraint quotient and the full field tape. -/
noncomputable def sampledPlonkVerifierProver {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) : PMF (ProofString (plonkProofShape actions urs.k) Fp G) :=
  (sampledPlonkJointProver construct history urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
    ch.ipaRound (plonkHonestQuotientPieces vk pub ch)).map (plonkProofFromJointView pub ch.x ch.x1)

/-- Sampling the deterministic typed proof gives exactly the law used by joint simulation. -/
theorem sampledPlonkVerifierProver_fromTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) :
    sampledPlonkVerifierProver construct history urs vk pub ch =
      (sampleFieldsWith (plonkJointSampleCount construct urs.k)
        (plonkVerifierProofFromTape construct history urs vk pub ch)).runFreshPMF fieldSample := by
  unfold sampledPlonkVerifierProver sampledPlonkJointProver plonkVerifierProofFromTape
  exact (sampleFieldsWith_map _ _ _ _).symm

variable [Fintype G]

/-- The public simulator uses the existing verifier's constraint calculation to form its IPA input. -/
noncomputable def idealPlonkVerifierSimulator {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) : PMF (ProofString (plonkProofShape actions urs.k) Fp G) :=
  (idealPlonkJointSimulator urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
    ch.ipaRound (plonkVerifierHx vk pub ch)).map (plonkProofFromJointView pub ch.x ch.x1)

/-- Joint simulation in the existing proof type, with quotient agreement derived from the numerator.

This endpoint retains the actual row-correctness obligations. It does not assume a
witness-independent quotient callback or independently resample the inherited IPA blind. -/
theorem sampledPlonkVerifier_simulation_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hdegree : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      (plonkConstraintNumerator vk pub ch rows).natDegree < 9 * 2048)
    (hdiv : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : ch.xi ≠ 0)
    (hu : ∀ j, ch.ipaRound j ≠ 0) (hx : ch.x ^ 2048 ≠ 1)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) ch.x ch.x3))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048,
      plonkObservationPoints (omegaOf 11) ch.x ch.x3 i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkVerifierProver construct history urs vk pub ch)
        (idealPlonkVerifierSimulator urs vk pub ch) ((fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkVerifierSimulator urs vk pub ch)
        (sampledPlonkVerifierProver construct history urs vk pub ch)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) := by
  have hpieces (rows : ColumnHistory 2048)
      (_ : rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support) :
      PlonkDegreeBounds pub (plonkHonestQuotientPieces vk pub ch rows) :=
    ⟨hinstance, hfixed, hsigma,
      plonkQuotientPieces_natDegree_lt (plonkConstraintNumerator vk pub ch rows)⟩
  have hquotient (rows : ColumnHistory 2048)
      (hrows : rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support) :=
    plonkHonestQuotient_agrees vk pub ch rows homega hn hblind hx
      (hdegree rows hrows) (hdiv rows hrows)
  have h := sampledPlonkJoint_simulation_error_bound construct history urs hk pub
    ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound
    (plonkHonestQuotientPieces vk pub ch) (plonkVerifierHx vk pub ch)
    hpieces hquotient hW hxi hu hpoints haway
  exact ⟨eventBias_map h.1 (plonkProofFromJointView pub ch.x ch.x1),
    eventBias_map h.2 (plonkProofFromJointView pub ch.x ch.x1)⟩

end Simulation

end Zcash.Snark.ZeroKnowledge
