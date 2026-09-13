import Zcash.Snark.ZeroKnowledge.PlonkRowSimulation
import Zcash.Snark.ZeroKnowledge.PlonkExceptional

/-!
# An explicit error term for inconsistent row states

No hypothesis here requires every possible random row state to satisfy the constraints.
The probability of failing exact domain division is retained as an error term under the
ideal row law. The sampling comparison already charges the change from that ideal law to
the full wide-reduced field tape. Bounding the remaining error for the actual lookup and
product constructors is a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common
open Zcash.Common.Probability
open CompPoly
open scoped ENNReal

/-- Probability that the ideal row construction does not produce an exactly divisible numerator. -/
noncomputable def plonkInvalidRowMass {actions k : ℕ} {G : Type*} [Zero G]
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) : ℝ≥0∞ :=
  (idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure
    {rows | ¬ ((CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows)}

/-- The invalid-numerator event is contained in the event of some violated row constraint. -/
theorem plonkInvalidRowMass_le_row_violation {actions k : ℕ} {G : Type*} [Zero G]
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) :
    plonkInvalidRowMass construct history vk pub ch ≤
      (idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure
        {rows | ∃ poly ∈ (plonkConstraintModel vk pub ch rows).constraints,
          ∃ i : Fin 2048, poly.eval (omegaOf 11 ^ i.val) ≠ 0} := by
  apply MeasureTheory.measure_mono
  intro rows hbad
  by_contra h
  apply hbad
  apply plonkConstraintNumerator_dvd_of_rows vk pub ch rows
  intro poly hpoly i
  by_contra hi
  exact h ⟨poly, hpoly, i, hi⟩

/-- Complete algebraic simulation with row inconsistency charged rather than excluded. -/
theorem sampledPlonkVerifier_consistency_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : ch.xi ≠ 0)
    (hu : ∀ j, ch.ipaRound j ≠ 0) (hx : ch.x ^ 2048 ≠ 1)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) ch.x ch.x3))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048,
      plonkObservationPoints (omegaOf 11) ch.x ch.x3 i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkVerifierProver construct history urs vk pub ch)
        (idealPlonkVerifierSimulator urs vk pub ch)
        (plonkInvalidRowMass construct history vk pub ch + (fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkVerifierSimulator urs vk pub ch)
        (sampledPlonkVerifierProver construct history urs vk pub ch)
        (plonkInvalidRowMass construct history vk pub ch + (fieldSampleCount actions : ℕ) * challenge255Bias) := by
  classical
  let good := fun rows => (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows
  have hpieces (rows : ColumnHistory 2048) :
      PlonkDegreeBounds pub (plonkHonestQuotientPieces vk pub ch rows) :=
    ⟨hinstance, hfixed, hsigma,
      plonkQuotientPieces_natDegree_lt (plonkConstraintNumerator vk pub ch rows)⟩
  have hquotient (rows : ColumnHistory 2048) (hrows : good rows) :=
    plonkHonestQuotient_agrees vk pub ch rows homega hn hblind hx
      (plonkConstraintNumerator_natDegree_lt vk pub ch rows profile hinstance hfixed hsigma) hrows
  have h := sampledPlonkJoint_exceptional_error_bound construct history urs hk pub
    ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound
    (plonkHonestQuotientPieces vk pub ch) (plonkVerifierHx vk pub ch) good
    hpieces hquotient hW hxi hu hpoints haway
  exact ⟨eventBias_map h.1 (plonkProofFromJointView pub ch.x ch.x1),
    eventBias_map h.2 (plonkProofFromJointView pub ch.x ch.x1)⟩

end Zcash.Snark.ZeroKnowledge
