import Zcash.Snark.ZeroKnowledge.PlonkSampling
import Zcash.Snark.ZeroKnowledge.ExceptionalMixtures

/-!
# Charging inconsistent private states in the joint simulation

The preceding exact theorem required quotient agreement on every reachable row state.
Here agreement is required only outside a chosen bad set, and its actual probability
under the ideal row law is added to the error. No conditioning or resampling of the
private rows or the inherited IPA blind takes place.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common
open CompPoly
open scoped ENNReal

/-- Forgetting the linear mask and commitment blinds recovers the original row law. -/
theorem idealPlonkMaterial_rows {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) :
    (idealPlonkMaterial construct history).map Prod.fst =
      idealColumnRows (plonkColumnSteps construct) history := by
  have hfst {A B : Type} (mu : PMF A) (nu : PMF B) :
      (Zcash.independentProductPMF mu nu).map Prod.fst = mu := by
    rw [Zcash.independentProductPMF, PMF.map_bind]
    have h (a : A) : (nu.map (Prod.mk a)).map Prod.fst = PMF.pure a := by
      rw [PMF.map_comp]
      exact PMF.map_const nu a
    simp_rw [h, PMF.bind_pure]
  exact hfst (idealColumnRows (plonkColumnSteps construct) history)
    (Zcash.independentProductPMF (PMF.uniformOfFintype (Fp × Fp))
      (PMF.uniformOfFintype (Fin (22 * actions + 10) → Fp)))

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Ideal joint simulation charges the probability of row states without quotient agreement. -/
theorem idealPlonkJoint_exceptional_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (good : ColumnHistory 2048 → Prop) [DecidablePred good]
    (hdegree : ∀ rows, PlonkDegreeBounds pub (pieces rows))
    (hquotient : ∀ rows, good rows →
      (plonkCollapsedQuotient x (pieces rows)).eval x =
        expectedHx (privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows)))
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : xi ≠ 0) (hu : ∀ j, rounds j ≠ 0)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        ((idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure {rows | ¬ good rows}) ∧
      PMFEventBiasLE (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        ((idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure {rows | ¬ good rows}) := by
  let observe := plonkMaskViewFromMaterial urs pub x x1 x2 q pieces
  let actual := fun material : PlonkPrivateMaterial actions =>
    let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
    (idealIpaProver data.1 data.2.1 data.2.2).map (Prod.mk (observe material))
  let simulate := fun view : PreIpaMaskView 5 (22 * actions + 10) G =>
    (idealIpaSimulator (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view)).map (Prod.mk view)
  have hfixed (material : PlonkPrivateMaterial actions) (hm : good material.1) :
      actual material = simulate (observe material) := by
    have hi := idealPlonkMultiopenIpa_simulation urs hk pub material.1 x x1 x2 x4 q xi z rounds
      (pieces material.1) material.2.1 (plonkCommitmentBlindsFromVector material.2.2)
      hpoints (hdegree material.1) hW hxi hu
    have hp := plonkPublicIpaInput_honest urs pub x x1 x2 x4 q xi z rounds expectedHx pieces
      material.1 material.2.1 material.2.2 (hquotient material.1 hm) hpoints
    dsimp only [actual, plonkIpaData]
    rw [hi]
    simp only [plonkCommitmentBlindsFromVector] at hp ⊢
    rw [← hp]
    rfl
  have hsim : (idealPlonkMaterial construct history).bind (simulate ∘ observe) =
      idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx := by
    rw [← PMF.bind_map,
      idealPlonkMaterial_maskView_simulation construct history urs pub x x1 x2 q pieces hW hpoints haway]
    rfl
  have hbad : (idealPlonkMaterial construct history).toOuterMeasure {material | ¬ good material.1} =
      (idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure {rows | ¬ good rows} := by
    change (idealPlonkMaterial construct history).toOuterMeasure (Prod.fst ⁻¹' {rows | ¬ good rows}) = _
    rw [← PMF.toOuterMeasure_map_apply, idealPlonkMaterial_rows]
  have h := mixedLaws_error_bound (idealPlonkMaterial construct history)
    actual (simulate ∘ observe) (fun material => good material.1) hfixed
  rw [hsim, hbad] at h
  exact h

/-- The full-tape sampling comparison holds without any row-correctness or challenge premise. -/
theorem sampledPlonkJoint_sampling_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) :
    PMFEventBiasLE (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (plonkJointSampleCount construct urs.k)
    (plonkJointViewFromTape construct history urs pub x x1 x2 x4 q xi z rounds pieces)
  rw [uniformTapePlonkJoint] at h
  change PMFEventBiasLE (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces) _ _ ∧
    PMFEventBiasLE _ (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces) _ at h
  rw [plonkJointSampleCount_eq construct hk] at h
  exact h

/-- Wide reduction and inconsistent private states contribute additive joint simulation errors. -/
theorem sampledPlonkJoint_exceptional_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (good : ColumnHistory 2048 → Prop) [DecidablePred good]
    (hdegree : ∀ rows, PlonkDegreeBounds pub (pieces rows))
    (hquotient : ∀ rows, good rows →
      (plonkCollapsedQuotient x (pieces rows)).eval x =
        expectedHx (privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows)))
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : xi ≠ 0) (hu : ∀ j, rounds j ≠ 0)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        ((idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure {rows | ¬ good rows} +
          (fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        ((idealColumnRows (plonkColumnSteps construct) history).toOuterMeasure {rows | ¬ good rows} +
          (fieldSampleCount actions : ℕ) * challenge255Bias) := by
  have hs := sampledPlonkJoint_sampling_error_bound construct history urs hk pub
    x x1 x2 x4 q xi z rounds pieces
  have hi := idealPlonkJoint_exceptional_error_bound construct history urs hk pub
    x x1 x2 x4 q xi z rounds pieces expectedHx good hdegree hquotient hW hxi hu hpoints haway
  exact ⟨hs.1.trans hi.1, by simpa only [add_comm] using hi.2.trans hs.2⟩

end Zcash.Snark.ZeroKnowledge
