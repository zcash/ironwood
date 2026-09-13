import Zcash.Snark.ZeroKnowledge.Sampling
import Zcash.Common.Probability.RetainedRetriesSimulation

/-!
# Independent raw tapes and replacement of the complete private source

The ideal raw source is uniform on a finite vector of 512-bit integers. Its
coordinatewise reduction is exactly the reference field tape, with the existing
wide-reduction bias. A replacement source is compared as one joint distribution;
no independence claim is inferred from its individual coordinate marginals.

`sourceTapeExperiment` samples its public coins independently of that source.
Statistical source bounds then add to an existing simulation bound. A PRNG
distinguishing assumption is a separate, test-dependent premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- A vector of independent samples from one arbitrary probability mass function. -/
noncomputable def independentTapeLaw {A : Type*} (law : PMF A) : (count : ℕ) → PMF (Fin count → A)
  | 0 => PMF.pure Fin.elim0
  | count + 1 => law.bind fun value => (independentTapeLaw law count).map (Fin.cons value)

/-- Coordinatewise deterministic conversion commutes with independent sampling. -/
theorem independentTapeLaw_map {A B : Type*} (law : PMF A) (convert : A → B) (count : ℕ) :
    independentTapeLaw (law.map convert) count =
      (independentTapeLaw law count).map (fun tape i => convert (tape i)) := by
  induction count with
  | zero =>
    simp only [independentTapeLaw, PMF.pure_map]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ count ih =>
    simp only [independentTapeLaw, PMF.bind_map, PMF.map_bind, ih, PMF.map_comp]
    congr 1
    funext value
    apply congrArg (fun f : (Fin count → A) → Fin (count + 1) → B =>
      (independentTapeLaw law count).map f)
    funext tape i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Independent uniform coordinates give the uniform distribution on the complete vector. -/
theorem independentTapeLaw_uniform {A : Type*} [Fintype A] [Nonempty A] (count : ℕ) :
    independentTapeLaw (PMF.uniformOfFintype A) count = PMF.uniformOfFintype (Fin count → A) := by
  induction count with
  | zero =>
    classical
    apply PMF.ext
    intro tape
    have ht : tape = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [independentTapeLaw, PMF.uniformOfFintype_apply, ht]
  | succ count ih =>
    let e := Fin.consEquiv (fun _ : Fin (count + 1) => A)
    calc
      _ = (Zcash.independentProductPMF (PMF.uniformOfFintype A)
          (PMF.uniformOfFintype (Fin count → A))).map e := by
        simp only [independentTapeLaw, ih, Zcash.independentProductPMF,
          PMF.map_bind, PMF.map_comp]
        rfl
      _ = _ := by
        rw [Zcash.independentProductPMF_uniform, Zcash.map_uniformOfFintype_equiv]

/-- The existing field-query program samples exactly the independent vector law. -/
theorem sampleFieldsWith_eq_independentTape {A : Type*} (count : ℕ)
    (finish : (Fin count → Fp) → A) (law : PMF Fp) :
    (sampleFieldsWith count finish).runFreshPMF law = (independentTapeLaw law count).map finish := by
  induction count with
  | zero => exact (PMF.pure_map finish Fin.elim0).symm
  | succ count ih =>
    simp only [sampleFieldsWith, OracleComp.runFreshPMF, independentTapeLaw, PMF.map_bind,
      PMF.map_comp]
    congr 1
    funext value
    exact ih (fun rest => finish (Fin.cons value rest))

/-- One 512-bit integer for every field draw consumed by the reference attempt. -/
abbrev RawPrivateTape (actions : ℕ) := Fin (fieldSampleCount actions) → Fin challengeDigestCard

/-- The specified wide reduction, applied without any rejection or hashing step. -/
def reducePrivateTape {actions : ℕ} (tape : RawPrivateTape actions) : Fin (fieldSampleCount actions) → Fp :=
  fun i => ((tape i).val : Fp)

/-- Uniform raw bits reproduce the existing reference's entire wide-reduced private tape. -/
theorem uniformRawPrivateTape_reduce (actions : ℕ) :
    (PMF.uniformOfFintype (RawPrivateTape actions)).map reducePrivateTape =
      independentTapeLaw fieldSample (fieldSampleCount actions) := by
  change (PMF.uniformOfFintype (Fin (fieldSampleCount actions) → Fin challengeDigestCard)).map
    (fun tape i => ((tape i).val : Fp)) = _
  rw [← independentTapeLaw_uniform (A := Fin challengeDigestCard)]
  exact (independentTapeLaw_map (PMF.uniformOfFintype (Fin challengeDigestCard))
    (fun value => (value.val : Fp)) (fieldSampleCount actions)).symm

/-- Sample public coins and the complete private tape independently, then run the continuation. -/
noncomputable def sourceTapeExperiment {C T A : Type*} (coins : PMF C) (source : PMF T)
    (run : C → T → A) : PMF A :=
  coins.bind fun c => source.map (run c)

/-- Replacing a complete private source costs only its joint statistical distance. -/
theorem sourceTapeExperiment_error_bound {C T A : Type*} [Fintype C]
    (coins : PMF C) {actual ideal : PMF T} {η : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal η) (reverse : PMFEventBiasLE ideal actual η)
    (run : C → T → A) :
    PMFEventBiasLE (sourceTapeExperiment coins actual run) (sourceTapeExperiment coins ideal run) η ∧
      PMFEventBiasLE (sourceTapeExperiment coins ideal run) (sourceTapeExperiment coins actual run) η :=
  ⟨PMFEventBiasLE.bind_same (fun c => eventBias_map forward (run c)),
    PMFEventBiasLE.bind_same (fun c => eventBias_map reverse (run c))⟩

/-- Source replacement composes with simulation while preserving both directions of the bound. -/
theorem sourceTapeExperiment_simulation_error_bound {C T A : Type*} [Fintype C]
    (coins : PMF C) {actual ideal : PMF T} {simulator : PMF A} {η ε : ℝ≥0∞}
    (sourceForward : PMFEventBiasLE actual ideal η) (sourceReverse : PMFEventBiasLE ideal actual η)
    (run : C → T → A)
    (simulateForward : PMFEventBiasLE (sourceTapeExperiment coins ideal run) simulator ε)
    (simulateReverse : PMFEventBiasLE simulator (sourceTapeExperiment coins ideal run) ε) :
    PMFEventBiasLE (sourceTapeExperiment coins actual run) simulator (ε + η) ∧
      PMFEventBiasLE simulator (sourceTapeExperiment coins actual run) (ε + η) := by
  have h := sourceTapeExperiment_error_bound coins sourceForward sourceReverse run
  exact ⟨h.1.trans simulateForward, by simpa only [add_comm] using simulateReverse.trans h.2⟩

end Zcash.Snark.ZeroKnowledge
