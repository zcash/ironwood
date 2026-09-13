import Zcash.Snark.ZeroKnowledge.PlonkSuccessBounds
import Zcash.Common.Probability.Retry

/-!
# Successful full-prover observations

The real and simulated laws use the same observable completion predicate.
Supported successful outputs follow from the honest failure bound and the raw
simulation comparison. Filtering retains both normalizing probabilities; it is
not an assertion that conditioning preserves the raw statistical error.

The support arguments below are proofs, not witness inputs to the simulator.
The simulated law is the public simulator conditioned on observable completion.
This file concerns successful attempts, not a policy for retrying terminal errors
or a verifier view containing the history of previous attempts.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

instance plonkAttemptSuccessDecidable {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    DecidablePred (fun view : PlonkFreshView actions k G =>
      view ∈ plonkAttemptSuccessSet pointCodec scalarCodec) :=
  fun view => inferInstanceAs
    (Decidable ((observePlonkAttempt pointCodec scalarCodec view).status = .complete))

/-- The encoded view conditioned on completing the full emission schedule. -/
noncomputable def successfulPlonkView {actions k : ℕ} {G : Type*}
    (law : PMF (PlonkFreshView actions k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (h : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ law.support) :
    PMF (Challenges k Fp × ProverAttemptResult) :=
  (law.filter (plonkAttemptSuccessSet pointCodec scalarCodec) h).map
    (plonkAttemptObservation pointCodec scalarCodec)

/-- The raw simulation comparison transfers the honest failure bound to the simulator. -/
theorem plonk_common_failure_le {actions k : ℕ} {G : Type*}
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions)
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions)) :
    actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
        plonkCommonFailureBound actions ∧
      simulate.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
        plonkCommonFailureBound actions :=
  ⟨hfailure.trans le_self_add, event_measure_le_of_bias reverse _ hfailure⟩

/-- A strict common failure budget proves support on both sides before either law is filtered. -/
theorem plonk_success_support {actions k : ℕ} {G : Type*}
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions)
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hbudget : plonkCommonFailureBound actions < 1) :
    (∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ actual.support) ∧
      (∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ simulate.support) := by
  have hf := plonk_common_failure_le pointCodec scalarCodec hfailure reverse
  exact ⟨exists_success_of_failure_lt_one actual _ (hf.1.trans_lt hbudget),
    exists_success_of_failure_lt_one simulate _ (hf.2.trans_lt hbudget)⟩

/-- Both directions for the complete successful observation, with proved positive normalizers. -/
theorem successfulPlonk_simulation_error_bound {actions k : ℕ} {G : Type*}
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (forward : PMFEventBiasLE actual simulate (plonkSimulationErrorBound actions))
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions)
    (hbudget : plonkCommonFailureBound actions < 1) :
    ∃ ha : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ actual.support,
      ∃ hi : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ simulate.support,
        PMFEventBiasLE (successfulPlonkView actual pointCodec scalarCodec ha)
            (successfulPlonkView simulate pointCodec scalarCodec hi) (plonkSuccessfulErrorBound actions) ∧
          PMFEventBiasLE (successfulPlonkView simulate pointCodec scalarCodec hi)
            (successfulPlonkView actual pointCodec scalarCodec ha) (plonkSuccessfulErrorBound actions) := by
  obtain ⟨ha, hi⟩ := plonk_success_support pointCodec scalarCodec hfailure reverse hbudget
  have hf := plonk_common_failure_le pointCodec scalarCodec hfailure reverse
  have hc := conditioned_common_error_bound forward reverse (plonkAttemptSuccessSet pointCodec scalarCodec)
    ha hi (success_mass_lower_bound _ _ hf.1) (success_mass_lower_bound _ _ hf.2)
  refine ⟨ha, hi, ?_, ?_⟩
  · simpa only [successfulPlonkView, plonkSuccessfulErrorBound, two_mul] using
      eventBias_map hc.1 (plonkAttemptObservation pointCodec scalarCodec)
  · simpa only [successfulPlonkView, plonkSuccessfulErrorBound, two_mul] using
      eventBias_map hc.2 (plonkAttemptObservation pointCodec scalarCodec)

/-- Independent attempts which discard every unsuccessful observation converge to this law.

This describes selection of successful attempts. It does not identify the protocol's
terminal opening error with a request to retry, or retain earlier failed prefixes. -/
theorem successfulPlonk_selection_tendsto {actions k : ℕ} {G : Type*}
    (law : PMF (PlonkFreshView actions k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (h : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ law.support)
    (event : Set (Option (Challenges k Fp × ProverAttemptResult))) :
    Filter.Tendsto (fun n =>
      ((boundedRetries law (plonkAttemptSuccessSet pointCodec scalarCodec) n).map
        (Option.map (plonkAttemptObservation pointCodec scalarCodec))).toOuterMeasure event)
      Filter.atTop (nhds (((successfulPlonkView law pointCodec scalarCodec h).map some).toOuterMeasure event)) := by
  have hlimit := boundedRetries_tendsto law (plonkAttemptSuccessSet pointCodec scalarCodec) h
    ((Option.map (plonkAttemptObservation pointCodec scalarCodec)) ⁻¹' event)
  simpa only [PMF.toOuterMeasure_map_apply, successfulPlonkView, Set.preimage_preimage,
    Function.comp_def, Option.map_some] using hlimit

end Zcash.Snark.ZeroKnowledge
