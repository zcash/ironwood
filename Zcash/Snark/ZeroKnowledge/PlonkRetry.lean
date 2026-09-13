import Zcash.Snark.ZeroKnowledge.PlonkFiniteView
import Zcash.Snark.ZeroKnowledge.PlonkSuccessBounds
import Zcash.Common.Probability.RetainedRetriesSimulation
import Zcash.Snark.ZeroKnowledge.CallerRetryPolicy

/-!
# Auxiliary caller composition with the observed history retained

An external caller explicitly repeats point failures or handled IPA panics.
A complete emission or a coincident-opening error stops that caller. Every encoded prefix, received
challenge sequence, verifier tape, and status is retained, with exhaustion of a
finite retry budget reported separately. Witness and public input stay fixed.

This additional caller is absent from Zakura 1.4.0's modeled proof entry point.
The independence and caller policy are premises of these composition results.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The terminal failures that the auxiliary caller elects to repeat. -/
def plonkRetrySet {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    Set (PlonkFreshView actions k G) :=
  {view | callerRetryAfterFailure (observePlonkAttempt pointCodec scalarCodec view).status = true}

instance plonkRetryDecidable {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    DecidablePred (fun view : PlonkFreshView actions k G => view ∈ plonkRetrySet pointCodec scalarCodec) :=
  fun view => inferInstanceAs
    (Decidable (callerRetryAfterFailure (observePlonkAttempt pointCodec scalarCodec view).status = true))

/-- The same retry decision can be made from the observed result alone. -/
def plonkObservedRetrySet {k : ℕ} : Set (Challenges k Fp × ProverAttemptResult) :=
  {view | callerRetryAfterFailure view.2.status = true}

instance plonkObservedRetryDecidable {k : ℕ} :
    DecidablePred (fun view : Challenges k Fp × ProverAttemptResult => view ∈ plonkObservedRetrySet) :=
  fun view => inferInstanceAs (Decidable (callerRetryAfterFailure view.2.status = true))

/-- Execute the finite policy and observe all attempts it actually uses. -/
def runPlonkRetries {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (tape : List (PlonkFreshView actions k G)) : RetryHistory (Challenges k Fp × ProverAttemptResult) :=
  (runRetryHistory (plonkRetrySet pointCodec scalarCodec) tape).map
    (plonkAttemptObservation pointCodec scalarCodec)

/-- Running on observed attempts gives the same history; no hidden proof value controls retries. -/
theorem runPlonkRetries_fromObserved {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (tape : List (PlonkFreshView actions k G)) :
    runPlonkRetries pointCodec scalarCodec tape =
      runRetryHistory plonkObservedRetrySet (tape.map (plonkAttemptObservation pointCodec scalarCodec)) := by
  unfold runPlonkRetries
  symm
  apply runRetryHistory_map
  intro view
  simp only [plonkAttemptObservation, plonkObservedRetrySet, plonkRetrySet, Set.mem_setOf_eq]

/-- A terminal opening error stops immediately, without exposing or requesting another attempt. -/
theorem runPlonkRetries_terminal {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : PlonkFreshView actions k G) (later : List (PlonkFreshView actions k G))
    (h : (observePlonkAttempt pointCodec scalarCodec view).status = .failed .coincidentOpeningQueries) :
    runPlonkRetries pointCodec scalarCodec (view :: later) =
      RetryHistory.stopped (plonkAttemptObservation pointCodec scalarCodec view) := by
  simp [runPlonkRetries, runRetryHistory, plonkRetrySet, h,
    RetryHistory.stopped, RetryHistory.map, plonkAttemptObservation]

/-- A completed emission also ends the retry policy immediately. -/
theorem runPlonkRetries_complete {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : PlonkFreshView actions k G) (later : List (PlonkFreshView actions k G))
    (h : (observePlonkAttempt pointCodec scalarCodec view).status = .complete) :
    runPlonkRetries pointCodec scalarCodec (view :: later) =
      RetryHistory.stopped (plonkAttemptObservation pointCodec scalarCodec view) := by
  simp [runPlonkRetries, runRetryHistory, plonkRetrySet, h,
    RetryHistory.stopped, RetryHistory.map, plonkAttemptObservation]

/-- The failures selected by the auxiliary caller are covered by the single-attempt bound. -/
theorem plonkRetry_subset_failure {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    plonkRetrySet (actions := actions) (k := k) pointCodec scalarCodec ⊆
      (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ := by
  intro view hretry hcomplete
  change callerRetryAfterFailure (observePlonkAttempt pointCodec scalarCodec view).status = true at hretry
  change (observePlonkAttempt pointCodec scalarCodec view).status = .complete at hcomplete
  exact callerRetryAfterFailure_ne_complete _ hretry hcomplete

/-- Repeat the same complete attempt law independently, preserving every encoded observation. -/
noncomputable def observedPlonkRetries {actions k : ℕ} {G : Type*}
    (law : PMF (PlonkFreshView actions k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) (n : ℕ) :
    PMF (RetryHistory (Challenges k Fp × ProverAttemptResult)) :=
  (retainedRetries law (plonkRetrySet pointCodec scalarCodec) n).map
    (RetryHistory.map (plonkAttemptObservation pointCodec scalarCodec))

/-- The retained probability law executes the actual observable retry program on independent attempts. -/
theorem observedPlonkRetries_fromTape {actions k : ℕ} {G : Type*}
    (law : PMF (PlonkFreshView actions k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) (n : ℕ) :
    (retryAttemptTape law n).map (runPlonkRetries pointCodec scalarCodec) =
      observedPlonkRetries law pointCodec scalarCodec n := by
  rw [observedPlonkRetries, ← retainedRetries_fromTape, PMF.map_comp]
  rfl

/-- Every finite retry budget has the geometric comparison, with all failed observations retained. -/
theorem observedPlonkRetries_simulation_error_bound {actions k : ℕ} {G : Type*} [Fintype G]
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (forward : PMFEventBiasLE actual simulate (plonkSimulationErrorBound actions))
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions) (n : ℕ) :
    PMFEventBiasLE (observedPlonkRetries actual pointCodec scalarCodec n)
        (observedPlonkRetries simulate pointCodec scalarCodec n)
        (retainedRetryError (plonkSimulationErrorBound actions) (plonkAttemptFailureBound actions) n) ∧
      PMFEventBiasLE (observedPlonkRetries simulate pointCodec scalarCodec n)
        (observedPlonkRetries actual pointCodec scalarCodec n)
        (retainedRetryError (plonkSimulationErrorBound actions) (plonkAttemptFailureBound actions) n) := by
  have hr := (actual.toOuterMeasure.mono (plonkRetry_subset_failure pointCodec scalarCodec)).trans hfailure
  have h := retainedRetries_simulation_error_bound forward reverse
    (plonkRetrySet pointCodec scalarCodec) hr n
  exact ⟨eventBias_map h.1 _, eventBias_map h.2 _⟩

/-- A single numerical budget controls the complete observed history for every finite retry limit. -/
theorem observedPlonkRetries_uniform_error_bound {actions k : ℕ} {G : Type*} [Fintype G]
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (forward : PMFEventBiasLE actual simulate (plonkSimulationErrorBound actions))
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions)
    (hrate : plonkAttemptFailureBound actions < 1) (n : ℕ) :
    PMFEventBiasLE (observedPlonkRetries actual pointCodec scalarCodec n)
        (observedPlonkRetries simulate pointCodec scalarCodec n)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) ∧
      PMFEventBiasLE (observedPlonkRetries simulate pointCodec scalarCodec n)
        (observedPlonkRetries actual pointCodec scalarCodec n)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) := by
  have hr := (actual.toOuterMeasure.mono (plonkRetry_subset_failure pointCodec scalarCodec)).trans hfailure
  have h := retainedRetries_uniform_error_bound forward reverse
    (plonkRetrySet pointCodec scalarCodec) hr hrate n
  exact ⟨eventBias_map h.1 _, eventBias_map h.2 _⟩

/-- Encoding every attempt preserves the exact exhaustion probability. -/
theorem observedPlonkRetries_exhausted {actions k : ℕ} {G : Type*}
    (law : PMF (PlonkFreshView actions k G))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) (n : ℕ) :
    (observedPlonkRetries law pointCodec scalarCodec n).toOuterMeasure {history | history.exhausted = true} =
      law.toOuterMeasure (plonkRetrySet pointCodec scalarCodec) ^ n := by
  rw [observedPlonkRetries, PMF.toOuterMeasure_map_apply]
  exact retainedRetries_exhausted law (plonkRetrySet pointCodec scalarCodec) n

/-- The real and simulated exhaustion masses obey the auxiliary caller's geometric bound. -/
theorem observedPlonkRetries_both_exhausted_le {actions k : ℕ} {G : Type*}
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions) (n : ℕ) :
    (observedPlonkRetries actual pointCodec scalarCodec n).toOuterMeasure {history | history.exhausted = true} ≤
        plonkAttemptFailureBound actions ^ n ∧
      (observedPlonkRetries simulate pointCodec scalarCodec n).toOuterMeasure {history | history.exhausted = true} ≤
        plonkCommonFailureBound actions ^ n := by
  have hr := (actual.toOuterMeasure.mono (plonkRetry_subset_failure pointCodec scalarCodec)).trans hfailure
  have hs := event_measure_le_of_bias reverse (plonkRetrySet pointCodec scalarCodec) hr
  simp only [observedPlonkRetries_exhausted]
  constructor
  · gcongr
    exact hr
  · gcongr
    exact hs

/-- In both experiments the probability of needing further attempts tends to zero. -/
theorem observedPlonkRetries_exhausted_tendsto {actions k : ℕ} {G : Type*}
    {actual simulate : PMF (PlonkFreshView actions k G)}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (reverse : PMFEventBiasLE simulate actual (plonkSimulationErrorBound actions))
    (hfailure : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions)
    (hrate : plonkCommonFailureBound actions < 1) :
    Filter.Tendsto (fun n =>
        (observedPlonkRetries actual pointCodec scalarCodec n).toOuterMeasure
          {history | history.exhausted = true}) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n =>
        (observedPlonkRetries simulate pointCodec scalarCodec n).toOuterMeasure
          {history | history.exhausted = true}) Filter.atTop (nhds 0) := by
  have hr := (actual.toOuterMeasure.mono (plonkRetry_subset_failure pointCodec scalarCodec)).trans hfailure
  have hs := event_measure_le_of_bias reverse (plonkRetrySet pointCodec scalarCodec) hr
  have hrlt : actual.toOuterMeasure (plonkRetrySet pointCodec scalarCodec) < 1 :=
    hr.trans_lt ((show plonkAttemptFailureBound actions ≤ plonkCommonFailureBound actions
      from le_self_add).trans_lt hrate)
  have hslt : simulate.toOuterMeasure (plonkRetrySet pointCodec scalarCodec) < 1 := hs.trans_lt hrate
  simp only [observedPlonkRetries_exhausted]
  exact ⟨ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrlt,
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hslt⟩

/-- The numerical certificate used for successful views also bounds the honest retry rate below one. -/
theorem plonkAttemptFailureBound_lt_one {actions : ℕ} (hsize : actions ≤ 65535) :
    plonkAttemptFailureBound actions < 1 :=
  (show plonkAttemptFailureBound actions ≤ plonkCommonFailureBound actions from le_self_add).trans_lt
    (plonkCommonFailureBound_lt_one hsize)

end Zcash.Snark.ZeroKnowledge
