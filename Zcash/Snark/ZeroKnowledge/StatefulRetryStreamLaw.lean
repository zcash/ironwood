import Zcash.Snark.ZeroKnowledge.StatefulRetryStream
import Zcash.Snark.ZeroKnowledge.UniformInfiniteTape
import Zcash.Snark.ZeroKnowledge.StatefulRetryGeometric

/-!
# Probability laws of the complete retained retry stream

The infinite experiment runs on an actual independent uniform tape stream.
Its finite-dimensional laws are the existing retry recursion, with each
intermediate public state also retained. No run is conditioned on termination.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- The finite retry law with each attempt's returned state retained in its observation. -/
noncomputable def statefulRetryRecorded {A State : Type*}
    (attempt : State → PMF (A × State)) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) : PMF (RetryHistory (A × State) × State) :=
  statefulRetries (fun prior => (attempt prior).map (fun observation => (observation, observation.2)))
    (retainedStateRetrySet retry) budget state

/-- The recorded finite recursion is exactly the same tape-driven runner with the extra states kept. -/
theorem statefulRetryRecorded_fromTape {A State Tape : Type*} (law : PMF Tape)
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) :
    (retryAttemptTape law budget).map
        (fun tapes => runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry) tapes state) =
      statefulRetryRecorded (fun prior => law.map (run prior)) retry budget state := by
  rw [statefulRetries_fromTape]
  unfold statefulRetryRecorded
  apply congrArg (fun attempt => statefulRetries attempt (retainedStateRetrySet retry) budget state)
  funext prior
  rw [PMF.map_comp]
  rfl

/-- The comparison potential also bounds histories that retain all intermediate public states. -/
theorem statefulRetryRecorded_potential_error_bound {A State : Type*}
    (actual ideal : State → PMF (A × State)) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (size : State → ℕ) (growth : ℕ)
    (error potential : ℕ → ℝ≥0∞) (rate : ℝ≥0∞)
    (hstep : ∀ bound state, size state ≤ bound →
      PMFEventBiasLE (actual state) (ideal state) (error bound) ∧
        PMFEventBiasLE (ideal state) (actual state) (error bound))
    (hgrowth : ∀ state observation, observation ∈ (ideal state).support →
      size observation.2 ≤ size state + growth)
    (hrate : ∀ state, (ideal state).toOuterMeasure {observation | observation.1 ∈ retry} ≤ rate)
    (hpotential : ∀ bound, error bound + rate * potential (bound + growth) ≤ potential bound)
    (budget bound : ℕ) (state : State) (hsize : size state ≤ bound) :
    PMFEventBiasLE (statefulRetryRecorded actual retry budget state) (statefulRetryRecorded ideal retry budget state)
        (potential bound) ∧
      PMFEventBiasLE (statefulRetryRecorded ideal retry budget state) (statefulRetryRecorded actual retry budget state)
        (potential bound) := by
  apply statefulRetries_potential_error_bound _ _ (retainedStateRetrySet retry) size growth error potential rate
  · intro bound prior hprior
    have h := hstep bound prior hprior
    exact ⟨eventBias_map h.1 (fun observation => (observation, observation.2)),
      eventBias_map h.2 (fun observation => (observation, observation.2))⟩
  · intro prior observation hobs
    rw [PMF.mem_support_map_iff] at hobs
    obtain ⟨value, hvalue, rfl⟩ := hobs
    exact hgrowth prior value hvalue
  · intro prior
    simpa only [PMF.toOuterMeasure_map_apply, retainedStateRetrySet, Set.preimage_setOf_eq] using hrate prior
  · exact hpotential
  · exact hsize

/-- The infinite tape's finite-prefix computation has exactly the recorded finite law under every observation. -/
theorem statefulRetryPrefix_map_law {A State Tape Output : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace Output]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) (observe : (RetryHistory (A × State) × State) → Output) :
    (uniformInfiniteTape Tape).map (fun tapes => observe (statefulRetryPrefix run retry budget tapes state)) =
      ((statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
        retry budget state).map observe).toMeasure := by
  let runner := fun tapes => runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry) tapes state
  have h : ((PMF.uniformOfFintype (Fin budget → Tape)).map List.ofFn).map runner =
      statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior)) retry budget state := by
    rw [← independentTapeLaw_uniform (A := Tape), independentTapeLaw_toList]
    exact statefulRetryRecorded_fromTape _ run retry budget state
  have ho := congrArg (PMF.map observe) h
  simp only [PMF.map_comp, Function.comp_def, runner] at ho
  have hm := uniformInfiniteTape_prefix_map budget (fun tape : Fin budget → Tape => observe (runner (List.ofFn tape)))
  exact hm.trans (congrArg PMF.toMeasure ho)

/-- Every stream coordinate is measurable because it depends on a finite attempt-tape prefix. -/
theorem statefulRetryStream_measurable {A State Tape : Type*} [Fintype Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (state : State) : Measurable (fun tapes => statefulRetryStream run retry tapes state) := by
  apply measurable_pi_lambda
  intro index
  have heq : (fun tapes => statefulRetryStream run retry tapes state index) =
      (fun tapes => (statefulRetryPrefix run retry (index + 1) tapes state).1.attempts[index]?) := by
    funext tapes
    exact (statefulRetryPrefix_at run retry (index + 1) tapes state index (Nat.lt_succ_self _)).symm
  rw [heq]
  exact (measurable_of_countable (fun tape : Fin (index + 1) → Tape =>
    (runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry) (List.ofFn tape) state).1.attempts[index]?)).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

/-- The law of all observed attempts and public states, including possibly infinite execution. -/
noncomputable def statefulRetryStreamLaw {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (state : State) : Measure (ℕ → Option (A × State)) :=
  (uniformInfiniteTape Tape).map (fun tapes => statefulRetryStream run retry tapes state)

/-- The complete history law is normalized without assuming that its execution terminates. -/
instance statefulRetryStreamLaw_isProbabilityMeasure {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (state : State) : IsProbabilityMeasure (statefulRetryStreamLaw run retry state) :=
  Measure.isProbabilityMeasure_map (statefulRetryStream_measurable run retry state).aemeasurable

/-- Every finite-dimensional observation is exactly the corresponding projection of the recorded finite runner. -/
theorem statefulRetryStreamLaw_prefix {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) :
    (statefulRetryStreamLaw run retry state).map (fun stream (i : Fin budget) => stream i.val) =
      ((statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
        retry budget state).map (fun output (i : Fin budget) => output.1.attempts[i.val]?)).toMeasure := by
  have hm : Measurable (fun stream : ℕ → Option (A × State) => fun i : Fin budget => stream i.val) := by fun_prop
  rw [statefulRetryStreamLaw, Measure.map_map hm (statefulRetryStream_measurable run retry state)]
  have heq : ((fun (stream : ℕ → Option (A × State)) (i : Fin budget) => stream i.val) ∘
      (fun tapes => statefulRetryStream run retry tapes state)) =
      (fun tapes (i : Fin budget) => (statefulRetryPrefix run retry budget tapes state).1.attempts[i.val]?) := by
    funext tapes i
    exact (statefulRetryPrefix_at run retry budget tapes state i.val i.isLt).symm
  rw [heq]
  exact statefulRetryPrefix_map_law run retry budget state
    (fun (output : RetryHistory (A × State) × State) (i : Fin budget) => output.1.attempts[i.val]?)

end Zcash.Snark.ZeroKnowledge
