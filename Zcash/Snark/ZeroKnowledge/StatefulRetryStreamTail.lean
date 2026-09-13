import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamLaw
import Zcash.Snark.ZeroKnowledge.MeasureAgreement

/-!
# Exhaustion, nontermination, and truncation of complete retry streams

Finite exhaustion bounds control how much a bounded observer misses. They also
bound the mass of infinite histories. Neither the observation space nor the
underlying probability law assumes almost-sure termination.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory
open scoped ENNReal

/-- Recording intermediate states preserves the same geometric exhaustion estimate. -/
theorem statefulRetryRecorded_exhaustion_le {A State : Type*}
    (attempt : State → PMF (A × State)) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (rate : ℝ≥0∞) (hrate : ∀ state,
      (attempt state).toOuterMeasure {observation | observation.1 ∈ retry} ≤ rate)
    (budget : ℕ) (state : State) :
    (statefulRetryRecorded attempt retry budget state).toOuterMeasure
      {output | output.1.exhausted = true} ≤ rate ^ budget := by
  apply statefulRetries_exhaustion_le _ (retainedStateRetrySet retry) rate
  intro prior
  simpa only [PMF.toOuterMeasure_map_apply, retainedStateRetrySet, Set.preimage_setOf_eq] using hrate prior

/-- The finite recorded output is a measurable function of its finite input prefix. -/
theorem statefulRetryPrefix_measurable {A State Tape : Type*} [Fintype Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape]
    [MeasurableSpace (RetryHistory (A × State) × State)]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) : Measurable (fun tapes => statefulRetryPrefix run retry budget tapes state) :=
  (measurable_of_countable (fun tape : Fin budget → Tape =>
    runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry) (List.ofFn tape) state)).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

/-- Every event of the finite output has exactly its existing probability mass function value. -/
theorem statefulRetryPrefix_event_law {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) (event : Set (RetryHistory (A × State) × State)) :
    (uniformInfiniteTape Tape) {tapes | statefulRetryPrefix run retry budget tapes state ∈ event} =
      (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
        retry budget state).toOuterMeasure event := by
  letI : MeasurableSpace (RetryHistory (A × State) × State) := ⊤
  have he : MeasurableSet event := trivial
  have h := statefulRetryPrefix_map_law run retry budget state id
  simp only [id_eq, PMF.map_id] at h
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ he, ← h,
    Measure.map_apply (statefulRetryPrefix_measurable run retry budget state) he]
  rfl

/-- The complete observation is nonterminating precisely when every attempt position is present. -/
def retryStreamNontermination {Value : Type*} : Set (ℕ → Option Value) :=
  {stream | ∀ index, stream index ≠ none}

/-- Nontermination is a measurable event of the complete stream. -/
theorem retryStreamNontermination_measurable {Value : Type*}
    [MeasurableSpace (Option Value)] [MeasurableSingletonClass (Option Value)] :
    MeasurableSet (retryStreamNontermination (Value := Value)) := by
  simp only [retryStreamNontermination, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro index
  exact (measurableSet_singleton none).compl.preimage (measurable_pi_apply index)

/-- A nonterminating tape exhausts every finite budget under the actual stopping policy. -/
theorem statefulRetryStream_nontermination_exhausts {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State)
    (h : statefulRetryStream run retry tapes state ∈ retryStreamNontermination) :
    (statefulRetryPrefix run retry budget tapes state).1.exhausted = true := by
  cases hs : (statefulRetryPrefix run retry budget tapes state).1.exhausted with
  | true => rfl
  | false => exact (h budget (statefulRetryStream_none_of_stopped run retry budget tapes state hs)).elim

/-- The infinite-history mass is no greater than the exhaustion probability at any finite budget. -/
theorem statefulRetryStreamLaw_nontermination_le {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape]
    [MeasurableSpace (Option (A × State))] [MeasurableSingletonClass (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) :
    (statefulRetryStreamLaw run retry state) retryStreamNontermination ≤
      (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
        retry budget state).toOuterMeasure {output | output.1.exhausted = true} := by
  rw [statefulRetryStreamLaw, Measure.map_apply (statefulRetryStream_measurable run retry state)
    retryStreamNontermination_measurable, ← statefulRetryPrefix_event_law]
  apply measure_mono
  intro tapes h
  exact statefulRetryStream_nontermination_exhausts run retry budget tapes state h

/-- A geometric exhaustion estimate plus a fixed error also bounds all nontermination mass. -/
theorem statefulRetryStreamLaw_nontermination_le_of_tail {A State Tape : Type*}
    [Fintype Tape] [Nonempty Tape] [MeasurableSpace Tape] [MeasurableSingletonClass Tape]
    [MeasurableSpace (Option (A × State))] [MeasurableSingletonClass (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (state : State) (rate error : ℝ≥0∞) (hrate : rate < 1)
    (h : ∀ budget, (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
      retry budget state).toOuterMeasure {output | output.1.exhausted = true} ≤ rate ^ budget + error) :
    (statefulRetryStreamLaw run retry state) retryStreamNontermination ≤ error := by
  have ht := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate).add (tendsto_const_nhds (x := error))
  simpa only [zero_add] using ge_of_tendsto' ht (fun budget =>
    (statefulRetryStreamLaw_nontermination_le run retry budget state).trans (h budget))

/-- Keep only the first `budget` entries, making the observation's truncation explicit in its input budget. -/
def truncateRetryStream {Value : Type*} (budget : ℕ) (stream : ℕ → Option Value) : ℕ → Option Value :=
  fun index => if index < budget then stream index else none

/-- Truncation is a measurable deterministic observation. -/
theorem truncateRetryStream_measurable {Value : Type*} [MeasurableSpace (Option Value)] (budget : ℕ) :
    Measurable (truncateRetryStream (Value := Value) budget) := by
  apply measurable_pi_lambda
  intro index
  by_cases hi : index < budget
  · simpa only [truncateRetryStream, if_pos hi] using (measurable_pi_apply index :
      Measurable (fun stream : ℕ → Option Value => stream index))
  · simp only [truncateRetryStream, if_neg hi]
    exact measurable_const

/-- The clipped stream is exactly the finite recorded history followed by absent entries. -/
theorem truncateRetryStream_prefix {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State) :
    truncateRetryStream budget (statefulRetryStream run retry tapes state) =
      fun index => (statefulRetryPrefix run retry budget tapes state).1.attempts[index]? := by
  funext index
  by_cases hi : index < budget
  · simpa only [truncateRetryStream, if_pos hi] using
      (statefulRetryPrefix_at run retry budget tapes state index hi).symm
  · rw [truncateRetryStream, if_neg hi]
    symm
    apply List.getElem?_eq_none
    exact ((runStatefulRetries_length_le (retainRetryState run) (retainedStateRetrySet retry)
      (List.ofFn (fun i : Fin budget => tapes i.val)) state).trans_eq List.length_ofFn).trans (Nat.le_of_not_gt hi)

/-- Once an observed finite prefix is terminal, clipping loses no part of its infinite observation. -/
theorem truncateRetryStream_of_stopped {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State)
    (h : (statefulRetryPrefix run retry budget tapes state).1.exhausted = false) :
    truncateRetryStream budget (statefulRetryStream run retry tapes state) = statefulRetryStream run retry tapes state := by
  rw [truncateRetryStream_prefix, statefulRetryPrefix_stopped_stream run retry budget tapes state h]

/-- The clipped complete stream has exactly the finite recorded law padded with absent entries. -/
theorem statefulRetryStreamLaw_truncate {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) :
    (statefulRetryStreamLaw run retry state).map (truncateRetryStream budget) =
      ((statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
        retry budget state).map (fun output index => output.1.attempts[index]?)).toMeasure := by
  rw [statefulRetryStreamLaw, Measure.map_map (truncateRetryStream_measurable budget)
    (statefulRetryStream_measurable run retry state)]
  have heq : (truncateRetryStream budget ∘ (fun tapes => statefulRetryStream run retry tapes state)) =
      (fun tapes index => (statefulRetryPrefix run retry budget tapes state).1.attempts[index]?) :=
    funext (fun tapes => truncateRetryStream_prefix run retry budget tapes state)
  rw [heq]
  exact statefulRetryPrefix_map_law run retry budget state
    (fun (output : RetryHistory (A × State) × State) (index : ℕ) => output.1.attempts[index]?)

/-- Truncation costs at most finite exhaustion, retaining all failed prefixes within the budget. -/
theorem statefulRetryStreamLaw_truncation_error_bound {A State Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (Option (A × State))]
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (state : State) :
    let error := (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype Tape).map (run prior))
      retry budget state).toOuterMeasure {output | output.1.exhausted = true}
    MeasureEventBiasLE (statefulRetryStreamLaw run retry state)
        ((statefulRetryStreamLaw run retry state).map (truncateRetryStream budget)) error ∧
      MeasureEventBiasLE ((statefulRetryStreamLaw run retry state).map (truncateRetryStream budget))
        (statefulRetryStreamLaw run retry state) error := by
  dsimp only
  let bad : Set (ℕ → Tape) := {tapes | (statefulRetryPrefix run retry budget tapes state).1.exhausted = true}
  have hbad := statefulRetryPrefix_event_law run retry budget state {output | output.1.exhausted = true}
  have hagree (tapes : ℕ → Tape) (hgood : tapes ∉ bad) :
      truncateRetryStream budget (statefulRetryStream run retry tapes state) = statefulRetryStream run retry tapes state := by
    apply truncateRetryStream_of_stopped run retry budget tapes state
    cases hs : (statefulRetryPrefix run retry budget tapes state).1.exhausted with
    | false => rfl
    | true => exact (hgood hs).elim
  have hm := statefulRetryStream_measurable run retry state
  have hc := (truncateRetryStream_measurable budget).comp hm
  rw [statefulRetryStreamLaw, Measure.map_map (truncateRetryStream_measurable budget) hm, ← hbad]
  exact ⟨measureEventBias_map_of_agree (uniformInfiniteTape Tape) _ _ hm hc bad
      (fun tapes hg => (hagree tapes hg).symm),
    measureEventBias_map_of_agree (uniformInfiniteTape Tape) _ _ hc hm bad hagree⟩

end Zcash.Snark.ZeroKnowledge
