import Zcash.Snark.ZeroKnowledge.GeneratedRetryStreamLaw
import Zcash.Snark.ZeroKnowledge.MeasureMixture

/-!
# Truncating a complete seeded retry experiment

Truncation costs the probability that the actual finite generated execution
requests another attempt. That probability is averaged over the fresh seed;
neither independent generated blocks nor termination for every seed is assumed.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- The finite recorded history is a measurable function of a finite reply prefix. -/
theorem generatedRetryRecord_measurable {A State Coins Tape Generator : Type*}
    [Fintype Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (RetryHistory (A × State) × State)]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator) :
    Measurable (fun coins : ℕ → Coins => generatedRetryRecord run retry next
      (List.ofFn (fun i : Fin budget => coins i.val)) state generator) :=
  (measurable_of_countable (fun coins : Fin budget → Coins =>
    generatedRetryRecord run retry next (List.ofFn coins) state generator)).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

/-- Every event of the finite generated prefix has exactly the finite PMF probability. -/
theorem generatedRetryRecord_event_law {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator)
    (event : Set (RetryHistory (A × State) × State)) :
    (uniformInfiniteTape Coins) {coins | generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator ∈ event} =
      (generatedRetryRecordLaw run retry next budget state generator).toOuterMeasure event := by
  letI : MeasurableSpace (RetryHistory (A × State) × State) := ⊤
  have he : MeasurableSet event := trivial
  have h := generatedRetryRecord_map_law run retry next budget state generator id
  simp only [id_eq, PMF.map_id] at h
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ he, ← h,
    Measure.map_apply (generatedRetryRecord_measurable run retry next budget state generator) he]
  rfl

/-- The full generated stream and its finite truncation differ only on actual finite exhaustion. -/
theorem generatedRetryStreamLaw_truncation_error_bound {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator) :
    let error := (generatedRetryRecordLaw run retry next budget state generator).toOuterMeasure
      {output | output.1.exhausted = true}
    MeasureEventBiasLE (generatedRetryStreamLaw run retry next state generator)
        ((generatedRetryStreamLaw run retry next state generator).map (truncateRetryStream budget)) error ∧
      MeasureEventBiasLE ((generatedRetryStreamLaw run retry next state generator).map (truncateRetryStream budget))
        (generatedRetryStreamLaw run retry next state generator) error := by
  dsimp only
  let bad : Set (ℕ → Coins) := {coins | (generatedRetryRecord run retry next
    (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.exhausted = true}
  have hbad := generatedRetryRecord_event_law run retry next budget state generator
    {output | output.1.exhausted = true}
  have hagree (coins : ℕ → Coins) (hgood : coins ∉ bad) :
      truncateRetryStream budget (generatedRetryStream run retry next coins state generator) =
        generatedRetryStream run retry next coins state generator := by
    have hstop : (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.exhausted = false := by
      cases hs : (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.exhausted with
      | false => rfl
      | true => exact (hgood hs).elim
    rw [generatedRetryStream_truncate, generatedRetryStream_of_stopped run retry next budget coins state generator hstop]
  have hm := generatedRetryStream_measurable run retry next state generator
  have hc := (truncateRetryStream_measurable budget).comp hm
  rw [generatedRetryStreamLaw, Measure.map_map (truncateRetryStream_measurable budget) hm, ← hbad]
  exact ⟨measureEventBias_map_of_agree (uniformInfiniteTape Coins) _ _ hm hc bad
      (fun coins hg => (hagree coins hg).symm),
    measureEventBias_map_of_agree (uniformInfiniteTape Coins) _ _ hc hm bad hagree⟩

/-- Sample the private initial state once, independently of the infinite public reply tape. -/
noncomputable def seededGeneratedRetryStreamLaw {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (source : PMF Generator) (state : State) : Measure (ℕ → Option (A × State)) :=
  pmfMeasureMixture source (generatedRetryStreamLaw run retry next state)

/-- The fresh-seed complete-stream law is normalized independently of stopping. -/
instance seededGeneratedRetryStreamLaw_isProbabilityMeasure {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (source : PMF Generator) (state : State) :
    IsProbabilityMeasure (seededGeneratedRetryStreamLaw run retry next source state) := by
  unfold seededGeneratedRetryStreamLaw
  infer_instance

/-- Finite truncation of the fresh-seed experiment is exactly its finite seeded public history. -/
theorem seededGeneratedRetryStreamLaw_truncate {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (source : PMF Generator) (budget : ℕ) (state : State) :
    (seededGeneratedRetryStreamLaw run retry next source state).map (truncateRetryStream budget) =
      ((source.bind (generatedRetryRecordLaw run retry next budget state)).map
        (fun output index => output.1.attempts[index]?)).toMeasure := by
  rw [seededGeneratedRetryStreamLaw, pmfMeasureMixture_map _ _ _ (truncateRetryStream_measurable budget)]
  simp_rw [generatedRetryStreamLaw_truncate]
  rw [pmfMeasureMixture_toMeasure, PMF.map_bind]

/-- Averaging actual exhaustion over the seed bounds both directions of the complete-stream truncation. -/
theorem seededGeneratedRetryStreamLaw_truncation_error_bound {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (source : PMF Generator) (budget : ℕ) (state : State) :
    let error := (source.bind (generatedRetryRecordLaw run retry next budget state)).toOuterMeasure
      {output | output.1.exhausted = true}
    MeasureEventBiasLE (seededGeneratedRetryStreamLaw run retry next source state)
        ((seededGeneratedRetryStreamLaw run retry next source state).map (truncateRetryStream budget)) error ∧
      MeasureEventBiasLE ((seededGeneratedRetryStreamLaw run retry next source state).map (truncateRetryStream budget))
        (seededGeneratedRetryStreamLaw run retry next source state) error := by
  dsimp only
  rw [seededGeneratedRetryStreamLaw, pmfMeasureMixture_map _ _ _ (truncateRetryStream_measurable budget),
    PMF.toOuterMeasure_bind_apply]
  exact ⟨measureEventBias_mixture_average source _ _ _ (fun generator =>
      (generatedRetryStreamLaw_truncation_error_bound run retry next budget state generator).1),
    measureEventBias_mixture_average source _ _ _ (fun generator =>
      (generatedRetryStreamLaw_truncation_error_bound run retry next budget state generator).2)⟩

end Zcash.Snark.ZeroKnowledge
