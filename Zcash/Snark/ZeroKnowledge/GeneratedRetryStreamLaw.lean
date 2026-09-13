import Zcash.Snark.ZeroKnowledge.GeneratedRetryStream
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamTail

/-!
# Infinite public reply tapes with one continuing private generator

Each fixed seed runs on an independent infinite stream of oracle reply slots.
The complete law is normalized before any termination or PRNG assumption. Its
finite truncations are exactly the finite continuing-generator observations.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- The finite public history under independent uniform reply slots and one fixed generator state. -/
noncomputable def generatedRetryRecordLaw {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] (run : State → Coins → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator) : PMF (RetryHistory (A × State) × State) :=
  (PMF.uniformOfFintype (Fin budget → Coins)).map
    (fun coins => generatedRetryRecord run retry next (List.ofFn coins) state generator)

/-- A recorded generated history consumes at most the available reply-slot blocks. -/
theorem generatedRetryRecord_length_le {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    (generatedRetryRecord run retry next coins state generator).1.attempts.length ≤ coins.length := by
  rw [generatedRetryRecord_eq_run]
  exact runStatefulRetries_length_le _ _ _ _

/-- Every complete public stream coordinate depends measurably on a finite reply prefix. -/
theorem generatedRetryStream_measurable {A State Coins Tape Generator : Type*}
    [Fintype Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (state : State) (generator : Generator) :
    Measurable (fun coins => generatedRetryStream run retry next coins state generator) := by
  apply measurable_pi_lambda
  intro index
  have heq : (fun coins => generatedRetryStream run retry next coins state generator index) =
      (fun coins => (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin (index + 1) => coins i.val)) state generator).1.attempts[index]?) := by
    funext coins
    exact generatedRetryStream_at run retry next (index + 1) coins state generator index (Nat.lt_succ_self _)
  rw [heq]
  exact (measurable_of_countable (fun coins : Fin (index + 1) → Coins =>
    (generatedRetryRecord run retry next (List.ofFn coins) state generator).1.attempts[index]?)).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

/-- The complete observation law for one initial generator state and an independent reply stream. -/
noncomputable def generatedRetryStreamLaw {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (state : State) (generator : Generator) : Measure (ℕ → Option (A × State)) :=
  (uniformInfiniteTape Coins).map (fun coins => generatedRetryStream run retry next coins state generator)

/-- The complete generated experiment retains probability one even if it never stops. -/
instance generatedRetryStreamLaw_isProbabilityMeasure {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (state : State) (generator : Generator) :
    IsProbabilityMeasure (generatedRetryStreamLaw run retry next state generator) :=
  Measure.isProbabilityMeasure_map (generatedRetryStream_measurable run retry next state generator).aemeasurable

/-- Clipping the public stream gives the exact finite continuing-generator history. -/
theorem generatedRetryStream_truncate {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (coins : ℕ → Coins) (state : State) (generator : Generator) :
    truncateRetryStream budget (generatedRetryStream run retry next coins state generator) =
      fun index => (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.attempts[index]? := by
  funext index
  by_cases hi : index < budget
  · rw [truncateRetryStream, if_pos hi]
    exact generatedRetryStream_at run retry next budget coins state generator index hi
  · rw [truncateRetryStream, if_neg hi]
    symm
    apply List.getElem?_eq_none
    exact ((generatedRetryRecord_length_le run retry next _ state generator).trans_eq List.length_ofFn).trans
      (Nat.le_of_not_gt hi)

/-- Observing a finite prefix of the infinite reply tape gives exactly the finite PMF experiment. -/
theorem generatedRetryRecord_map_law {A State Coins Tape Generator Output : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace Output] (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator)
    (observe : (RetryHistory (A × State) × State) → Output) :
    (uniformInfiniteTape Coins).map (fun coins => observe (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator)) =
      ((generatedRetryRecordLaw run retry next budget state generator).map observe).toMeasure := by
  simpa only [generatedRetryRecordLaw, PMF.map_comp, Function.comp_def] using
    uniformInfiniteTape_prefix_map budget (fun coins : Fin budget → Coins =>
      observe (generatedRetryRecord run retry next (List.ofFn coins) state generator))

/-- The complete law's clipped observation agrees exactly with finite-budget public replay. -/
theorem generatedRetryStreamLaw_truncate {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins] [MeasurableSpace Coins] [MeasurableSingletonClass Coins]
    [MeasurableSpace (Option (A × State))]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (state : State) (generator : Generator) :
    (generatedRetryStreamLaw run retry next state generator).map (truncateRetryStream budget) =
      ((generatedRetryRecordLaw run retry next budget state generator).map
        (fun output index => output.1.attempts[index]?)).toMeasure := by
  rw [generatedRetryStreamLaw, Measure.map_map (truncateRetryStream_measurable budget)
    (generatedRetryStream_measurable run retry next state generator)]
  have heq : (truncateRetryStream budget ∘
      (fun coins => generatedRetryStream run retry next coins state generator)) =
      (fun coins index => (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.attempts[index]?) :=
    funext (fun coins => generatedRetryStream_truncate run retry next budget coins state generator)
  rw [heq]
  exact generatedRetryRecord_map_law run retry next budget state generator
    (fun (output : RetryHistory (A × State) × State) (index : ℕ) => output.1.attempts[index]?)

end Zcash.Snark.ZeroKnowledge
