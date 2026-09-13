import Zcash.Snark.ZeroKnowledge.GeneratedRetryStreamLaw

/-!
# Complete private prefixes and recorded public retry histories

Public reply slots are sampled independently of the whole private prefix. The
source may correlate every private word and every attempt. Retaining intermediate
public states commutes exactly with replay from a continuing generator.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Retry on separated finite tapes, retaining each attempted result and public state. -/
def recordedCoinRetries {A State Coins Tape : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {budget : ℕ}
    (coins : Fin budget → Coins) (tapes : Fin budget → Tape) (state : State) :
    RetryHistory (A × State) × State :=
  runStatefulRetries (retainRetryState (fun state pair => run state pair.1 pair.2))
    (retainedStateRetrySet retry) (List.ofFn (fun i => (coins i, tapes i))) state

/-- Sample all public replies independently of one arbitrary joint private prefix. -/
noncomputable def recordedCoinRetriesFromSource {A State Coins Tape : Type*}
    [Fintype Coins] [Nonempty Coins]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {budget : ℕ}
    (source : PMF (Fin budget → Tape)) (state : State) : PMF (RetryHistory (A × State) × State) :=
  sourceTapeExperiment (PMF.uniformOfFintype (Fin budget → Coins)) source
    (fun coins tapes => recordedCoinRetries run retry coins tapes state)

/-- Uniform separated private and public tapes reproduce the recorded stateful retry law. -/
theorem recordedCoinRetriesFromSource_uniform {A State Coins Tape : Type*}
    [Fintype Coins] [Nonempty Coins] [Fintype Tape] [Nonempty Tape]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (state : State) :
    recordedCoinRetriesFromSource run retry (PMF.uniformOfFintype (Fin budget → Tape)) state =
      statefulRetryRecorded
        (fun prior => (PMF.uniformOfFintype (Coins × Tape)).map (fun pair => run prior pair.1 pair.2))
        retry budget state := by
  have h := uniformRetryTape_source_law budget
    (fun tapes => runStatefulRetries (retainRetryState (fun s pair => run s pair.1 pair.2))
      (retainedStateRetrySet retry) tapes state)
  exact h.trans (statefulRetryRecorded_fromTape _ _ retry budget state)

/-- Generated public histories equal replay from the entire generated private prefix. -/
theorem generatedRetryRecord_replay {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    {budget : ℕ} (coins : Fin budget → Coins) (state : State) (generator : Generator) :
    generatedRetryRecord run retry next (List.ofFn coins) state generator =
      recordedCoinRetries run retry coins (drawGeneratorTape next budget generator).1 state := by
  rw [generatedRetryRecord, runGeneratedCoinRetries_replay]
  simp only [List.length_ofFn, zip_ofFn_pair, recordedCoinRetries, drawGeneratorTape_cast]
  rfl

/-- One fresh generator state and independent reply slots give the exact generated-prefix source law. -/
theorem generatedRetryRecordLaw_source {A State Coins Tape Generator : Type*}
    [Fintype Coins] [Nonempty Coins]
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (source : PMF Generator) (budget : ℕ) (state : State) :
    source.bind (generatedRetryRecordLaw run retry next budget state) =
      recordedCoinRetriesFromSource run retry
        (source.map (fun generator => (drawGeneratorTape next budget generator).1)) state := by
  calc
    source.bind (generatedRetryRecordLaw run retry next budget state) =
        source.bind (fun generator => (PMF.uniformOfFintype (Fin budget → Coins)).map
          (fun coins => recordedCoinRetries run retry coins (drawGeneratorTape next budget generator).1 state)) := by
      apply congrArg (PMF.bind source)
      funext generator
      apply congrArg (fun observe => (PMF.uniformOfFintype (Fin budget → Coins)).map observe)
      funext coins
      exact generatedRetryRecord_replay run retry next coins state generator
    _ = _ := by
      simp only [recordedCoinRetriesFromSource, sourceTapeExperiment, PMF.map_comp, Function.comp_def]
      exact PMF.bind_comm source (PMF.uniformOfFintype (Fin budget → Coins))
        (fun generator coins => PMF.pure
          (recordedCoinRetries run retry coins (drawGeneratorTape next budget generator).1 state))

end Zcash.Snark.ZeroKnowledge
