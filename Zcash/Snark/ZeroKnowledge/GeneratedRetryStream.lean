import Zcash.Snark.ZeroKnowledge.GeneratedRetryCoins
import Zcash.Snark.ZeroKnowledge.StatefulRetryStream

/-!
# Complete retry streams from a continuing private generator

The execution state contains both the public state and the private generator.
Only the attempted result and public state are recorded. Each started attempt
allocates one whole private block, exactly as in `runGeneratedCoinRetries`.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Retain the attempt's public state without exposing the continuing generator. -/
def generatedPublicRun {A State Coins Tape : Type*}
    (run : State → Coins → Tape → A × State) (state : State) (coins : Coins) (tape : Tape) :
    (A × State) × State :=
  let observed := run state coins tape
  (observed, observed.2)

/-- One generated attempt has a public observation and a separate private execution state. -/
def generatedRecordedStep {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (next : Generator → Tape × Generator)
    (state : State × Generator) (coins : Coins) : (A × State) × (State × Generator) :=
  let block := next state.2
  let observed := run state.1 coins block.1
  (observed, (observed.2, block.2))

/-- The finite continuing-generator runner with each intermediate public state retained. -/
def generatedRetryRecord {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    RetryHistory (A × State) × State :=
  (runGeneratedCoinRetries (generatedPublicRun run) (retainedStateRetrySet retry)
    next coins state generator).1

/-- Pairing the public and generator states is an exact execution of the existing finite runner. -/
theorem generatedRecordedStep_run {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    runStatefulRetries (generatedRecordedStep run next) (retainedStateRetrySet retry)
        coins (state, generator) =
      let result := runGeneratedCoinRetries (generatedPublicRun run)
        (retainedStateRetrySet retry) next coins state generator
      (result.1.1, (result.1.2, result.2)) := by
  induction coins generalizing state generator with
  | nil => rfl
  | cons coin coins ih =>
    by_cases hr : (run state coin (next generator).1).1 ∈ retry
    · simp only [runStatefulRetries, generatedRecordedStep, generatedPublicRun,
        runGeneratedCoinRetries, retainedStateRetrySet, Set.mem_setOf_eq, hr, if_true]
      rw [ih]
      rfl
    · simp only [runStatefulRetries, generatedRecordedStep, generatedPublicRun,
        runGeneratedCoinRetries, retainedStateRetrySet, Set.mem_setOf_eq, hr, if_false]

/-- Erasing only the final generator state gives exactly the public finite history. -/
theorem generatedRetryRecord_eq_run {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    generatedRetryRecord run retry next coins state generator =
      let result := runStatefulRetries (generatedRecordedStep run next)
        (retainedStateRetrySet retry) coins (state, generator)
      (result.1, result.2.1) := by
  rw [generatedRecordedStep_run]
  rfl

/-- The complete public stream retains all attempts and caches, with private generator states erased. -/
def generatedRetryStream {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : ℕ → Coins) (state : State) (generator : Generator) : ℕ → Option (A × State) :=
  fun index => (statefulRetryStream (generatedRecordedStep run next)
    (retainedStateRetrySet retry) coins (state, generator) index).map Prod.fst

/-- Every public stream coordinate is exactly its finite continuing-generator prefix observation. -/
theorem generatedRetryStream_at {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (coins : ℕ → Coins) (state : State) (generator : Generator)
    (index : ℕ) (hindex : index < budget) :
    generatedRetryStream run retry next coins state generator index =
      (generatedRetryRecord run retry next (List.ofFn (fun i : Fin budget => coins i.val))
        state generator).1.attempts[index]? := by
  rw [generatedRetryStream, ← statefulRetryPrefix_at _ _ budget coins (state, generator) index hindex]
  have hf := runStatefulRetries_forget_states (generatedRecordedStep run next)
    (retainedStateRetrySet retry) (List.ofFn (fun i : Fin budget => coins i.val)) (state, generator)
  have ha := congrArg (fun result => result.1.attempts[index]?) hf
  simp only [forgetRetryStates, RetryHistory.map, List.getElem?_map] at ha
  rw [generatedRetryRecord_eq_run]
  exact ha

/-- A finite prefix that stopped determines the entire subsequent public stream. -/
theorem generatedRetryStream_of_stopped {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (budget : ℕ) (coins : ℕ → Coins) (state : State) (generator : Generator)
    (hstop : (generatedRetryRecord run retry next
      (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.exhausted = false) :
    generatedRetryStream run retry next coins state generator =
      fun index => (generatedRetryRecord run retry next
        (List.ofFn (fun i : Fin budget => coins i.val)) state generator).1.attempts[index]? := by
  have hf := runStatefulRetries_forget_states (generatedRecordedStep run next)
    (retainedStateRetrySet retry) (List.ofFn (fun i : Fin budget => coins i.val)) (state, generator)
  have hex : (statefulRetryPrefix (generatedRecordedStep run next) (retainedStateRetrySet retry)
      budget coins (state, generator)).1.exhausted = false := by
    rw [generatedRetryRecord_eq_run] at hstop
    exact (congrArg (fun result => result.1.exhausted) hf).trans hstop
  funext index
  rw [generatedRetryStream, ← statefulRetryPrefix_stopped_stream _ _ budget coins (state, generator) hex]
  have ha := congrArg (fun result => result.1.attempts[index]?) hf
  simp only [forgetRetryStates, RetryHistory.map, List.getElem?_map] at ha
  rw [generatedRetryRecord_eq_run]
  exact ha

end Zcash.Snark.ZeroKnowledge
