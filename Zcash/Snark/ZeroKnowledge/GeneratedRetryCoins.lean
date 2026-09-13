import Zcash.Snark.ZeroKnowledge.GeneratorTape
import Zcash.Snark.ZeroKnowledge.StatefulRetry
import Mathlib.Data.List.OfFn

/-!
# Continuous private generation with separately supplied verifier coins

Each started attempt receives its public reply slots and one full private block.
Reply slots never come from the private generator. The private state stops at the
last started attempt; the public observation nevertheless agrees with replay
from a preallocated private prefix covering the entire attempt budget.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Retained retries with one supplied coin tape per attempt and a continuing private generator. -/
def runGeneratedCoinRetries {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator) :
    List Coins → State → Generator → (RetryHistory A × State) × Generator
  | [], state, generator => ((⟨[], true⟩, state), generator)
  | coins :: rest, state, generator =>
    let tape := next generator
    let observed := run state coins tape.1
    if observed.1 ∈ retry then
      let later := runGeneratedCoinRetries run retry next rest observed.2 tape.2
      (prependStatefulRetry observed.1 later.1, later.2)
    else ((RetryHistory.stopped observed.1, observed.2), tape.2)

/-- The separately supplied public coins pair with the same private blocks in deterministic replay. -/
theorem runGeneratedCoinRetries_replay {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    (runGeneratedCoinRetries run retry next coins state generator).1 =
      runStatefulRetries (fun s pair => run s pair.1 pair.2) retry
        (coins.zip (List.ofFn (drawGeneratorTape next coins.length generator).1)) state := by
  induction coins generalizing state generator with
  | nil => rfl
  | cons coin coins ih =>
    simp only [List.length_cons, drawGeneratorTape, List.ofFn_cons, List.zip_cons_cons,
      runGeneratedCoinRetries, runStatefulRetries]
    split
    · exact congrArg (prependStatefulRetry (run state coin (next generator).1).1)
        (ih (run state coin (next generator).1).2 (next generator).2)
    · rfl

/-- No private blocks for later attempts are consumed after a terminal observation. -/
theorem runGeneratedCoinRetries_state {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    (runGeneratedCoinRetries run retry next coins state generator).2 =
      ((fun g => (next g).2)^[
        (runGeneratedCoinRetries run retry next coins state generator).1.1.attempts.length]) generator := by
  induction coins generalizing state generator with
  | nil => rfl
  | cons coin coins ih =>
    by_cases hretry : (run state coin (next generator).1).1 ∈ retry
    · simpa only [runGeneratedCoinRetries, hretry, if_true, prependStatefulRetry,
        RetryHistory.prepend, List.length_cons, Function.iterate_succ_apply] using
        ih (run state coin (next generator).1).2 (next generator).2
    · simp only [runGeneratedCoinRetries, hretry, if_false, RetryHistory.stopped,
        List.length_cons, List.length_nil, Function.iterate_succ_apply,
        Function.iterate_zero_apply]

/-- Each actually started attempt consumes one of the separately supplied coin tapes. -/
theorem runGeneratedCoinRetries_length_le {A State Coins Tape Generator : Type*}
    (run : State → Coins → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Tape × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    (runGeneratedCoinRetries run retry next coins state generator).1.1.attempts.length ≤ coins.length := by
  rw [runGeneratedCoinRetries_replay]
  exact (runStatefulRetries_length_le _ retry _ state).trans_eq
    (by simp only [List.length_zip, List.length_ofFn, min_self])

/-- Fixed-size private blocks advance the word generator by exactly the number of consumed words. -/
theorem runGeneratedCoinRetries_word_state {A State Coins Word Generator : Type*} {width : ℕ}
    (run : State → Coins → (Fin width → Word) → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : Generator → Word × Generator)
    (coins : List Coins) (state : State) (generator : Generator) :
    (runGeneratedCoinRetries run retry (drawGeneratorTape next width) coins state generator).2 =
      ((fun g => (next g).2)^[
        (runGeneratedCoinRetries run retry (drawGeneratorTape next width) coins state generator).1.1.attempts.length
          * width]) generator := by
  rw [runGeneratedCoinRetries_state]
  have hstep : (fun g => (drawGeneratorTape next width g).2) =
      (fun g => (next g).2)^[width] := funext (drawGeneratorTape_state next width)
  rw [hstep, ← Function.iterate_mul, Nat.mul_comm width]

/-- Pairing two equal-length finite tapes enumerates the same ordered list of pairs. -/
theorem zip_ofFn_pair {A B : Type*} {count : ℕ} (left : Fin count → A) (right : Fin count → B) :
    (List.ofFn left).zip (List.ofFn right) = List.ofFn (fun i => (left i, right i)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.ofFn_succ, List.zip_cons_cons]
    exact congrArg (List.cons (left 0, right 0)) (ih (fun i => left i.succ) (fun i => right i.succ))

/-- Converting the input tape before replay is the same as converting each started attempt's tape. -/
theorem runStatefulRetries_map {A State Tape Input : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (convert : Input → Tape) (tapes : List Input) (state : State) :
    runStatefulRetries run retry (tapes.map convert) state =
      runStatefulRetries (fun s tape => run s (convert tape)) retry tapes state := by
  induction tapes generalizing state with
  | nil => rfl
  | cons tape tapes ih =>
    simp only [List.map_cons, runStatefulRetries]
    split
    · exact congrArg (prependStatefulRetry (run state (convert tape)).1) (ih (run state (convert tape)).2)
    · rfl

end Zcash.Snark.ZeroKnowledge
