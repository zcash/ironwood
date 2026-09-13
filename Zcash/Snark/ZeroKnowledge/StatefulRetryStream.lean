import Zcash.Snark.ZeroKnowledge.StatefulRetry
import Mathlib.Data.List.OfFn

/-!
# The complete observable stream of stateful retries

Each present entry retains the attempted result and the resulting public state.
After a terminal attempt every subsequent entry is absent. An execution that
never stops retains its entire infinite stream. The implementation performs the
same retry decision as the finite runner, without a termination assumption.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Record the state returned by every attempt as part of that attempt's observation. -/
def retainRetryState {A State Tape : Type*} (run : State → Tape → A × State)
    (state : State) (tape : Tape) : (A × State) × State :=
  let observation := run state tape
  (observation, observation.2)

/-- Retaining the new state does not change the attempt's retry decision. -/
abbrev retainedStateRetrySet {A State : Type*} (retry : Set A) : Set (A × State) :=
  {observation | observation.1 ∈ retry}

/-- Forget intermediate states while preserving all ordinary observations and the final state. -/
def forgetRetryStates {A State : Type*} (output : RetryHistory (A × State) × State) :
    RetryHistory A × State := (output.1.map Prod.fst, output.2)

/-- The extra recorded states project exactly to the existing deterministic retry runner. -/
theorem runStatefulRetries_forget_states {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (tapes : List Tape) (state : State) :
    forgetRetryStates (runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry) tapes state) =
      runStatefulRetries run retry tapes state := by
  induction tapes generalizing state with
  | nil => rfl
  | cons tape tapes ih =>
    by_cases hr : (run state tape).1 ∈ retry
    · simpa only [runStatefulRetries, retainRetryState, retainedStateRetrySet, Set.mem_setOf_eq,
        hr, if_true, forgetRetryStates, prependStatefulRetry, RetryHistory.prepend,
        RetryHistory.map, List.map_cons] using congrArg (prependStatefulRetry (run state tape).1)
          (ih (run state tape).2)
    · simp only [runStatefulRetries, retainRetryState, retainedStateRetrySet, Set.mem_setOf_eq,
        hr, if_false, forgetRetryStates, RetryHistory.stopped, RetryHistory.map,
        List.map_cons, List.map_nil]

/-- The unbounded execution, with absent entries exactly after the policy stops. -/
def statefulRetryStream {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (tapes : ℕ → Tape) (state : State) : ℕ → Option (A × State)
  | 0 => some (run state (tapes 0))
  | index + 1 =>
    let observation := run state (tapes 0)
    if observation.1 ∈ retry then
      statefulRetryStream run retry (fun i => tapes (i + 1)) observation.2 index
    else none

/-- The finite runner on the prefix of a complete tape stream, retaining each returned state. -/
def statefulRetryPrefix {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State) : RetryHistory (A × State) × State :=
  runStatefulRetries (retainRetryState run) (retainedStateRetrySet retry)
    (List.ofFn (fun i : Fin budget => tapes i.val)) state

/-- Zero budget records exhaustion before any attempt. -/
theorem statefulRetryPrefix_zero {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (tapes : ℕ → Tape) (state : State) :
    statefulRetryPrefix run retry 0 tapes state = (⟨[], true⟩, state) := by
  simp [statefulRetryPrefix, runStatefulRetries]

/-- Extending a tape prefix executes exactly one attempt and follows its retained-state decision. -/
theorem statefulRetryPrefix_succ {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State) :
    statefulRetryPrefix run retry (budget + 1) tapes state =
      if (run state (tapes 0)).1 ∈ retry then
        prependStatefulRetry (run state (tapes 0))
          (statefulRetryPrefix run retry budget (fun i => tapes (i + 1)) (run state (tapes 0)).2)
      else (RetryHistory.stopped (run state (tapes 0)), (run state (tapes 0)).2) := by
  simp only [statefulRetryPrefix, List.ofFn_succ, runStatefulRetries, retainRetryState,
    retainedStateRetrySet, Set.mem_setOf_eq, Fin.val_zero, Fin.val_succ]

/-- Every available finite observation is exactly its corresponding infinite-stream entry. -/
theorem statefulRetryPrefix_at {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State) (index : ℕ) (hindex : index < budget) :
    (statefulRetryPrefix run retry budget tapes state).1.attempts[index]? =
      statefulRetryStream run retry tapes state index := by
  induction budget generalizing tapes state index with
  | zero => omega
  | succ budget ih =>
    rw [statefulRetryPrefix_succ]
    by_cases hr : (run state (tapes 0)).1 ∈ retry
    · rw [if_pos hr]
      cases index with
      | zero => rfl
      | succ index =>
        simpa only [prependStatefulRetry, RetryHistory.prepend, List.getElem?_cons_succ,
          statefulRetryStream, hr, if_true] using ih (fun i => tapes (i + 1))
            (run state (tapes 0)).2 index (by omega)
    · rw [if_neg hr]
      cases index <;> simp [RetryHistory.stopped, statefulRetryStream, hr]

/-- A stopped finite execution determines the entire infinite observation, including every absent suffix entry. -/
theorem statefulRetryPrefix_stopped_stream {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State)
    (hstopped : (statefulRetryPrefix run retry budget tapes state).1.exhausted = false) :
    (fun index => (statefulRetryPrefix run retry budget tapes state).1.attempts[index]?) =
      statefulRetryStream run retry tapes state := by
  induction budget generalizing tapes state with
  | zero => simp [statefulRetryPrefix_zero] at hstopped
  | succ budget ih =>
    rw [statefulRetryPrefix_succ] at hstopped ⊢
    by_cases hr : (run state (tapes 0)).1 ∈ retry
    · simp only [if_pos hr, prependStatefulRetry, RetryHistory.prepend] at hstopped ⊢
      have h := ih (fun i => tapes (i + 1)) (run state (tapes 0)).2 hstopped
      funext index
      cases index with
      | zero => rfl
      | succ index =>
        simpa only [List.getElem?_cons_succ, statefulRetryStream, hr, if_true] using congrFun h index
    · simp only [if_neg hr, RetryHistory.stopped]
      funext index
      cases index <;> simp [statefulRetryStream, hr]

/-- A terminal prefix has no stream entry at the exhausted-capacity index. -/
theorem statefulRetryStream_none_of_stopped {A State Tape : Type*}
    (run : State → Tape → A × State) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (budget : ℕ) (tapes : ℕ → Tape) (state : State)
    (hstopped : (statefulRetryPrefix run retry budget tapes state).1.exhausted = false) :
    statefulRetryStream run retry tapes state budget = none := by
  rw [← statefulRetryPrefix_stopped_stream run retry budget tapes state hstopped]
  apply List.getElem?_eq_none
  exact (runStatefulRetries_length_le (retainRetryState run) (retainedStateRetrySet retry)
    (List.ofFn (fun i : Fin budget => tapes i.val)) state).trans_eq List.length_ofFn

end Zcash.Snark.ZeroKnowledge
