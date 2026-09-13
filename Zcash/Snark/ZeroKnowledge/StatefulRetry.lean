import Zcash.Common.Probability.RetainedRetries

/-!
# Finite retained retries carrying state between attempts

Each attempt receives the state returned by its predecessor. Only the supplied
retry predicate permits another attempt; terminal outcomes stop immediately.
The output keeps the entire observed history, explicit exhaustion, and the final
state. This model does not replace a retained oracle cache by fresh verifier coins.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Prepend an observed attempt while preserving the continuation's final state. -/
def prependStatefulRetry {A State : Type*} (attempt : A)
    (output : RetryHistory A × State) : RetryHistory A × State :=
  (output.1.prepend attempt, output.2)

/-- Execute the state-carrying retry policy on a fixed sequence of private attempt tapes. -/
def runStatefulRetries {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] :
    List Tape → State → RetryHistory A × State
  | [], state => (⟨[], true⟩, state)
  | tape :: later, state =>
    let observation := run state tape
    if observation.1 ∈ retry then
      prependStatefulRetry observation.1 (runStatefulRetries run retry later observation.2)
    else (RetryHistory.stopped observation.1, observation.2)

/-- One observed transition either continues with its returned state or stops. -/
noncomputable def statefulRetryNext {A State : Type*} (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (next : State → PMF (RetryHistory A × State))
    (observation : A × State) : PMF (RetryHistory A × State) :=
  if observation.1 ∈ retry then
    (next observation.2).map (prependStatefulRetry observation.1)
  else PMF.pure (RetryHistory.stopped observation.1, observation.2)

/-- Run at most the supplied number of attempts, passing the same evolving state through them. -/
noncomputable def statefulRetries {A State : Type*} (attempt : State → PMF (A × State))
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] :
    ℕ → State → PMF (RetryHistory A × State)
  | 0, state => PMF.pure (⟨[], true⟩, state)
  | budget + 1, state =>
    (attempt state).bind (statefulRetryNext retry (statefulRetries attempt retry budget))

/-- Independent private tapes realize exactly the state-carrying probability recursion. -/
theorem statefulRetries_fromTape {A State Tape : Type*} (tapeLaw : PMF Tape)
    (run : State → Tape → A × State) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (budget : ℕ) (state : State) :
    (retryAttemptTape tapeLaw budget).map (fun tapes => runStatefulRetries run retry tapes state) =
      statefulRetries (fun state => tapeLaw.map (run state)) retry budget state := by
  induction budget generalizing state with
  | zero => exact PMF.pure_map _ _
  | succ budget ih =>
    simp only [retryAttemptTape, PMF.map_bind, PMF.map_comp, Function.comp_def,
      statefulRetries, PMF.bind_map]
    apply congrArg (PMF.bind tapeLaw)
    funext tape
    by_cases hretry : (run state tape).1 ∈ retry
    · simp only [runStatefulRetries, statefulRetryNext, hretry, if_true]
      have h := congrArg (PMF.map (prependStatefulRetry (run state tape).1)) (ih (run state tape).2)
      simpa only [PMF.map_comp, Function.comp_def] using h
    · simp only [runStatefulRetries, statefulRetryNext, hretry, if_false]
      exact PMF.map_const _ _

/-- No execution can retain more attempts than its supplied private-tape budget. -/
theorem runStatefulRetries_length_le {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (tapes : List Tape) (state : State) :
    (runStatefulRetries run retry tapes state).1.attempts.length ≤ tapes.length := by
  induction tapes generalizing state with
  | nil => exact le_rfl
  | cons tape later ih =>
    by_cases hretry : (run state tape).1 ∈ retry
    · simpa only [runStatefulRetries, hretry, if_true, prependStatefulRetry,
        RetryHistory.prepend, List.length_cons] using Nat.succ_le_succ (ih (run state tape).2)
    · simp only [runStatefulRetries, hretry, if_false, RetryHistory.stopped, List.length_cons,
        List.length_nil]
      omega

/-- Exhaustion retains every available attempt, each of which requested another attempt. -/
theorem runStatefulRetries_exhausted {A State Tape : Type*} (run : State → Tape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (tapes : List Tape) (state : State)
    (hexhausted : (runStatefulRetries run retry tapes state).1.exhausted = true) :
    (runStatefulRetries run retry tapes state).1.attempts.length = tapes.length ∧
      ∀ attempt ∈ (runStatefulRetries run retry tapes state).1.attempts, attempt ∈ retry := by
  induction tapes generalizing state with
  | nil => simp [runStatefulRetries]
  | cons tape later ih =>
    by_cases hretry : (run state tape).1 ∈ retry
    · simp only [runStatefulRetries, hretry, if_true, prependStatefulRetry, RetryHistory.prepend] at hexhausted ⊢
      obtain ⟨hlength, hall⟩ := ih (run state tape).2 hexhausted
      simp only [List.length_cons, hlength, List.mem_cons, true_and]
      intro attempt hattempt
      rcases hattempt with rfl | hattempt
      · exact hretry
      · exact hall attempt hattempt
    · simp only [runStatefulRetries, hretry, if_false, RetryHistory.stopped] at hexhausted
      cases hexhausted

end Zcash.Snark.ZeroKnowledge
