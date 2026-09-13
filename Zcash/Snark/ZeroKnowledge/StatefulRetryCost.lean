import Zcash.Snark.ZeroKnowledge.StatefulRetry

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Execute retained retries, charging every attempt, decision, history node, and state handoff. -/
def runStatefulRetriesCosted {A State Tape : Type*}
    (run : State → Tape → (A × State) × ℕ) (retry : A → Bool × ℕ) :
    List Tape → State → (RetryHistory A × State) × ℕ
  | [], state => ((⟨[], true⟩, state), 4)
  | tape :: later, state =>
    let observation := run state tape
    let check := retry observation.1.1
    if check.1 then
      let rest := runStatefulRetriesCosted run retry later observation.1.2
      (prependStatefulRetry observation.1.1 rest.1, observation.2 + check.2 + rest.2 + 8)
    else ((RetryHistory.stopped observation.1.1, observation.1.2), observation.2 + check.2 + 7)

/-- The counted runner keeps exactly the original retry history, final state, and exhaustion flag. -/
theorem runStatefulRetriesCosted_result {A State Tape : Type*}
    (run : State → Tape → (A × State) × ℕ) (retry : A → Bool × ℕ)
    (tapes : List Tape) (state : State) :
    (runStatefulRetriesCosted run retry tapes state).1 =
      runStatefulRetries (fun state tape => (run state tape).1) {a | (retry a).1 = true} tapes state := by
  induction tapes generalizing state with
  | nil => rfl
  | cons tape later ih =>
    by_cases h : (retry (run state tape).1.1).1 = true
    · simp only [runStatefulRetriesCosted, runStatefulRetries, Set.mem_setOf_eq, if_pos h, ih]
    · simp only [runStatefulRetriesCosted, runStatefulRetries, Set.mem_setOf_eq, if_neg h]

/-- Refining stored tape representations preserves the literal retry computation on the source tapes. -/
theorem runStatefulRetries_map_tape {A State SourceTape StoredTape : Type*}
    (source : State → SourceTape → A × State) (stored : State → StoredTape → A × State)
    (encode : SourceTape → StoredTape) (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (hsource : ∀ state tape, stored state (encode tape) = source state tape)
    (tapes : List SourceTape) (state : State) :
    runStatefulRetries stored retry (tapes.map encode) state = runStatefulRetries source retry tapes state := by
  induction tapes generalizing state with
  | nil => rfl
  | cons tape later ih =>
    simp only [List.map_cons, runStatefulRetries, hsource]
    split
    · rewrite [ih]
      rfl
    · rfl

/-- Equal retry predicates give the same computation, independently of their decision proofs. -/
theorem runStatefulRetries_congr_retry {A State Tape : Type*}
    (run : State → Tape → A × State) (left right : Set A)
    [dl : DecidablePred (fun a => a ∈ left)] [dr : DecidablePred (fun a => a ∈ right)]
    (h : left = right) (tapes : List Tape) (state : State) :
    runStatefulRetries run left tapes state = runStatefulRetries run right tapes state := by
  cases h
  have hd : dl = dr := Subsingleton.elim _ _
  cases hd
  rfl

/-- No counted execution can record more attempts than its supplied tape list. -/
theorem runStatefulRetriesCosted_length_le {A State Tape : Type*}
    (run : State → Tape → (A × State) × ℕ) (retry : A → Bool × ℕ)
    (tapes : List Tape) (state : State) :
    (runStatefulRetriesCosted run retry tapes state).1.1.attempts.length ≤ tapes.length := by
  rewrite [runStatefulRetriesCosted_result]
  exact runStatefulRetries_length_le _ _ tapes state

end Zcash.Snark.ZeroKnowledge
