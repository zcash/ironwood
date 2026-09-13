import Zcash.Snark.ZeroKnowledge.CachedOracle
import Zcash.Common.Probability.DistributionAgreement

/-!
# Programming a finite oracle trace without changing cached answers

Programming fails on every previously answered address, even if the proposed
answer happens to match. This conservative policy never overwrites an answer.
Independent execution and the actual cached oracle can then be coupled until
the first such conflict.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open scoped ENNReal

/-- Install a chronological trace of answers, refusing every previously answered address. -/
def programOracleTrace {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) : List (Query × Reply) → Option (OracleCache Query Reply)
  | [] => some cache
  | (query, reply) :: rest =>
    match oracleCacheLookup cache query with
    | some _ => none
    | none => programOracleTrace ((query, reply) :: cache) rest

/-- Programming two traces is sequential programming with the resulting cache. -/
theorem programOracleTrace_append {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (first rest : List (Query × Reply)) :
    programOracleTrace cache (first ++ rest) =
      (programOracleTrace cache first).bind (fun next => programOracleTrace next rest) := by
  induction first generalizing cache with
  | nil => rfl
  | cons entry first ih =>
    rcases entry with ⟨query, reply⟩
    simp only [List.cons_append, programOracleTrace]
    cases oracleCacheLookup cache query with
    | some value => rfl
    | none => exact ih ((query, reply) :: cache)

/-- Successful programming preserves every answer in the initial cache. -/
theorem programOracleTrace_keeps {Query Reply : Type*} [DecidableEq Query]
    (trace : List (Query × Reply)) (cache finalCache : OracleCache Query Reply)
    (hprogram : programOracleTrace cache trace = some finalCache)
    (query : Query) (reply : Reply) (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup finalCache query = some reply := by
  induction trace generalizing cache with
  | nil =>
    cases Option.some.inj hprogram
    exact hstored
  | cons entry trace ih =>
    rcases entry with ⟨address, answer⟩
    cases hlookup : oracleCacheLookup cache address with
    | some value => simp [programOracleTrace, hlookup] at hprogram
    | none =>
      have hne : address ≠ query := by
        intro h
        subst address
        rw [hstored] at hlookup
        contradiction
      apply ih ((address, answer) :: cache)
      · simpa only [programOracleTrace, hlookup] using hprogram
      · simpa only [oracleCacheLookup_cons_ne cache address query answer hne] using hstored

/-- Successful programming stores each reply from the proposed trace. -/
theorem programOracleTrace_answers {Query Reply : Type*} [DecidableEq Query]
    (trace : List (Query × Reply)) (cache finalCache : OracleCache Query Reply)
    (hprogram : programOracleTrace cache trace = some finalCache) :
    ∀ entry ∈ trace, oracleCacheLookup finalCache entry.1 = some entry.2 := by
  induction trace generalizing cache with
  | nil => simp
  | cons entry trace ih =>
    rcases entry with ⟨query, reply⟩
    cases hlookup : oracleCacheLookup cache query with
    | some value => simp [programOracleTrace, hlookup] at hprogram
    | none =>
      have hrest : programOracleTrace ((query, reply) :: cache) trace = some finalCache := by
        simpa only [programOracleTrace, hlookup] using hprogram
      intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | hentry
      · exact programOracleTrace_keeps trace ((query, reply) :: cache) finalCache hrest
          query reply (oracleCacheLookup_cons_same cache query reply)
      · exact ih ((query, reply) :: cache) hrest entry hentry

/-- A trace of distinct fresh addresses can always be programmed. -/
theorem programOracleTrace_ne_none_of_fresh {Query Reply : Type*} [DecidableEq Query]
    (trace : List (Query × Reply)) (cache : OracleCache Query Reply)
    (hdistinct : (trace.map Prod.fst).Nodup)
    (hfresh : ∀ query ∈ trace.map Prod.fst, query ∉ cache.map Prod.fst) :
    programOracleTrace cache trace ≠ none := by
  induction trace generalizing cache with
  | nil => simp [programOracleTrace]
  | cons entry trace ih =>
    rcases entry with ⟨query, reply⟩
    have hdistinct' : query ∉ trace.map Prod.fst ∧ (trace.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hdistinct
    have hlookup : oracleCacheLookup cache query = none :=
      (oracleCacheLookup_eq_none cache query).mpr (hfresh query (by simp))
    simp only [programOracleTrace, hlookup]
    apply ih ((query, reply) :: cache) hdistinct'.2
    intro other hother
    have hne : other ≠ query := by
      intro h
      exact hdistinct'.1 (h ▸ hother)
    simpa only [List.map_cons, List.mem_cons, not_or] using
      And.intro hne (hfresh other (by simp [hother]))

/-- Retain the result only when its entire proposed oracle trace can be installed. -/
def programOracleView {Query Reply Value : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (view : Value × List (Query × Reply)) :
    Option (Value × OracleCache Query Reply) :=
  (programOracleTrace cache view.2).map (Prod.mk view.1)

/-- Independent query replies, retaining every query and its answer in chronological order. -/
noncomputable def freshOracleTraceLaw {Query Reply Value : Type*}
    (answerLaw : PMF Reply) : OracleComp Query Reply Value → PMF (Value × List (Query × Reply))
  | .pure value => PMF.pure (value, [])
  | .query query next => answerLaw.bind fun reply =>
    (freshOracleTraceLaw answerLaw (next reply)).map (fun view => (view.1, (query, reply) :: view.2))

/-- Forgetting the recorded trace gives the existing independent-answer oracle semantics. -/
theorem freshOracleTraceLaw_result {Query Reply Value : Type*}
    (answerLaw : PMF Reply) (comp : OracleComp Query Reply Value) :
    (freshOracleTraceLaw answerLaw comp).map Prod.fst = comp.runFreshPMF answerLaw := by
  induction comp with
  | pure value => exact PMF.pure_map _ _
  | query query next ih =>
    simp only [freshOracleTraceLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, OracleComp.runFreshPMF]
    exact congrArg (PMF.bind answerLaw) (funext ih)

/-- Run the independent-answer tree on a fixed tape and record its chronological query trace. -/
def freshOracleRunTape {Query Reply Value : Type*} :
    (budget : ℕ) → OracleComp Query Reply Value → (Fin budget → Reply) →
      Option (Value × List (Query × Reply))
  | _, .pure value, _ => some (value, [])
  | 0, .query _ _, _ => none
  | budget + 1, .query query next, tape =>
    (freshOracleRunTape budget (next (tape 0)) (Fin.tail tape)).map
      (fun view => (view.1, (query, tape 0) :: view.2))

/-- A bounded independent-answer execution cannot exhaust its assigned tape. -/
theorem freshOracleRunTape_ne_none {Query Reply Value : Type*}
    {comp : OracleComp Query Reply Value} {budget : ℕ} (h : comp.QueryBound budget)
    (tape : Fin budget → Reply) : freshOracleRunTape budget comp tape ≠ none := by
  induction h with
  | pure value budget => simp [freshOracleRunTape]
  | query h ih =>
    simpa only [freshOracleRunTape, ne_eq, Option.map_eq_none_iff] using ih (tape 0) (Fin.tail tape)

/-- The independent tape implements exactly the recorded fresh-answer distribution. -/
theorem freshOracleRunTape_law {Query Reply Value : Type*}
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (h : comp.QueryBound budget) :
    (independentTapeLaw answerLaw budget).map (freshOracleRunTape budget comp) =
      (freshOracleTraceLaw answerLaw comp).map some := by
  induction h with
  | pure value budget =>
    have hconstant : freshOracleRunTape budget (OracleComp.pure value : OracleComp Query Reply Value) =
        fun _ => some (value, []) := by
      funext tape
      cases budget <;> rfl
    rw [hconstant]
    simp only [freshOracleTraceLaw, PMF.pure_map]
    exact PMF.map_const _ _
  | @query query next budget h ih =>
    simp only [independentTapeLaw, PMF.map_bind, PMF.map_comp, Function.comp_def,
      freshOracleRunTape, Fin.cons_zero, Fin.tail_cons, freshOracleTraceLaw]
    congr 1
    funext reply
    have hmap := congrArg (PMF.map (Option.map (fun view : Value × List (Query × Reply) =>
      (view.1, (query, reply) :: view.2)))) (ih reply)
    simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using hmap

/-- The real cached run equals independent replay followed by programming whenever programming succeeds. -/
theorem cachedOracleRunTape_eq_programmed {Query Reply Value : Type*} [DecidableEq Query]
    (budget : ℕ) (comp : OracleComp Query Reply Value) (cache : OracleCache Query Reply)
    (tape : Fin budget → Reply)
    (hgood : (freshOracleRunTape budget comp tape).bind (programOracleView cache) ≠ none) :
    cachedOracleRunTape budget comp cache tape =
      (freshOracleRunTape budget comp tape).bind (programOracleView cache) := by
  induction budget generalizing comp cache with
  | zero =>
    cases comp with
    | pure value => rfl
    | query query next => simp [freshOracleRunTape] at hgood
  | succ budget ih =>
    cases comp with
    | pure value => rfl
    | query query next =>
      cases hrun : freshOracleRunTape budget (next (tape 0)) (Fin.tail tape) with
      | none => simp [freshOracleRunTape, hrun] at hgood
      | some view =>
        cases hlookup : oracleCacheLookup cache query with
        | some reply => simp [freshOracleRunTape, hrun, programOracleView, programOracleTrace, hlookup] at hgood
        | none =>
          have hrest : programOracleView ((query, tape 0) :: cache) view ≠ none := by
            simpa only [freshOracleRunTape, hrun, Option.map_some, Option.bind_some,
              programOracleView, programOracleTrace, hlookup] using hgood
          have h := ih (next (tape 0)) ((query, tape 0) :: cache) (Fin.tail tape)
            (by simpa only [hrun, Option.bind_some] using hrest)
          simpa only [cachedOracleRunTape, hlookup, freshOracleRunTape, hrun, Option.map_some,
            Option.bind_some, programOracleView, programOracleTrace] using h

end Zcash.Snark.ZeroKnowledge
