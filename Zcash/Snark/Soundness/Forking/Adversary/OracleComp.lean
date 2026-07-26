import Zcash.Snark.Soundness.Forking.Rewind

/-!
# The oracle-querying Fiat–Shamir adversary

Model a `Q`-query adversary as an adaptive query tree with eager whole-table semantics. Query
histories support replay and reprogramming; blind escape sets give the adaptive query loss.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- An adaptive computation with one oracle `T → F`: either a result or a query whose continuation
receives the answer. -/
inductive OracleComp (T F α : Type*) where
  | pure (a : α)
  | query (t : T) (k : F → OracleComp T F α)

namespace OracleComp

variable {T F α : Type*}

/-- Run the machine against an oracle table `O`, answering each query by lookup (the eager/whole-table
semantics: drawing `O` uniformly makes every fresh answer uniform). -/
def run : OracleComp T F α → (T → F) → α
  | .pure a, _ => a
  | .query t k, O => (k (O t)).run O

@[simp] theorem run_pure (a : α) (O : T → F) : (pure a : OracleComp T F α).run O = a := rfl

@[simp] theorem run_query (t : T) (k : F → OracleComp T F α) (O : T → F) :
    (query t k).run O = (k (O t)).run O := rfl

/-- The query log of a run: the points the machine asks, in order, on the path the table induces. -/
def queries : OracleComp T F α → (T → F) → List T
  | .pure _, _ => []
  | .query t k, O => t :: (k (O t)).queries O

/-- The machine makes at most `Q` queries on every path (VCVio's structural `IsQueryBound`). The
forking reduction charges its query loss against this `Q`. -/
inductive QueryBound : OracleComp T F α → ℕ → Prop
  | pure (a : α) (Q : ℕ) : QueryBound (.pure a) Q
  | query {t : T} {k : F → OracleComp T F α} {Q : ℕ}
      (h : ∀ u, QueryBound (k u) Q) : QueryBound (.query t k) (Q + 1)

/-- A query bound is monotone: a machine within budget `Q` is within any larger budget. -/
theorem QueryBound.mono {A : OracleComp T F α} {Q Q' : ℕ} (h : QueryBound A Q) (hle : Q ≤ Q') :
    QueryBound A Q' := by
  induction h generalizing Q' with
  | pure a _ => exact .pure a Q'
  | query _ ih =>
      obtain ⟨Q'', rfl⟩ : ∃ Q'', Q' = Q'' + 1 := ⟨Q' - 1, by omega⟩
      exact .query fun u => ih u (by omega)

/-- A `Q`-bounded machine's query log has length at most `Q`, on every table. -/
theorem queries_length_le {A : OracleComp T F α} {Q : ℕ} (h : QueryBound A Q) (O : T → F) :
    (A.queries O).length ≤ Q := by
  induction h with
  | pure => exact Nat.zero_le _
  | query h ih => simpa [queries] using Nat.succ_le_succ (ih _)

/-- The ordered query–answer history of a run. -/
def history : OracleComp T F α → (T → F) → List (T × F)
  | .pure _, _ => []
  | .query t k, O => (t, O t) :: (k (O t)).history O

@[simp] theorem history_pure (a : α) (O : T → F) :
    (pure a : OracleComp T F α).history O = [] := rfl

@[simp] theorem history_query (t : T) (k : F → OracleComp T F α) (O : T → F) :
    (query t k).history O = (t, O t) :: (k (O t)).history O := rfl

/-- The query log is the history's points. -/
theorem queries_eq_map_fst_history (A : OracleComp T F α) (O : T → F) :
    A.queries O = (A.history O).map Prod.fst := by
  induction A with
  | pure a => rfl
  | query t k ih => simp [queries, ih (O t)]

/-- Every recorded answer is the table's. -/
theorem history_mem_answer (A : OracleComp T F α) (O : T → F) :
    ∀ p ∈ A.history O, O p.1 = p.2 := by
  induction A with
  | pure a => intro p hp; simp at hp
  | query t k ih =>
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; rfl
      · exact ih (O t) p hp

/-- A table agreeing with the first `i` recorded answers reproduces those steps. -/
theorem history_take_replay (A : OracleComp T F α) (O O' : T → F) (i : ℕ)
    (h : ∀ p ∈ (A.history O).take i, O' p.1 = p.2) :
    (A.history O').take i = (A.history O).take i := by
  induction A generalizing i with
  | pure a => rfl
  | query t k ih =>
      cases i with
      | zero => rfl
      | succ j =>
          have ht : O' t = O t := h (t, O t) (by simp)
          simp only [history_query, List.take_succ_cons, ht]
          congr 1
          exact ih (O t) j fun p hp => h p (by simp [hp])

/-- Two runs share their first `i` steps exactly when the second table agrees with those recorded
answers. -/
theorem history_take_eq_iff (A : OracleComp T F α) (O O' : T → F) (i : ℕ) :
    (A.history O').take i = (A.history O).take i
      ↔ ∀ p ∈ (A.history O).take i, O' p.1 = p.2 := by
  constructor
  · intro heq p hp
    rw [← heq] at hp
    exact history_mem_answer A O' p (List.mem_of_mem_take hp)
  · exact history_take_replay A O O' i

/-- Shared history determines the next query point: two runs agreeing on their first `i` steps ask
the same `i`-th question (the answers may then diverge — the fork). -/
theorem history_getElem_fst_congr (A : OracleComp T F α) (O O' : T → F) (i : ℕ)
    (h : (A.history O').take i = (A.history O).take i) :
    ((A.history O')[i]?).map Prod.fst = ((A.history O)[i]?).map Prod.fst := by
  induction A generalizing i with
  | pure a => rfl
  | query t k ih =>
      cases i with
      | zero => rfl
      | succ j =>
          simp only [history_query, List.take_succ_cons, List.cons.injEq] at h
          have ht : O' t = O t := congrArg Prod.snd h.1
          simp only [history_query, List.getElem?_cons_succ, ht]
          exact ih (O t) j (ht ▸ h.2)

/-- Some query answer lies in a table-dependent escape set that is blind at that query point. -/
def escapesDuringC (esc : T → (T → F) → Set F) : OracleComp T F α → (T → F) → Prop
  | .pure _, _ => False
  | .query t k, O => O t ∈ esc t O ∨ (k (O t)).escapesDuringC esc O

/-- The machine avoids cached points and makes no repeated query on a path. -/
inductive AvoidsCache [DecidableEq T] : List (T × F) → OracleComp T F α → Prop
  | pure (c : List (T × F)) (a : α) : AvoidsCache c (.pure a)
  | query {c : List (T × F)} {t : T} {k : F → OracleComp T F α}
      (ht : t ∉ c.map Prod.fst) (h : ∀ u, AvoidsCache ((t, u) :: c) (k u)) :
      AvoidsCache c (.query t k)

/-- Answer cached queries locally and issue each fresh query once. -/
def dedup [DecidableEq T] (c : List (T × F)) : OracleComp T F α → OracleComp T F α
  | .pure a => .pure a
  | .query t k =>
      match (c.find? (fun p => p.1 = t)) with
      | some p => dedup c (k p.2)
      | none => .query t (fun u => dedup ((t, u) :: c) (k u))

theorem dedup_avoidsCache [DecidableEq T] (c : List (T × F)) (A : OracleComp T F α) :
    AvoidsCache c (dedup c A) := by
  induction A generalizing c with
  | pure a => exact .pure c a
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact ih p.2 c
      | none =>
          refine .query ?_ (fun u => ih u ((t, u) :: c))
          intro hmem
          obtain ⟨p, hp, hpt⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hfind p hp
          simp [hpt] at this

theorem dedup_queryBound [DecidableEq T] {A : OracleComp T F α} {Q : ℕ}
    (h : A.QueryBound Q) (c : List (T × F)) : (dedup c A).QueryBound Q := by
  induction h generalizing c with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact (ih p.2 c).mono (Nat.le_succ Q)
      | none => exact .query (fun u => ih u ((t, u) :: c))

/-- Deduplication preserves escapes when the cache is table-consistent and contains no escaping
answer. -/
theorem escapesDuringC_dedup [DecidableEq T] (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {O : T → F} {c : List (T × F)}
    (hcon : ∀ p ∈ c, O p.1 = p.2) (hesc : ∀ p ∈ c, O p.1 ∉ esc p.1 O)
    (h : A.escapesDuringC esc O) : (dedup c A).escapesDuringC esc O := by
  induction A generalizing c with
  | pure a => exact h
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p =>
          have hp := List.find?_some hfind
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t := by simpa using hp
          subst hpt
          have hval : O p.1 = p.2 := hcon p hpmem
          rcases h with h | h
          · exact absurd h (hesc p hpmem)
          · show (dedup c (k p.2)).escapesDuringC esc O
            rw [← hval]
            exact ih (O p.1) hcon hesc h
      | none =>
          by_cases hOt : O t ∈ esc t O
          · exact Or.inl hOt
          · rcases h with h | h
            · exact absurd h hOt
            · refine Or.inr (ih (O t) ?_ ?_ h)
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; rfl
                · exact hcon p hp
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; exact hOt
                · exact hesc p hp


variable {β : Type*}

/-- Sequence two machines: run the first, feed its result to the second. -/
def bind : OracleComp T F α → (α → OracleComp T F β) → OracleComp T F β
  | .pure a, f => f a
  | .query t k, f => .query t (fun u => (k u).bind f)

@[simp] theorem run_bind (A : OracleComp T F α) (f : α → OracleComp T F β) (O : T → F) :
    (A.bind f).run O = ((f (A.run O)).run O) := by
  induction A with
  | pure a => rfl
  | query t k ih => exact ih (O t)

/-- Query a list of points in order, ignoring the answers, and return `p`. -/
def queryList (p : α) : List T → OracleComp T F α
  | [] => .pure p
  | t :: ts => .query t (fun _ => queryList p ts)

@[simp] theorem run_queryList (p : α) (ts : List T) (O : T → F) :
    (queryList p ts).run O = p := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem queryBound_bind {A : OracleComp T F α} {f : α → OracleComp T F β} {Q Q' : ℕ}
    (hA : A.QueryBound Q) (hf : ∀ a, (f a).QueryBound Q') : (A.bind f).QueryBound (Q + Q') := by
  induction hA with
  | pure a Q => exact (hf a).mono (Nat.le_add_left _ _)
  | @query t k Q h ih =>
      have : (OracleComp.query t k).bind f = .query t (fun u => (k u).bind f) := rfl
      rw [this, Nat.succ_add]
      exact .query fun u => ih u

theorem queryBound_queryList (p : α) (ts : List T) :
    (queryList (F := F) p ts).QueryBound ts.length := by
  induction ts with
  | nil => exact .pure p 0
  | cons t ts ih => exact .query fun _ => ih

/-- An escape inside the second machine is an escape of the sequence. -/
theorem escapesDuringC_bind_right (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {f : α → OracleComp T F β} {O : T → F}
    (h : (f (A.run O)).escapesDuringC esc O) : (A.bind f).escapesDuringC esc O := by
  induction A with
  | pure a => exact h
  | query t k ih => exact Or.inr (ih (O t) h)

/-- An escaping answer at some listed point is an escape of the listing run. -/
theorem escapesDuringC_queryList (esc : T → (T → F) → Set F) (p : α) {ts : List T} {O : T → F}
    {t : T} (ht : t ∈ ts) (h : O t ∈ esc t O) : (queryList p ts).escapesDuringC esc O := by
  induction ts with
  | nil => exact absurd ht (List.not_mem_nil)
  | cons t' ts ih =>
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact Or.inl h
      · exact Or.inr (ih hmem)

/-- Run a machine, query every round prefix of its output, and return that output unchanged. -/
def completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T) (A : OracleComp T F P) :
    OracleComp T F P :=
  A.bind fun p => queryList p (List.ofFn (prefixes p))

@[simp] theorem run_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    (A : OracleComp T F P) (O : T → F) : (A.completing prefixes).run O = A.run O := by
  rw [completing, run_bind, run_queryList]

theorem queryBound_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    {A : OracleComp T F P} {Q : ℕ} (hA : A.QueryBound Q) :
    (A.completing prefixes).QueryBound (Q + k) := by
  refine queryBound_bind hA fun p => ?_
  have h := queryBound_queryList (F := F) p (List.ofFn (prefixes p))
  rwa [List.length_ofFn] at h

/-- An escaping answer at one of the output's own prefixes is an escape of the completed run. -/
theorem escapesDuringC_completing (esc : T → (T → F) → Set F) {P : Type*} {k : ℕ}
    (prefixes : P → Fin k → T) {A : OracleComp T F P} {O : T → F} {j : Fin k}
    (h : O (prefixes (A.run O) j) ∈ esc (prefixes (A.run O) j) O) :
    (A.completing prefixes).escapesDuringC esc O :=
  escapesDuringC_bind_right esc
    (escapesDuringC_queryList esc _ (by exact List.mem_ofFn.mpr ⟨j, rfl⟩) h)

/-- Sequencing concatenates the query logs. -/
theorem queries_bind (A : OracleComp T F α) (f : α → OracleComp T F β) (O : T → F) :
    (A.bind f).queries O = A.queries O ++ (f (A.run O)).queries O := by
  induction A with
  | pure a => rfl
  | query t k ih =>
      show t :: ((k (O t)).bind f).queries O
          = (t :: (k (O t)).queries O) ++ (f ((OracleComp.query t k).run O)).queries O
      rw [run_query, List.cons_append, ih (O t)]

/-- A list-query pass queries exactly its list. -/
theorem queries_queryList (p : α) (ts : List T) (O : T → F) :
    (queryList (F := F) p ts).queries O = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      show t :: _ = _
      rw [ih]

/-- The completed run queries every one of the output's own round prefixes. -/
theorem mem_queries_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    (A : OracleComp T F P) (O : T → F) (j : Fin k) :
    prefixes (A.run O) j ∈ (A.completing prefixes).queries O := by
  rw [completing, queries_bind, List.mem_append]
  right
  rw [queries_queryList]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩


/-- Fix the junk table and retain only queries to the game domain. -/
def restrictSum {J : Type*} (j : J → F) : OracleComp (T ⊕ J) F α → OracleComp T F α
  | .pure a => .pure a
  | .query (Sum.inl t) k => .query t (fun u => restrictSum j (k u))
  | .query (Sum.inr x) k => restrictSum j (k (j x))

/-- The restriction's run against `O` is the original run against `O` with the junk table glued
on. -/
theorem run_restrictSum {J : Type*} (j : J → F) :
    (A : OracleComp (T ⊕ J) F α) → (O : T → F) →
    (restrictSum j A).run O = A.run (Sum.elim O j)
  | .pure _, _ => rfl
  | .query (Sum.inl t) k, O => run_restrictSum j (k (O t)) O
  | .query (Sum.inr x) k, O => run_restrictSum j (k (j x)) O

/-- Restriction never adds queries: the junk answers are read from the fixed table for free. -/
theorem queryBound_restrictSum {J : Type*} {A : OracleComp (T ⊕ J) F α} {Q : ℕ}
    (h : A.QueryBound Q) (j : J → F) : (restrictSum j A).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      cases t with
      | inl t => exact .query fun u => ih u
      | inr x => exact (ih (j x)).mono (Nat.le_succ Q)

/-- A cache-avoiding run queries distinct points, none already cached. -/
theorem AvoidsCache.run_queries_nodup [DecidableEq T] :
    {c : List (T × F)} → {A : OracleComp T F α} → AvoidsCache c A → (O : T → F) →
    (A.queries O).Nodup ∧ ∀ p ∈ c, p.1 ∉ A.queries O
  | _, _, .pure c a, O => ⟨by simp [queries], by intro p _; simp [queries]⟩
  | c, _, .query (t := t) (k := k) ht h, O => by
      obtain ⟨hnd, hdis⟩ := (h (O t)).run_queries_nodup O
      have htnotin : t ∉ (k (O t)).queries O := hdis ⟨t, O t⟩ (List.mem_cons_self ..)
      refine ⟨?_, ?_⟩
      · rw [queries]
        exact List.nodup_cons.mpr ⟨htnotin, hnd⟩
      · intro p hp
        rw [queries, List.mem_cons]
        push Not
        refine ⟨fun hpt => ?_, ?_⟩
        · exact absurd (hpt ▸ List.mem_map_of_mem (f := Prod.fst) hp) ht
        · exact hdis p (List.mem_cons_of_mem _ hp)

/-- Reprogramming a cache-avoiding run at query `i` preserves its earlier history and supplies the
new answer at `i`. -/
theorem reprogram_replay_fork [DecidableEq T] {A : OracleComp T F α}
    (hac : A.AvoidsCache []) (O : T → F) {i : ℕ} (hi : i < (A.history O).length) (u : F) :
    ((A.history (Function.update O ((A.history O)[i].1) u)).take i = (A.history O).take i)
      ∧ (A.history (Function.update O ((A.history O)[i].1) u))[i]?
          = some ((A.history O)[i].1, u) := by
  set t := (A.history O)[i].1 with ht
  set O' := Function.update O t u with hO'
  have hnd : ((A.history O).map Prod.fst).Nodup := by
    have h := (hac.run_queries_nodup O).1
    rwa [queries_eq_map_fst_history] at h
  have hagree : ∀ p ∈ (A.history O).take i, O' p.1 = p.2 := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
    rw [List.length_take] at hj
    have hji : j < i := lt_of_lt_of_le hj (min_le_left _ _)
    have hjlen : j < (A.history O).length := lt_of_lt_of_le hji hi.le
    have hpoint : p.1 = (A.history O)[j].1 := by
      rw [← hpj, List.getElem_take]
    have hne : p.1 ≠ t := by
      rw [hpoint, ht]
      intro heq
      have hmap : ((A.history O).map Prod.fst)[j]'(by rw [List.length_map]; exact hjlen)
          = ((A.history O).map Prod.fst)[i]'(by rw [List.length_map]; exact hi) := by
        rw [List.getElem_map, List.getElem_map]; exact heq
      exact absurd (hnd.getElem_inj_iff.mp hmap) (by omega)
    have hval : p.2 = O p.1 := (A.history_mem_answer O p (List.mem_of_mem_take hp)).symm
    rw [hO', Function.update_apply, if_neg hne, hval]
  have htake : (A.history O').take i = (A.history O).take i := A.history_take_replay O O' i hagree
  refine ⟨htake, ?_⟩
  have hpt : ((A.history O')[i]?).map Prod.fst = ((A.history O)[i]?).map Prod.fst :=
    A.history_getElem_fst_congr O O' i htake
  have hrhs : ((A.history O)[i]?).map Prod.fst = some t := by
    rw [List.getElem?_eq_getElem hi]; rfl
  rw [hrhs] at hpt
  obtain ⟨q, hq⟩ : ∃ q, (A.history O')[i]? = some q := by
    cases hc : (A.history O')[i]? with
    | none => rw [hc] at hpt; simp at hpt
    | some q => exact ⟨q, rfl⟩
  rw [hq] at hpt ⊢
  rw [Option.map_some] at hpt
  have hq1 : q.1 = t := Option.some.inj hpt
  have hqmem : q ∈ A.history O' := List.mem_of_getElem? hq
  have hans : O' q.1 = q.2 := A.history_mem_answer O' q hqmem
  rw [hq1, hO', Function.update_self] at hans
  rw [Option.some.injEq, Prod.ext_iff]
  exact ⟨hq1, hans.symm⟩


/-- The first query index of the output's fork point. -/
def forkIdx [DecidableEq T] (A : OracleComp T F α) (fp : α → T) (O : T → F) : ℕ :=
  (A.queries O).idxOf (fp (A.run O))

theorem forkIdx_lt [DecidableEq T] {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    (fp : α → T) {O : T → F} (hmem : fp (A.run O) ∈ A.queries O) :
    forkIdx A fp O < Q :=
  lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hmem) (A.queries_length_le hQ O)

/-- Partition winning tables by their fork index among the first `Q` queries. -/
theorem card_win_eq_sum_forkIdx [Fintype T] [DecidableEq T] [Fintype F] [DecidableEq F]
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) (fp : α → T)
    (win : (T → F) → Prop) [DecidablePred win]
    (hquery : ∀ O, win O → fp (A.run O) ∈ A.queries O) :
    (Finset.univ.filter win).card
      = ∑ i ∈ Finset.range Q,
          (Finset.univ.filter (fun O => win O ∧ forkIdx A fp O = i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun O => forkIdx A fp O) (t := Finset.range Q) ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_filter]
  · intro O hO
    exact Finset.mem_range.mpr (forkIdx_lt hQ fp (hquery O (Finset.mem_filter.mp hO).2))

end OracleComp

/-! ## Overridden tables

Conditioned answers are represented as point-value overrides on an otherwise uniform table. -/

variable {T F : Type*} [DecidableEq T]

/-- Apply a list of point-value overrides to a table, later entries winning. -/
def applyUpdates (σ : List (T × F)) (O : T → F) : T → F :=
  σ.foldl (fun g p => Function.update g p.1 p.2) O

@[simp] theorem applyUpdates_nil (O : T → F) : applyUpdates ([] : List (T × F)) O = O := rfl

theorem applyUpdates_cons (p : T × F) (σ : List (T × F)) (O : T → F) :
    applyUpdates (p :: σ) O = applyUpdates σ (Function.update O p.1 p.2) := rfl

/-- Off the override domain, the table shows through. -/
theorem applyUpdates_apply_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) : applyUpdates σ O t = O t := by
  induction σ generalizing O with
  | nil => rfl
  | cons p σ ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [applyUpdates_cons, ih h.2, Function.update_apply, if_neg h.1]

/-- On the override domain, the value does not depend on the underlying table. -/
theorem applyUpdates_apply_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O O' : T → F) : applyUpdates σ O t = applyUpdates σ O' t := by
  induction σ generalizing O O' with
  | nil => simp at h
  | cons p σ ih =>
      by_cases hmem : t ∈ σ.map Prod.fst
      · exact ih hmem _ _
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h
          rw [applyUpdates_cons, applyUpdates_cons, applyUpdates_apply_not_mem hmem,
            applyUpdates_apply_not_mem hmem, Function.update_self, Function.update_self]
        · exact absurd h hmem

/-- Off the override domain, overriding the underlying table commutes with the record. -/
theorem applyUpdates_update_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = Function.update (applyUpdates σ O) t v := by
  funext j
  by_cases hj : j = t
  · subst hj
    rw [applyUpdates_apply_not_mem h, Function.update_self, Function.update_self]
  · by_cases hdom : j ∈ σ.map Prod.fst
    · rw [Function.update_apply, if_neg hj, applyUpdates_apply_of_mem hdom]
    · simp [applyUpdates_apply_not_mem hdom, hj]

/-- Overriding the table at an already-overridden point changes nothing. -/
theorem applyUpdates_update_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = applyUpdates σ O := by
  induction σ generalizing O with
  | nil => simp at h
  | cons p σ ih =>
      rw [applyUpdates_cons, applyUpdates_cons]
      by_cases hp : t = p.1
      · subst hp
        rw [Function.update_idem]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hp
        · rw [Function.update_comm hp]
          exact ih h _

/-- A `Q`-query cache-avoiding machine enters table-dependent blind escape sets of measure `ε` with
probability at most `Q · ε`. -/
theorem escapesDuringC_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc (applyUpdates σ O)} ≤ Q * ε := by
  induction hQ generalizing σ with
  | pure a Q' =>
      have hempty : {O : T → F | (OracleComp.pure a : OracleComp T F α).escapesDuringC esc
          (applyUpdates σ O)} = ∅ := by
        ext O; simp [OracleComp.escapesDuringC]
      rw [hempty]
      simp
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsub : {O : T → F | (OracleComp.query t k).escapesDuringC esc (applyUpdates σ O)}
          ⊆ {O : T → F | O t ∈ esc t (applyUpdates σ O)} ∪ ⋃ u : F, {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}} := by
        intro O hO
        simp only [OracleComp.escapesDuringC, Set.mem_setOf_eq, happ O] at hO
        rcases hO with h1 | h2
        · exact Or.inl h1
        · refine Or.inr (Set.mem_iUnion.mpr ⟨O t, rfl, ?_⟩)
          have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
            rw [applyUpdates_cons, Function.update_eq_self]
          simp only [Set.mem_setOf_eq, hcons]
          exact h2
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (MeasureTheory.measure_union_le _ _) ?_
      have hfirst : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          {O : T → F | O t ∈ esc t (applyUpdates σ O)} ≤ ε := by
        refine uniformOfFintype_point_mem_blind_le t (fun O => esc t (applyUpdates σ O))
          (fun O v => ?_) (fun O => hesc t _)
        beta_reduce
        rw [applyUpdates_update_not_mem ht, hblind]
      have hsecond : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          (⋃ u : F, {O : T → F | O t = u ∧
            O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}})
          ≤ Q * ε := by
        refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
        rw [tsum_fintype]
        have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}}
            ≤ (Q * ε) / Fintype.card F := by
          intro u
          have hblindE : ∀ (O : T → F) (v : F),
              Function.update O t v ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}
              ↔ O ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')} := by
            intro O v
            have hcons : applyUpdates ((t, u) :: σ) (Function.update O t v)
                = applyUpdates ((t, u) :: σ) O := by
              rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
            simp only [Set.mem_setOf_eq, hcons]
          rw [uniformOfFintype_cond_point t u _ hblindE]
          exact ENNReal.div_le_div_right (ih u (hk u)) _
        refine le_trans (Finset.sum_le_sum fun u _ => hper u) ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
          ENNReal.div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      calc (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t ∈ esc t (applyUpdates σ O)}
            + (PMF.uniformOfFintype (T → F)).toOuterMeasure (⋃ u : F, _)
          ≤ ε + Q * ε := add_le_add hfirst hsecond
        _ = (Q + 1) * ε := by ring
        _ = ((Q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

/-- The conditional escape bound for an arbitrary machine: deduplicate
(`OracleComp.escapesDuringC_dedup`), then apply the fresh-query bound. -/
theorem escapesDuringC_measure_le' {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc O} ≤ Q * ε := by
  have hsub : {O : T → F | A.escapesDuringC esc O}
      ⊆ {O : T → F | (OracleComp.dedup [] A).escapesDuringC esc
          (applyUpdates ([] : List (T × F)) O)} := by
    intro O hO
    simp only [Set.mem_setOf_eq, applyUpdates_nil]
    exact OracleComp.escapesDuringC_dedup esc (by simp) (by simp) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact escapesDuringC_measure_le esc hblind hesc (OracleComp.dedup_queryBound hQ [])
    (OracleComp.dedup_avoidsCache [] A)

/-! ## Weighted query charges

Bound natural-number query charges by the query budget for AFK accounting. -/

/-- Accumulate a per-query charge along the run: each query `t` contributes `v t O (O t)`. -/
def queryCharge {T F α : Type*} (v : T → (T → F) → F → ℕ) :
    OracleComp T F α → (T → F) → ℕ
  | .pure _, _ => 0
  | .query t k, O => v t O (O t) + queryCharge v (k (O t)) O

/-- Fibering a table sum over one coordinate's value. -/
theorem sum_table_fiberwise {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ) :
    ∑ O : T → F, g O
      = ∑ u : F, ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O := by
  calc ∑ O : T → F, g O = ∑ O : T → F, ∑ u : F, if O t = u then g O else 0 := by
        refine Finset.sum_congr rfl fun O _ => ?_
        simp
    _ = ∑ u : F, ∑ O : T → F, if O t = u then g O else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun u _ => (Finset.sum_filter _ _).symm

/-- A coordinate-blind summand makes every fiber of that coordinate the same size. -/
theorem sum_table_fiber_blind {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ)
    (hblind : ∀ (O : T → F) (v : F), g (Function.update O t v) = g O) (u u' : F) :
    ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O
      = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u'), g O := by
  refine Finset.sum_nbij' (fun O => Function.update O t u') (fun O => Function.update O t u)
    (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_)
  · simp
  · simp
  · dsimp only
    rw [Function.update_idem, ← (Finset.mem_filter.mp hO).2, Function.update_eq_self]
  · dsimp only
    rw [Function.update_idem, ← (Finset.mem_filter.mp hO).2, Function.update_eq_self]
  · exact (hblind O u').symm

/-- Summing a coordinate-blind summand over one fiber recovers the full sum after scaling by the
field size. -/
theorem sum_table_fiber_mul_card {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ)
    (hblind : ∀ (O : T → F) (v : F), g (Function.update O t v) = g O) (u : F) :
    (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O) * Fintype.card F
      = ∑ O : T → F, g O := by
  rw [sum_table_fiberwise t g,
    Finset.sum_congr rfl fun u' _ => sum_table_fiber_blind t g hblind u' u,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- A `Q`-query machine's total blind charge is at most `Q` times its average per-point budget,
stated after clearing the factor `|F|`.  The budget must hold uniformly over every override
context `σ'`, not just the ambient one; `queryCharge_sum_mul_le_table_budget` trades this for a
pointwise table-indexed budget. -/
theorem queryCharge_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (∑ O : T → F, queryCharge v A (applyUpdates σ O)) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  induction hQ generalizing σ with
  | pure a Q' => simp [queryCharge]
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsplit : ∀ O : T → F,
          queryCharge v (OracleComp.query t k) (applyUpdates σ O)
            = v t (applyUpdates σ O) (O t)
              + queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O) := by
        intro O
        have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
          rw [applyUpdates_cons, Function.update_eq_self]
        rw [queryCharge, happ O, hcons]
      rw [Finset.sum_congr rfl fun O _ => hsplit O, Finset.sum_add_distrib, Nat.add_mul,
        show (Q + 1) * M * Fintype.card (T → F)
          = M * Fintype.card (T → F) + Q * M * Fintype.card (T → F) by ring]
      refine Nat.add_le_add ?_ ?_
      · -- one query pays its answer-averaged budget
        have hb : ∀ (x : F) (O : T → F) (y : F),
            v t (applyUpdates σ (Function.update O t y)) x = v t (applyUpdates σ O) x := by
          intro x O y
          rw [applyUpdates_update_not_mem ht, hblind]
        calc (∑ O : T → F, v t (applyUpdates σ O) (O t)) * Fintype.card F
            = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) (O t)) * Fintype.card F := by
              rw [sum_table_fiberwise t, Finset.sum_mul]
          _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) u) * Fintype.card F := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              exact Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]
          _ = ∑ u : F, ∑ O : T → F, v t (applyUpdates σ O) u :=
              Finset.sum_congr rfl fun u _ => sum_table_fiber_mul_card t _ (hb u) u
          _ = ∑ O : T → F, ∑ u : F, v t (applyUpdates σ O) u := Finset.sum_comm
          _ ≤ M * Fintype.card (T → F) := hbudget t σ
      · -- the continuation recurses conditionally on the answer
        have hbk : ∀ (u : F) (O : T → F) (y : F),
            queryCharge v (k u) (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hfiber : (∑ O : T → F,
            queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F
            = ∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          rw [sum_table_fiberwise t, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [show (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O))
              = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) from
            Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]]
          exact sum_table_fiber_mul_card t _ (hbk u) u
        rw [hfiber]
        refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
        calc (∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O))
              * Fintype.card F
            = ∑ u : F, (∑ O : T → F,
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ _u : F, Q * M * Fintype.card (T → F) :=
              Finset.sum_le_sum fun u _ => ih u (hk u)
          _ = Q * M * Fintype.card (T → F) * Fintype.card F := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Table-indexed query-charge bound, charging the budget sum at the original override context. -/
theorem queryCharge_sum_mul_le_table_budget {T F α : Type*} [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    (B : (T → F) → ℕ) (hB : ∀ (t : T) (O : T → F), ∑ x : F, v t O x ≤ B O)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (∑ O : T → F, queryCharge v A (applyUpdates σ O)) * Fintype.card F
      ≤ Q * ∑ O : T → F, B (applyUpdates σ O) := by
  induction hQ generalizing σ with
  | pure a Q' => simp [queryCharge]
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsplit : ∀ O : T → F,
          queryCharge v (OracleComp.query t k) (applyUpdates σ O)
            = v t (applyUpdates σ O) (O t)
              + queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O) := by
        intro O
        have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
          rw [applyUpdates_cons, Function.update_eq_self]
        rw [queryCharge, happ O, hcons]
      rw [Finset.sum_congr rfl fun O _ => hsplit O, Finset.sum_add_distrib, Nat.add_mul,
        show (Q + 1) * ∑ O : T → F, B (applyUpdates σ O)
          = (∑ O : T → F, B (applyUpdates σ O)) + Q * ∑ O : T → F, B (applyUpdates σ O)
          by ring]
      refine Nat.add_le_add ?_ ?_
      · -- one query pays the budget at the current context
        have hb : ∀ (x : F) (O : T → F) (y : F),
            v t (applyUpdates σ (Function.update O t y)) x = v t (applyUpdates σ O) x := by
          intro x O y
          rw [applyUpdates_update_not_mem ht, hblind]
        calc (∑ O : T → F, v t (applyUpdates σ O) (O t)) * Fintype.card F
            = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) (O t)) * Fintype.card F := by
              rw [sum_table_fiberwise t, Finset.sum_mul]
          _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) u) * Fintype.card F := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              exact Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]
          _ = ∑ u : F, ∑ O : T → F, v t (applyUpdates σ O) u :=
              Finset.sum_congr rfl fun u _ => sum_table_fiber_mul_card t _ (hb u) u
          _ = ∑ O : T → F, ∑ u : F, v t (applyUpdates σ O) u := Finset.sum_comm
          _ ≤ ∑ O : T → F, B (applyUpdates σ O) :=
              Finset.sum_le_sum fun O _ => hB t _
      · -- the continuation recurses conditionally; the budget fibers recombine exactly
        have hbk : ∀ (u : F) (O : T → F) (y : F),
            queryCharge v (k u) (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hBk : ∀ (u : F) (O : T → F) (y : F),
            B (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = B (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hfiber : (∑ O : T → F,
            queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F
            = ∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          rw [sum_table_fiberwise t, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [show (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O))
              = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) from
            Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]]
          exact sum_table_fiber_mul_card t _ (hbk u) u
        have hBfiber : ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O)
            = (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by
          calc ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O)
              = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                  B (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
                Finset.sum_congr rfl fun u _ => (sum_table_fiber_mul_card t _ (hBk u) u).symm
            _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                  B (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F := by
                refine Finset.sum_congr rfl fun u _ => ?_
                congr 1
                exact Finset.sum_congr rfl fun O hO => by
                  rw [(Finset.mem_filter.mp hO).2]
            _ = (∑ O : T → F, B (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F := by
                rw [sum_table_fiberwise t, Finset.sum_mul]
            _ = (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by
                congr 1
                refine Finset.sum_congr rfl fun O _ => ?_
                congr 1
                rw [applyUpdates_cons, Function.update_eq_self]
        rw [hfiber]
        refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
        calc (∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O))
              * Fintype.card F
            = ∑ u : F, (∑ O : T → F,
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ u : F, Q * ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O) :=
              Finset.sum_le_sum fun u _ => ih u (hk u)
          _ = Q * ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O) := by
              rw [Finset.mul_sum]
          _ = Q * ((∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F) := by
              rw [hBfiber]
          _ = Q * (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by ring

/-- A single query's charge is dominated by the accumulated charge of any run that makes it. -/
theorem le_queryCharge_of_mem_queries {T F α : Type*} (v : T → (T → F) → F → ℕ)
    {B : OracleComp T F α} {O : T → F} {t : T} (h : t ∈ B.queries O) :
    v t O (O t) ≤ queryCharge v B O := by
  induction B with
  | pure a => simp [OracleComp.queries] at h
  | query t' k ih =>
      simp only [OracleComp.queries, List.mem_cons] at h
      rw [queryCharge]
      rcases h with rfl | h
      · exact Nat.le_add_right _ _
      · exact le_trans (ih (O t') h) (Nat.le_add_left _ _)

/-- Deduplication preserves occurrence of a queried point not already cached. -/
theorem mem_queries_dedup {T F α : Type*} [DecidableEq T] {B : OracleComp T F α}
    {O : T → F} {t : T} {c : List (T × F)} (hc : ∀ p ∈ c, O p.1 = p.2)
    (ht : t ∉ c.map Prod.fst) (h : t ∈ B.queries O) :
    t ∈ (OracleComp.dedup c B).queries O := by
  induction B generalizing c with
  | pure a => simp [OracleComp.queries] at h
  | query t' k ih =>
      simp only [OracleComp.queries, List.mem_cons] at h
      rw [OracleComp.dedup]
      cases hfind : c.find? (fun p => p.1 = t') with
      | some p =>
          have hpc := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t' := by simpa using List.find?_some hfind
          have hval : O t' = p.2 := by rw [← hpt]; exact hc p hpc
          rcases h with rfl | h
          · exact absurd (hpt ▸ List.mem_map_of_mem hpc) ht
          · show t ∈ (OracleComp.dedup c (k p.2)).queries O
            rw [← hval]
            exact ih (O t') hc ht h
      | none =>
          simp only [OracleComp.queries, List.mem_cons]
          rcases h with rfl | h
          · exact Or.inl rfl
          · by_cases htt' : t = t'
            · exact Or.inl htt'
            · refine Or.inr (ih (O t') ?_ ?_ h)
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · rfl
                · exact hc p hp
              · simp only [List.map_cons, List.mem_cons, not_or]
                exact ⟨htt', ht⟩

/-- With pairwise-distinct override keys, the reprogrammed table shows each recorded override. -/
theorem applyUpdates_apply_mem_nodup {T F : Type*} [DecidableEq T] {σ : List (T × F)}
    (hnodup : (σ.map Prod.fst).Nodup) {p : T × F} (hp : p ∈ σ) (O : T → F) :
    applyUpdates σ O p.1 = p.2 := by
  induction σ generalizing O with
  | nil => simp at hp
  | cons q σ ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [applyUpdates_cons, applyUpdates_apply_not_mem hnodup.1, Function.update_self]
      · rw [applyUpdates_cons]
        exact ih hnodup.2 hp _

/-- Bound the charge at an adaptively selected queried point under a reprogrammed table by the
query budget times the average per-point budget. -/
theorem steeredCharge_context_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hnodup : (σ.map Prod.fst).Nodup)
    (fp : (T → F) → T)
    (hfp : ∀ O : T → F, fp O ∈ A.queries (applyUpdates σ O))
    (hfresh : ∀ O : T → F, fp O ∉ σ.map Prod.fst) :
    (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  have hle : ∀ O : T → F,
      v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))
        ≤ queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O) := fun O =>
    le_queryCharge_of_mem_queries v
      (mem_queries_dedup (fun p hp => applyUpdates_apply_mem_nodup hnodup hp O)
        (hfresh O) (hfp O))
  calc (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ (∑ O : T → F, queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O))
        * Fintype.card F :=
        Nat.mul_le_mul_right _ (Finset.sum_le_sum fun O _ => hle O)
    _ ≤ Q * M * Fintype.card (T → F) :=
        queryCharge_sum_mul_le v hblind hbudget (OracleComp.dedup_queryBound hQ σ)
          (OracleComp.dedup_avoidsCache σ A)

/-- Table-indexed form of `steeredCharge_context_sum_mul_le`. -/
theorem steeredCharge_context_sum_mul_le_table_budget {T F α : Type*} [Fintype T]
    [DecidableEq T] [Fintype F] [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    (B : (T → F) → ℕ) (hB : ∀ (t : T) (O : T → F), ∑ x : F, v t O x ≤ B O)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hnodup : (σ.map Prod.fst).Nodup)
    (fp : (T → F) → T)
    (hfp : ∀ O : T → F, fp O ∈ A.queries (applyUpdates σ O))
    (hfresh : ∀ O : T → F, fp O ∉ σ.map Prod.fst) :
    (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ Q * ∑ O : T → F, B (applyUpdates σ O) := by
  have hle : ∀ O : T → F,
      v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))
        ≤ queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O) := fun O =>
    le_queryCharge_of_mem_queries v
      (mem_queries_dedup (fun p hp => applyUpdates_apply_mem_nodup hnodup hp O)
        (hfresh O) (hfp O))
  calc (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ (∑ O : T → F, queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O))
        * Fintype.card F :=
        Nat.mul_le_mul_right _ (Finset.sum_le_sum fun O _ => hle O)
    _ ≤ Q * ∑ O : T → F, B (applyUpdates σ O) :=
        queryCharge_sum_mul_le_table_budget v hblind B hB (OracleComp.dedup_queryBound hQ σ)
          (OracleComp.dedup_avoidsCache σ A)

/-- Context-free form of `steeredCharge_context_sum_mul_le`. -/
theorem steeredCharge_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    (fp : (T → F) → T) (hfp : ∀ O : T → F, fp O ∈ A.queries O) :
    (∑ O : T → F, v (fp O) O (O (fp O))) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  have h := steeredCharge_context_sum_mul_le v hblind hbudget hQ
    (σ := []) (by simp) fp (fun O => by simpa using hfp O) (fun O => by simp)
  simpa using h


/-! ## Fiat–Shamir attack game

The adversary and verifier read one table at output-dependent round prefixes. -/

/-! ## Adaptive reads of a uniform random function

`AdSched.map_read_uniform` proves uniformity when each query point depends on earlier answers. -/

universe u v

/-- A depth-`k` adaptive query schedule: the first query point, then the remaining schedule as a
function of that query's answer. -/
def AdSched (T : Type u) (F : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | k + 1 => T × (F → AdSched T F k)

namespace AdSched

variable {T F : Type*}

/-- The points the schedule visits when its reads are `χ`. -/
def points : {k : ℕ} → AdSched T F k → (Fin k → F) → (Fin k → T)
  | 0, _, _ => Fin.elim0
  | _ + 1, s, χ => Fin.cons s.1 (points (s.2 (χ 0)) (Fin.tail χ))

/-- The schedule's reads against a table `O`. -/
def read : {k : ℕ} → AdSched T F k → (T → F) → (Fin k → F)
  | 0, _, _ => Fin.elim0
  | _ + 1, s, O => Fin.cons (O s.1) (read (s.2 (O s.1)) O)

/-- Reads match a target exactly when the table agrees at its visited points. -/
theorem read_eq_iff : {k : ℕ} → (s : AdSched T F k) → (O : T → F) → (χ : Fin k → F) →
    (s.read O = χ ↔ ∀ j, O (s.points χ j) = χ j)
  | 0, _, _, χ => ⟨fun _ j => j.elim0, fun _ => funext fun j => j.elim0⟩
  | k + 1, s, O, χ => by
      constructor
      · intro h
        have h0 : O s.1 = χ 0 := by have := congrFun h 0; rwa [read, Fin.cons_zero] at this
        have htail : (s.2 (χ 0)).read O = Fin.tail χ := by
          have := congrArg Fin.tail h
          rwa [read, Fin.tail_cons, h0] at this
        intro j
        refine Fin.cases ?_ ?_ j
        · rw [points, Fin.cons_zero]; exact h0
        · intro i
          rw [points, Fin.cons_succ]
          exact (read_eq_iff (s.2 (χ 0)) O (Fin.tail χ)).mp htail i
      · intro h
        have h0 : O s.1 = χ 0 := by have := h 0; rwa [points, Fin.cons_zero] at this
        have htail : (s.2 (χ 0)).read O = Fin.tail χ :=
          (read_eq_iff (s.2 (χ 0)) O (Fin.tail χ)).mpr fun i => by
            have := h i.succ; rwa [points, Fin.cons_succ] at this
        rw [read, h0, htail, Fin.cons_self_tail]

/-- Freshness along `χ`: the χ-determined points are pairwise distinct. -/
def Fresh {k : ℕ} (s : AdSched T F k) : Prop := ∀ χ : Fin k → F, Function.Injective (s.points χ)

/-- A fresh adaptive schedule reads a uniform table to a uniform answer vector. -/
theorem map_read_uniform [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F] {k : ℕ}
    (s : AdSched T F k) (hs : s.Fresh) :
    (PMF.uniformOfFintype (T → F)).map s.read = PMF.uniformOfFintype (Fin k → F) := by
  refine PMF.ext fun χ => ?_
  have hset : {O : T → F | s.read O = χ} = (fun O => O ∘ s.points χ) ⁻¹' {χ} := by
    ext O
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [read_eq_iff s O χ]
    exact ⟨fun h => funext fun j => h j, fun h j => congrFun h j⟩
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    show s.read ⁻¹' {χ} = {O : T → F | s.read O = χ} from rfl, hset,
    ← PMF.toOuterMeasure_map_apply, uniformOfFintype_map_precomp_injective _ (hs χ),
    PMF.toOuterMeasure_apply_singleton]

/-- Append a read whose point depends on all preceding answers. -/
def snoc : {k : ℕ} → AdSched T F k → ((Fin k → F) → T) → AdSched T F (k + 1)
  | 0, _, pt => (pt Fin.elim0, fun _ => PUnit.unit)
  | _ + 1, s, pt => (s.1, fun u => (s.2 u).snoc (fun χ => pt (Fin.cons u χ)))

/-- The reads of `s.snoc pt`: the schedule's `k` reads, then the answer at `pt` applied to them. -/
theorem read_snoc : {k : ℕ} → (s : AdSched T F k) → (pt : (Fin k → F) → T) → (O : T → F) →
    (s.snoc pt).read O = Fin.snoc (s.read O) (O (pt (s.read O)))
  | 0, _, pt, O => by
      funext j
      fin_cases j
      simp [snoc, read, Fin.snoc]
  | k + 1, s, pt, O => by
      rw [snoc, read, read_snoc (s.2 (O s.1)) _ O, read]
      exact Fin.cons_snoc_eq_snoc_cons _ _ _

/-- The points of `s.snoc pt` along `χ`: the schedule's points, then `pt` at the read prefix. -/
theorem points_snoc : {k : ℕ} → (s : AdSched T F k) → (pt : (Fin k → F) → T) → (χ : Fin (k+1) → F) →
    (s.snoc pt).points χ = Fin.snoc (s.points (Fin.init χ)) (pt (Fin.init χ))
  | 0, _, pt, χ => by
      have he : (Fin.init χ : Fin 0 → F) = Fin.elim0 := funext fun x => x.elim0
      funext j
      rw [Fin.fin_one_eq_zero j, he]
      simp [snoc, points, Fin.snoc]
  | k + 1, s, pt, χ => by
      have hit : Fin.init (Fin.tail χ) = Fin.tail (Fin.init χ) := by
        funext i; simp [Fin.init, Fin.tail]
      have h0 : (Fin.init χ) 0 = χ 0 := by simp [Fin.init, Fin.castSucc_zero]
      rw [snoc, points, points_snoc (s.2 (χ 0)) _ (Fin.tail χ), points, hit,
          show pt (Fin.cons (χ 0) (Fin.tail (Fin.init χ))) = pt (Fin.init χ) from by
            rw [← h0, Fin.cons_self_tail], h0]
      exact Fin.cons_snoc_eq_snoc_cons _ _ _

/-- Appending a pathwise-fresh point preserves schedule freshness. -/
theorem Fresh.snoc {k : ℕ} {s : AdSched T F k} (hs : s.Fresh) {pt : (Fin k → F) → T}
    (hpt : ∀ ψ : Fin k → F, pt ψ ∉ Set.range (s.points ψ)) : (s.snoc pt).Fresh := by
  intro χ
  rw [points_snoc]
  exact Fin.snoc_injective_iff.mpr ⟨hs (Fin.init χ), hpt (Fin.init χ)⟩

/-- A snoc-extended schedule's base is fresh: freshness of `s.snoc pt` restricts to `s`. -/
theorem Fresh.of_snoc [Nonempty F] {k : ℕ} {s : AdSched T F k} {pt : (Fin k → F) → T}
    (h : (s.snoc pt).Fresh) : s.Fresh := by
  intro ψ
  have hinj := h (Fin.snoc ψ (Classical.arbitrary F))
  rw [points_snoc, Fin.init_snoc] at hinj
  exact (Fin.snoc_injective_iff.mp hinj).1

end AdSched

section Game

variable {T P F : Type*} [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F] {k : ℕ}

/-- Acceptance of the adversary's output under its table-induced round challenges. -/
def fsWins (A : OracleComp T F P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) (O : T → F) : Prop :=
  accept (A.run O) (fun j => O (prefixes (A.run O) j))

/-- The adversary's advantage `ε`: the probability, over a uniformly drawn oracle table, of the
Fiat–Shamir attack event. -/
noncomputable def fsAdvantage (A : OracleComp T F P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (T → F)).toOuterMeasure {O | fsWins A accept prefixes O}

/-- A query-free adversary's advantage equals its fixed output's accept measure over uniform
challenges. -/
theorem fsAdvantage_pure (p : P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) (hinj : Function.Injective (prefixes p)) :
    fsAdvantage (.pure p) accept prefixes
      = (PMF.uniformOfFintype (Fin k → F)).toOuterMeasure {χ | accept p χ} := by
  rw [fsAdvantage, ← uniformOfFintype_map_precomp_injective (prefixes p) hinj,
    PMF.toOuterMeasure_map_apply]
  rfl

end Game

open scoped ENNReal in
open Classical in
/-- Legacy fixed-strategy wrapper: advantage above `kerr/Nᵏ` yields an IPA opening or relation. -/
noncomputable def legacy_deployed_forking_soundness_of_fixed_adversary
    {G : Type*} [AddCommGroup G]
    [Module Fp G] [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp G urs.k)
    {T : Type*} [Fintype T] [DecidableEq T] (prefixes : Fin urs.k → T)
    (hinj : Function.Injective prefixes)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hadv : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < fsAdvantage (.pure P)
            (fun P' => proverAccept P' urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w))
            (fun _ => prefixes)) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rw [fsAdvantage_pure P _ (fun _ => prefixes) hinj] at hadv
  refine legacy_deployed_forking_soundness urs b v ξ z blind aMulti aDep s P hz hb0 hP ?_
  convert hadv using 2
  ext χ
  simp

section StagedAdversary

variable {G : Type*}

/-- The adaptive query schedule of a staged strategy: append `(L,R)` and the challenge marker,
squeeze, then continue under the answer. -/
def schedOfProver : {d : ℕ} → Prover Fp G d → List (TranscriptElt Fp G) →
    AdSched (List (TranscriptElt Fp G)) Fp d
  | 0, _, _ => PUnit.unit
  | _ + 1, .node L R cont, t =>
      (t ++ [.point L, .point R, .challenge],
       fun u => schedOfProver (cont u) (t ++ [.point L, .point R, .challenge]))

/-- Each round's point extends the base by `3·(j+1)` — every squeeze absorbs a fresh point pair and
marker — so the schedule's points have strictly increasing length. -/
theorem schedOfProver_points_length : {d : ℕ} → (P : Prover Fp G d) →
    (t : List (TranscriptElt Fp G)) → (χ : Fin d → Fp) → (j : Fin d) →
    ((schedOfProver P t).points χ j).length = t.length + 3 * (j.val + 1)
  | _ + 1, .node L R cont, t, χ, j => by
      refine Fin.cases ?_ ?_ j
      · show ((schedOfProver (.node L R cont) t).points χ 0).length = _
        rw [schedOfProver, AdSched.points, Fin.cons_zero]
        simp
      · intro i
        show ((schedOfProver (.node L R cont) t).points χ i.succ).length = _
        rw [schedOfProver, AdSched.points, Fin.cons_succ,
          schedOfProver_points_length (cont (χ 0)) _ (Fin.tail χ) i]
        simp only [List.length_append, List.length_cons, List.length_nil, Fin.val_succ]
        omega

/-- Distinct round lengths make staged squeeze points pathwise distinct. -/
theorem schedOfProver_fresh {d : ℕ} (P : Prover Fp G d) (t : List (TranscriptElt Fp G)) :
    (schedOfProver P t).Fresh := by
  intro χ a c hac
  have hlen : ((schedOfProver P t).points χ a).length
      = ((schedOfProver P t).points χ c).length := congrArg List.length hac
  rw [schedOfProver_points_length P t χ a, schedOfProver_points_length P t χ c] at hlen
  exact Fin.ext (by omega)

open Classical in
/-- Legacy staged-strategy wrapper: advantage above `kerr/Nᵏ` yields an IPA opening or relation. -/
noncomputable def legacy_deployed_forking_soundness_of_staged_adversary
    [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp) (Q : Prover Fp G urs.k)
    {T : Type*} [Fintype T] [DecidableEq T] (sched : AdSched T Fp urs.k) (hfresh : sched.Fresh)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hadv : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (T → Fp)).toOuterMeasure
            {O | flatAccept Q urs.g b urs.u urs.w z
                  (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (sched.read O)}) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_deployed_forking_soundness_flat urs b v ξ z blind aMulti aDep s Q hz hb0 hP ?_
  rw [show {O : T → Fp | flatAccept Q urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (sched.read O)}
      = sched.read ⁻¹' {χ | flatAccept Q urs.g b urs.u urs.w z
          (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ} from rfl,
    ← PMF.toOuterMeasure_map_apply, AdSched.map_read_uniform sched hfresh] at hadv
  convert hadv using 2
  ext χ
  simp

end StagedAdversary

/-- Decode a staged transcript point into its round, prefix chain, and continuation predicate. -/
structure StagedDecode (T F P : Type*) (k : ℕ) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) : Type _ where
  /-- The full-vector accept predicate of the transcript's staged continuation. -/
  stateAt : T → ((Fin k → F) → Prop)
  /-- The round the transcript point sits at. -/
  roundOf : T → ℕ
  /-- The round-prefix chain through the transcript point. -/
  chainAt : T → Fin k → T
  /-- On an output's own prefixes, the decoded state is the output's accept predicate. -/
  stateAt_prefixes : ∀ p (j : Fin k), stateAt (prefixes p j) = accept p
  /-- On an output's own prefixes, the decoded round is the prefix's round. -/
  roundOf_prefixes : ∀ p (j : Fin k), roundOf (prefixes p j) = (j : ℕ)
  /-- On an output's own prefixes, the decoded chain is the output's chain. -/
  chainAt_prefixes : ∀ p (j : Fin k), chainAt (prefixes p j) = prefixes p
  /-- Chain points before a transcript point's round are distinct from it (deployed: strictly
  shorter prefixes). -/
  chainAt_ne : ∀ t (i : Fin k), (i : ℕ) < roundOf t → chainAt t i ≠ t

namespace StagedDecode

variable {T F P : Type*} [Zero F] {k : ℕ} {accept : P → (Fin k → F) → Prop}
  {prefixes : P → Fin k → T}

/-- The decode's escape sets: at each transcript point, the ladder's escape set for the decoded
state at the decoded round, over the chain's answers. -/
def esc [DecidableEq T] (D : StagedDecode T F P k accept prefixes) : T → (T → F) → Set F :=
  fun t O => ladderEscapeSet (D.stateAt t) (fun i => O (D.chainAt t i)) (D.roundOf t)

/-- The decode's escape sets are blind at their own point: the ladder reads only the rounds before
`roundOf t`, whose chain points differ from `t`. -/
theorem esc_blind [DecidableEq T] (D : StagedDecode T F P k accept prefixes)
    (t : T) (O : T → F) (v : F) : D.esc t (Function.update O t v) = D.esc t O := by
  refine ladderEscapeSet_congr _ _ _ _ (fun i hi => ?_)
  rw [Function.update_apply, if_neg (D.chainAt_ne t i hi)]

/-- The decode's escape sets sit inside three challenges. -/
theorem esc_measure_le [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) (t : T) (O : T → F) :
    (PMF.uniformOfFintype F).toOuterMeasure (D.esc t O) ≤ 3 / Fintype.card F := by
  obtain ⟨a, b, hab⟩ := ladderEscapeSet_subset_triple (D.stateAt t)
    (fun i => O (D.chainAt t i)) (D.roundOf t)
  exact uniformOfFintype_toOuterMeasure_triple_le hab

/-- A winning completed run either escapes or returns an extractable output. -/
theorem win_forces [DecidableEq T] (D : StagedDecode T F P k accept prefixes)
    {A : OracleComp T F P} {O : T → F} (hwin : fsWins A accept prefixes O) :
    (A.completing prefixes).escapesDuringC D.esc O ∨ Extractable (accept (A.run O)) := by
  rcases extractable_or_ladderEscape (accept (A.run O))
      (fun j => O (prefixes (A.run O) j)) hwin with hext | hlad
  · exact Or.inr hext
  · obtain ⟨j, hj⟩ := exists_mem_ladderEscapeSet _ _ hlad
    refine Or.inl (OracleComp.escapesDuringC_completing D.esc prefixes (j := j) ?_)
    show O (prefixes (A.run O) j) ∈ ladderEscapeSet (D.stateAt (prefixes (A.run O) j))
      (fun i => O (D.chainAt (prefixes (A.run O) j) i)) (D.roundOf (prefixes (A.run O) j))
    rw [D.stateAt_prefixes, D.roundOf_prefixes, D.chainAt_prefixes]
    exact hj

/-- A staged `Q`-query adversary with no extractable output has advantage at most
`(Q + k) · 3/|F|`. -/
theorem fsAdvantage_le [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) {A : OracleComp T F P} {Q : ℕ}
    (hQ : A.QueryBound Q)
    (hnoext : ∀ O : T → F, ¬ Extractable (accept (A.run O))) :
    fsAdvantage A accept prefixes ≤ (Q + k) * (3 / Fintype.card F) := by
  have hsub : {O : T → F | fsWins A accept prefixes O}
      ⊆ {O : T → F | (A.completing prefixes).escapesDuringC D.esc O} := by
    intro O hO
    rcases D.win_forces hO with h | h
    · exact h
    · exact absurd h (hnoext O)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have h := escapesDuringC_measure_le' D.esc D.esc_blind D.esc_measure_le
    (OracleComp.queryBound_completing prefixes hQ)
  exact_mod_cast h

/-- Advantage above `(Q+k)·3/|F|` yields an extractable output. -/
theorem extractable_of_lt_fsAdvantage [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) {A : OracleComp T F P} {Q : ℕ}
    (hQ : A.QueryBound Q)
    (h : (Q + k) * (3 / Fintype.card F) < fsAdvantage A accept prefixes) :
    ∃ O : T → F, Extractable (accept (A.run O)) := by
  by_contra hno
  push Not at hno
  exact absurd (D.fsAdvantage_le hQ hno) (not_le.mpr h)

end StagedDecode


/-- Legacy staged-adversary wrapper: advantage above `(Q + k) · 3/p` yields an IPA opening or
relation. -/
noncomputable def legacy_deployed_forking_soundness_of_adversary
    {G : Type*} [AddCommGroup G]
    [Module Fp G] [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    {T : Type*} [Fintype T] [DecidableEq T]
    (A : OracleComp T Fp (Prover Fp G urs.k)) (prefixes : Prover Fp G urs.k → Fin urs.k → T)
    (D : StagedDecode T Fp (Prover Fp G urs.k) urs.k
      (fun P χ => proverAccept P urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ) prefixes)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    {Q : ℕ} (hQ : A.QueryBound Q)
    (hadv : (Q + urs.k) * (3 / Fintype.card Fp)
        < fsAdvantage A (fun P χ => proverAccept P urs.g b urs.u urs.w z
            (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ) prefixes) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hext := D.extractable_of_lt_fsAdvantage hQ hadv
  have hpf := proverAccept_forkValid (A.run hext.choose) urs.g b
    (commit urs aDep + (z * 0) • urs.u + blind • urs.w) hext.choose_spec
  rcases deployed_forking_relation urs b v ξ z blind aMulti aDep s hpf.choose hz hb0 hP
    hpf.choose_spec with ⟨a, ha⟩ | r
  · exact PSum.inl ⟨a, ha⟩
  · exact PSum.inr r

end Zcash.Snark
