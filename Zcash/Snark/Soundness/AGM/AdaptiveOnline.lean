import Zcash.Snark.Soundness.AGM.OnlineMembers

/-!
# Arbitrary adaptive online-AGM random-oracle adversaries

`LabeledOracleComp` records pre-answer AGM representations at each ordinary oracle query.
`ComputedAdaptiveOnlineAGMFSFamily` permits arbitrary query order and continuation without
requiring phase, cut, or trace objects.
-/

namespace Zcash.Snark

/-- An adaptive oracle computation whose query nodes carry data not passed to the oracle.  The
oracle still receives only `t : T`, so different labels at the same `t` share one oracle answer. -/
inductive LabeledOracleComp (T F : Type*) (Label : T → Type*) (α : Type*) where
  | pure (a : α)
  | query (t : T) (label : Label t) (k : F → LabeledOracleComp T F Label α)

namespace LabeledOracleComp

variable {T F α β : Type*} {Label : T → Type*}

/-- Forget query annotations, preserving the exact adaptive query tree seen by the random oracle. -/
def erase : LabeledOracleComp T F Label α → OracleComp T F α
  | .pure a => .pure a
  | .query t _ k => .query t (fun u => (k u).erase)

/-- Run a labeled computation against an ordinary oracle table. -/
def run (A : LabeledOracleComp T F Label α) (O : T → F) : α := A.erase.run O

/-- The ordinary query log of a labeled computation. -/
def queries (A : LabeledOracleComp T F Label α) (O : T → F) : List T := A.erase.queries O

/-- The annotation attached to each query on one concrete run.  Answers are deliberately omitted:
they remain available from the oracle table, while this log records exactly the data fixed before
each answer was read. -/
structure QueryAnnotation (T : Type*) (Label : T → Type*) where
  point : T
  label : Label point

/-- Query annotations along the adaptive path selected by `O`. -/
def annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    List (QueryAnnotation T Label) :=
  match A with
  | .pure _ => []
  | .query t label k => ⟨t, label⟩ :: (k (O t)).annotations O

/-- Evaluate an adaptive computation and retain its query annotations in the same traversal.
Unlike calling `run` and then repeatedly calling `findLabel`, this consults the oracle exactly
once at each visited query node. -/
def runWithAnnotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    α × List (QueryAnnotation T Label) :=
  match A with
  | .pure a => (a, [])
  | .query t label k =>
      let rest := (k (O t)).runWithAnnotations O
      (rest.1, ⟨t, label⟩ :: rest.2)

@[simp] theorem runWithAnnotations_snd
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.runWithAnnotations O).2 = A.annotations O := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simp only [runWithAnnotations, annotations]
      rw [ih (O t)]

/-- Look up the first annotation at a point in an already retained log.  This traverses ordinary
data and does not re-run the adversary or consult the oracle. -/
def findLabelInAnnotations [DecidableEq T] :
    List (QueryAnnotation T Label) → (t : T) → Option (Label t)
  | [], _ => none
  | entry :: rest, t =>
      if h : entry.point = t then some (h ▸ entry.label)
      else findLabelInAnnotations rest t

/-- Retrieve the first annotation at `t`, if the computation queried `t`. -/
def findLabel [DecidableEq T] (A : LabeledOracleComp T F Label α) (O : T → F)
    (t : T) : Option (Label t) :=
  match A with
  | .pure _ => none
  | .query q label k =>
      if h : q = t then some (h ▸ label) else (k (O q)).findLabel O t

/-- A labeled computation is query-bounded exactly when its erased computation is. -/
abbrev QueryBound (A : LabeledOracleComp T F Label α) (Q : ℕ) : Prop := A.erase.QueryBound Q

/-- Sequence two labeled computations. -/
def bind : LabeledOracleComp T F Label α →
    (α → LabeledOracleComp T F Label β) → LabeledOracleComp T F Label β
  | .pure a, f => f a
  | .query t label k, f => .query t label (fun u => (k u).bind f)

@[simp] theorem erase_pure (a : α) :
    (pure a : LabeledOracleComp T F Label α).erase = .pure a := rfl

@[simp] theorem erase_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) :
    (query t label k).erase = .query t (fun u => (k u).erase) := rfl

@[simp] theorem erase_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) :
    (A.bind f).erase = A.erase.bind (fun a => (f a).erase) := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [bind, erase, OracleComp.bind]
      congr
      funext u
      exact ih u

@[simp] theorem run_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).run O = a := rfl

@[simp] theorem run_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).run O = (k (O t)).run O := rfl

@[simp] theorem run_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).run O = (f (A.run O)).run O := by
  simp only [run, erase_bind, OracleComp.run_bind]

@[simp] theorem annotations_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).annotations O = [] := rfl

@[simp] theorem annotations_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).annotations O =
      ⟨t, label⟩ :: (k (O t)).annotations O := rfl

/-- Erasing annotations gives the ordinary query log. -/
theorem queries_eq_map_annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    A.queries O = (A.annotations O).map QueryAnnotation.point := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [queries, erase, OracleComp.queries, annotations, List.map_cons]
      exact congrArg (List.cons t) (ih (O t))

@[simp] theorem runWithAnnotations_fst
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.runWithAnnotations O).1 = A.run O := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simpa only [runWithAnnotations, run_query] using ih (O t)

/-- Cached annotation lookup agrees with a fresh `findLabel` traversal. -/
theorem findLabelInAnnotations_annotations [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) :
    findLabelInAnnotations (A.annotations O) t = A.findLabel O t := by
  induction A with
  | pure => rfl
  | query q label k ih =>
      simp only [annotations, findLabelInAnnotations, findLabel]
      split
      · rfl
      · exact ih (O q)

/-- A labeled computation's result, query log, and annotations depend only on the table's
values at its own queries.  This is the locality fact behind every oracle-access certificate:
agreement on the query log reproduces the entire run. -/
theorem run_queries_annotations_eq_of_agree {A : LabeledOracleComp T F Label α} :
    ∀ {O O' : T → F}, (∀ t ∈ A.queries O, O' t = O t) →
      A.run O' = A.run O ∧ A.queries O' = A.queries O ∧
        A.annotations O' = A.annotations O := by
  induction A with
  | pure a => exact fun _ => ⟨rfl, rfl, rfl⟩
  | query t label k ih =>
      intro O O' h
      have hmemHead : t ∈ (LabeledOracleComp.query t label k).queries O := by
        simp [queries, erase, OracleComp.queries]
      have ht : O' t = O t := h t hmemHead
      have htail := ih (O t) (O := O) (O' := O') (fun s hs => h s (by
        simp only [queries, erase, OracleComp.queries, List.mem_cons]
        exact Or.inr (by simpa [queries, erase] using hs)))
      refine ⟨?_, ?_, ?_⟩
      · show ((k (O' t)).erase).run O' = ((k (O t)).erase).run O
        rw [ht]
        exact htail.1
      · show t :: ((k (O' t)).erase).queries O' = t :: ((k (O t)).erase).queries O
        rw [ht]
        exact congrArg _ htail.2.1
      · show ⟨t, label⟩ :: (k (O' t)).annotations O' = ⟨t, label⟩ :: (k (O t)).annotations O
        rw [ht]
        exact congrArg _ htail.2.2

/-- Locality of the single-traversal execution: agreement on the query log reproduces the
retained output and annotation log together. -/
theorem runWithAnnotations_eq_of_agree {A : LabeledOracleComp T F Label α} {O O' : T → F}
    (h : ∀ t ∈ A.queries O, O' t = O t) :
    A.runWithAnnotations O' = A.runWithAnnotations O := by
  have hall := run_queries_annotations_eq_of_agree (A := A) h
  ext1 <;> simp [runWithAnnotations_fst, runWithAnnotations_snd, hall.1, hall.2.2]

/-- The retained log contains exactly the ordinary query path. -/
theorem annotations_length_eq_queries
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.annotations O).length = (A.queries O).length := by
  rw [queries_eq_map_annotations, List.length_map]

/-- A query-bounded adaptive computation's one-pass output/annotation log has the same bound. -/
theorem runWithAnnotations_log_length_le
    (A : LabeledOracleComp T F Label α) {Q : ℕ} (hQ : A.QueryBound Q) (O : T → F) :
    (A.runWithAnnotations O).2.length ≤ Q := by
  rw [runWithAnnotations_snd, annotations_length_eq_queries]
  exact A.erase.queries_length_le hQ O

@[simp] theorem findLabel_isSome_iff [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) :
    (A.findLabel O t).isSome ↔ t ∈ A.queries O := by
  induction A with
  | pure a => simp [findLabel, queries, erase, OracleComp.queries]
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel, queries, erase, OracleComp.queries]
      · simpa [findLabel, h, queries, erase, OracleComp.queries, Ne.symm h] using ih (O q)

/-- Post-processing the output with a pure continuation leaves the first labels alone. -/
@[simp] theorem findLabel_bind_pure {β : Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (f : α → β) (O : T → F) (t : T) :
    (A.bind fun a => pure (f a)).findLabel O t = A.findLabel O t := by
  induction A with
  | pure a => rfl
  | query q label k ih =>
      by_cases h : q = t
      · simp [bind, findLabel, h]
      · simp [bind, findLabel, h, ih (O q)]

/-- If no query-time annotation exists at `t`, reprogramming `t` cannot change the result. -/
theorem run_update_of_findLabel_eq_none [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F)
    (hfresh : A.findLabel O t = none) :
    A.run (Function.update O t v) = A.run O := by
  apply OracleComp.run_update_of_not_mem_queries
  intro hmem
  have : (A.findLabel O t).isSome := (findLabel_isSome_iff A O t).2 hmem
  simp [hfresh] at this

/-- The first annotation at a point is fixed before that point's answer is read. -/
theorem findLabel_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F) :
    A.findLabel (Function.update O t v) t = A.findLabel O t := by
  induction A with
  | pure a => rfl
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel]
      · simp [findLabel, h, ih (O q)]

/-- The bad set selected at `t`: use the first query-time annotation when it exists, otherwise
use a set computed from the final output.  The fallback is safe because `findLabel = none` means
reprogramming `t` cannot change that output. -/
def firstLabelOrFallbackBad [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) : Set F :=
  match A.findLabel O t with
  | some label => bad t label O
  | none => fallback (A.run O) t O

/-- `firstLabelOrFallbackBad` is blind to the answer at the point it prices. -/
theorem firstLabelOrFallbackBad_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    (t : T) (O : T → F) (v : F) :
    firstLabelOrFallbackBad A bad fallback t (Function.update O t v) =
      firstLabelOrFallbackBad A bad fallback t O := by
  rw [firstLabelOrFallbackBad, firstLabelOrFallbackBad, A.findLabel_update_self O t v]
  cases hfound : A.findLabel O t with
  | some label => exact hbadBlind t label O v
  | none =>
    rw [A.run_update_of_findLabel_eq_none O t v hfound]
    exact hfallbackBlind (A.run O) t O v

/-- **Arbitrary adaptive labeled squeeze.**  Complete the adversary with the verifier's selected
query.  Its answer lands in the first pre-answer annotation's bad set, or in the fresh fallback
set, with probability at most `(Q+1)·ε`.  No phase ordering or prefix-determinism premise is
required. -/
theorem firstLabelOrFallbackBad_measure_le
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (A : LabeledOracleComp T F Label α) (xpt : α → T)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype F).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ a t O,
      (PMF.uniformOfFintype F).toOuterMeasure (fallback a t O) ≤ epsilon)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈
        firstLabelOrFallbackBad A bad fallback (xpt (A.run O)) O} ≤
      (Q + 1 : ℕ) * epsilon := by
  let esc : T → (T → F) → Set F := firstLabelOrFallbackBad A bad fallback
  have hsub : {O : T → F | O (xpt (A.run O)) ∈ esc (xpt (A.run O)) O} ⊆
      {O : T → F | (A.erase.completing (fun a (_ : Fin 1) => xpt a)).escapesDuringC esc O} := by
    intro O hO
    exact OracleComp.escapesDuringC_completing esc
      (fun a (_ : Fin 1) => xpt a) (j := 0) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  apply escapesDuringC_measure_le' esc
  · exact firstLabelOrFallbackBad_update_self A bad fallback hbadBlind hfallbackBlind
  · intro t O
    unfold esc firstLabelOrFallbackBad
    cases A.findLabel O t with
    | some label => exact hbad t label O
    | none => exact hfallback (A.run O) t O
  · exact OracleComp.queryBound_completing (fun a (_ : Fin 1) => xpt a) hQ

/-- Reduction shell for an output-defined failure event.  Once a computed relation finder covers
every discrepancy between final data and the first query annotation, the no-relation branch is
contained in the arbitrary adaptive labeled squeeze and inherits its `(Q+1) * epsilon` bound. -/
theorem finalBadWithoutRelation_measure_le
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (A : LabeledOracleComp T F Label α) (xpt : α → T)
    (finalBad : α → T → (T → F) → Set F)
    (finder : (T → F) → Option β)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hcover : ∀ O,
      O (xpt (A.run O)) ∈ finalBad (A.run O) (xpt (A.run O)) O →
      finder O = none →
      O (xpt (A.run O)) ∈ firstLabelOrFallbackBad A bad fallback
        (xpt (A.run O)) O)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype F).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ a t O,
      (PMF.uniformOfFintype F).toOuterMeasure (fallback a t O) ≤ epsilon)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈
          finalBad (A.run O) (xpt (A.run O)) O ∧ finder O = none} ≤
      (Q + 1 : ℕ) * epsilon := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (firstLabelOrFallbackBad_measure_le A xpt bad fallback hbadBlind hfallbackBlind
      hbad hfallback hQ)
  intro O hO
  exact hcover O hO.1 hO.2

end LabeledOracleComp

/-- Extract the group elements, in order, from a Fiat--Shamir transcript. -/
def transcriptGroupPoints {F G : Type*} : List (TranscriptElt F G) → List G
  | [] => []
  | .point P :: rest => P :: transcriptGroupPoints rest
  | _ :: rest => transcriptGroupPoints rest

/-- A point absorbed into a transcript occurs in its ordered group-point projection. -/
theorem mem_transcriptGroupPoints_of_mem_point {F G : Type*} {P : G}
    {t : List (TranscriptElt F G)} (h : TranscriptElt.point P ∈ t) :
    P ∈ transcriptGroupPoints t := by
  induction t with
  | nil => simp at h
  | cons e rest ih =>
      cases e with
      | scalar x =>
          simp only [List.mem_cons, reduceCtorEq] at h
          exact ih (by simpa using h)
      | point Q =>
          simp only [List.mem_cons, TranscriptElt.point.injEq] at h
          simp only [transcriptGroupPoints, List.mem_cons]
          exact h.imp id ih
      | challenge =>
          simp only [List.mem_cons, reduceCtorEq, false_or] at h
          exact ih h

/-- Projecting group points preserves transcript prefixes. -/
theorem transcriptGroupPoints_prefix {F G : Type*}
    {t u : List (TranscriptElt F G)} (h : t <+: u) :
    transcriptGroupPoints t <+: transcriptGroupPoints u := by
  obtain ⟨tail, rfl⟩ := h
  have append_eq : transcriptGroupPoints (t ++ tail) =
      transcriptGroupPoints t ++ transcriptGroupPoints tail := by
    induction t with
    | nil => rfl
    | cons e rest ih =>
        cases e <;> simp only [List.cons_append, transcriptGroupPoints, ih]
  rw [append_eq]
  exact List.prefix_append _ _

/-- The shape-determined deployed squeeze points are nested in challenge order. -/
theorem preIpaSqueezePoints_prefix_of_le {G : Type*}
    {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (hwf : PsWellFormed ps)
    (i j : Fin 11) (hij : (i : ℕ) ≤ (j : ℕ)) :
    preIpaSqueezePoints init ps i <+: preIpaSqueezePoints init ps j := by
  let z := preIpaTranscript init ps
  have hi := List.prefix_iff_eq_take.mp (preIpaSqueezePoints_prefix init ps i)
  have hj := List.prefix_iff_eq_take.mp (preIpaSqueezePoints_prefix init ps j)
  have hmono : Monotone (preIpaLen shape init.length) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [preIpaLen] <;> omega
  have hlen : (preIpaSqueezePoints init ps i).length ≤
      (preIpaSqueezePoints init ps j).length := by
    rw [preIpaSqueezePoints_length_eq init ps hwf i,
      preIpaSqueezePoints_length_eq init ps hwf j]
    exact hmono hij
  rw [hi, hj]
  have htake := List.take_prefix (preIpaSqueezePoints init ps i).length
    (List.take (preIpaSqueezePoints init ps j).length z)
  simpa only [List.take_take, min_eq_left hlen] using htake

/-- Prover-emitted commitment points fixed before `x₁`, without AGM coordinates. -/
def ProofString.preX1CommitmentPoints {G : Type*} {shape : Shape}
    (ps : ProofString shape Fp G) : List G :=
  (List.ofFn fun p => List.ofFn fun i => ps.adviceCommitments p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedInput p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedTable p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => ps.permutationProduct p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => ps.lookupProduct p i).flatten ++
  [ps.vanishingRandom] ++ List.ofFn ps.hPieces

/-- Every pre-`x₁` commitment point occurs in the `x₁` query transcript. -/
theorem ProofString.preX1CommitmentPoints_coveredAtX1
    {G : Type*} {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (P : G) (hP : P ∈ ps.preX1CommitmentPoints) :
    P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 5) := by
  apply mem_transcriptGroupPoints_of_mem_point
  change TranscriptElt.point P ∈ preX1Transcript init ps
  rw [ProofString.preX1CommitmentPoints] at hP
  rcases List.mem_append.mp hP with hpre | hpiece
  rcases List.mem_append.mp hpre with hpre | hran
  rcases List.mem_append.mp hpre with hpre | hlk
  rcases List.mem_append.mp hpre with hpre | hperm
  rcases List.mem_append.mp hpre with hpre | htab
  rcases List.mem_append.mp hpre with hadv | hin
  · obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hadv
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hPl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints]
  · obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hin
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hPl)
    rw [← hi]
    simp [preX1Transcript, absorbLookupPermuted, absorbPoints]
    exact Or.inr (Or.inr (Or.inl ⟨p, i, Or.inl rfl⟩))
  · obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp htab
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hPl)
    rw [← hi]
    simp [preX1Transcript, absorbLookupPermuted, absorbPoints]
    exact Or.inr (Or.inr (Or.inl ⟨p, i, Or.inr rfl⟩))
  · obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hperm
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hPl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints]
  · obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hlk
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hPl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints]
  · rw [List.mem_singleton.mp hran]
    simp [preX1Transcript]
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    rw [← hi]
    simp [preX1Transcript, absorbPoints]

/-- Every prover representation used before `x₁` is already represented by the online-AGM
annotation at the deployed `x₁` squeeze point. -/
theorem AlgebraicProofString.preX1Points_coveredAtX1
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.preX1Points) :
    ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 5) := by
  apply mem_transcriptGroupPoints_of_mem_point
  change TranscriptElt.point ap.point ∈ preX1Transcript init aps.erase
  rw [AlgebraicProofString.preX1Points] at hap
  rcases List.mem_append.mp hap with hpre | hpiece
  rcases List.mem_append.mp hpre with hpre | hran
  rcases List.mem_append.mp hpre with hpre | hlk
  rcases List.mem_append.mp hpre with hpre | hperm
  rcases List.mem_append.mp hpre with hpre | htab
  rcases List.mem_append.mp hpre with hadv | hin
  · obtain ⟨l, hl, hapl⟩ := List.mem_flatten.mp hadv
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hapl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints, AlgebraicProofString.erase]
  · obtain ⟨l, hl, hapl⟩ := List.mem_flatten.mp hin
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hapl)
    rw [← hi]
    simp [preX1Transcript, absorbLookupPermuted, absorbPoints,
      AlgebraicProofString.erase]
    exact Or.inr (Or.inr (Or.inl ⟨p, i, Or.inl rfl⟩))
  · obtain ⟨l, hl, hapl⟩ := List.mem_flatten.mp htab
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hapl)
    rw [← hi]
    simp [preX1Transcript, absorbLookupPermuted, absorbPoints,
      AlgebraicProofString.erase]
    exact Or.inr (Or.inr (Or.inl ⟨p, i, Or.inr rfl⟩))
  · obtain ⟨l, hl, hapl⟩ := List.mem_flatten.mp hperm
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hapl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints, AlgebraicProofString.erase]
  · obtain ⟨l, hl, hapl⟩ := List.mem_flatten.mp hlk
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp ▸ hapl)
    rw [← hi]
    simp [preX1Transcript, absorbPoints2, absorbPoints, AlgebraicProofString.erase]
  · have hr := List.mem_singleton.mp hran
    rw [hr]
    simp [preX1Transcript, AlgebraicProofString.erase]
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    rw [← hi]
    simp [preX1Transcript, absorbPoints, AlgebraicProofString.erase]

/-- The final algebraic representations whose coefficients can affect a deployed pre-IPA
challenge surface. Later surfaces include commitments emitted since `x₁`. -/
def AlgebraicProofString.representationsBefore
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 11) :
    List (AlgebraicPoint (F := Fp) basis) :=
  if (n : ℕ) < 7 then aps.preX1Points
  else if (n : ℕ) < 9 then aps.preX1Points ++ [aps.multiopenQPrime]
  else aps.preX1Points ++ [aps.multiopenQPrime, aps.ipaS]

/-- Coordinate-free counterpart of `representationsBefore`. -/
def ProofString.commitmentPointsBefore {G : Type*} {shape : Shape}
    (ps : ProofString shape Fp G) (n : Fin 11) : List G :=
  if (n : ℕ) < 7 then ps.preX1CommitmentPoints
  else if (n : ℕ) < 9 then ps.preX1CommitmentPoints ++ [ps.multiopenQPrime]
  else ps.preX1CommitmentPoints ++ [ps.multiopenQPrime, ps.ipaS]

/-- Erasing the AGM coordinates of the stage-local representations gives exactly the ordinary
commitment list available at that stage. -/
@[simp] theorem AlgebraicProofString.representationsBefore_points
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 11) :
    (aps.representationsBefore n).map AlgebraicPoint.point =
      aps.erase.commitmentPointsBefore n := by
  unfold AlgebraicProofString.representationsBefore ProofString.commitmentPointsBefore
  by_cases h7 : (n : ℕ) < 7
  · simp [h7, AlgebraicProofString.preX1Points,
      ProofString.preX1CommitmentPoints, AlgebraicProofString.erase, Function.comp_def]
  · by_cases h9 : (n : ℕ) < 9 <;>
      simp [h7, h9, AlgebraicProofString.preX1Points,
        ProofString.preX1CommitmentPoints, AlgebraicProofString.erase, Function.comp_def]

/-- Every coordinate-free stage point occurs in that stage's transcript. -/
theorem ProofString.commitmentPointsBefore_covered
    {G : Type*} {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (hwf : PsWellFormed ps)
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ)) (P : G)
    (hP : P ∈ ps.commitmentPointsBefore n) :
    P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps n) := by
  have lift_mem {i : Fin 11}
      (hin : P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps i))
      (hin_le : (i : ℕ) ≤ (n : ℕ)) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps n) :=
    (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init ps hwf i n hin_le)).mem hin
  unfold ProofString.commitmentPointsBefore at hP
  by_cases h7 : (n : ℕ) < 7
  · apply lift_mem (i := 5) (ps.preX1CommitmentPoints_coveredAtX1 init P
      (by simpa [h7] using hP))
    omega
  · by_cases h9 : (n : ℕ) < 9
    · simp only [if_neg h7, if_pos h9, List.mem_append, List.mem_singleton] at hP
      rcases hP with hpre | hq
      · apply lift_mem (i := 5) (ps.preX1CommitmentPoints_coveredAtX1 init P hpre)
        omega
      · subst P
        apply lift_mem (i := 7)
        · apply mem_transcriptGroupPoints_of_mem_point
          exact qPrime_mem_preX3Transcript init ps
        · omega
    · simp only [if_neg h7, if_neg h9, List.mem_append, List.mem_cons] at hP
      rcases hP with hpre | hq | hs
      · apply lift_mem (i := 5) (ps.preX1CommitmentPoints_coveredAtX1 init P hpre)
        omega
      · subst P
        apply lift_mem (i := 7)
        · apply mem_transcriptGroupPoints_of_mem_point
          exact qPrime_mem_preX3Transcript init ps
        · omega
      · rcases hs with rfl | hs
        · apply lift_mem (i := 9)
          · apply mem_transcriptGroupPoints_of_mem_point
            exact ipaS_mem_preIpaSqueezePoints_nine init ps
          · omega
        · simp at hs

/-- Every representation used by a deployed surface is already present in that surface's
transcript. This is commit-before-challenge chronology for a bare adaptive adversary; it does not
assume an honest execution phase. -/
theorem AlgebraicProofString.representationsBefore_covered
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.representationsBefore n) :
    ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase n) := by
  have lift_mem {i : Fin 11} (hin : ap.point ∈
      transcriptGroupPoints (preIpaSqueezePoints init aps.erase i))
      (hin_le : (i : ℕ) ≤ (n : ℕ)) :
      ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase n) :=
    (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init aps.erase hwf i n hin_le)).mem hin
  unfold AlgebraicProofString.representationsBefore at hap
  by_cases h7 : (n : ℕ) < 7
  · apply lift_mem (i := 5) (aps.preX1Points_coveredAtX1 init ap (by simpa [h7] using hap))
    omega
  · by_cases h9 : (n : ℕ) < 9
    · simp only [if_neg h7, if_pos h9, List.mem_append, List.mem_singleton] at hap
      rcases hap with hpre | hq
      · apply lift_mem (i := 5) (aps.preX1Points_coveredAtX1 init ap hpre)
        omega
      · subst ap
        apply lift_mem (i := 7)
        · apply mem_transcriptGroupPoints_of_mem_point
          change TranscriptElt.point aps.erase.multiopenQPrime ∈
            preX3Transcript init aps.erase
          exact qPrime_mem_preX3Transcript init aps.erase
        · omega
    · simp only [if_neg h7, if_neg h9, List.mem_append, List.mem_cons] at hap
      rcases hap with hpre | hq | hs
      · apply lift_mem (i := 5) (aps.preX1Points_coveredAtX1 init ap hpre)
        omega
      · subst ap
        apply lift_mem (i := 7)
        · apply mem_transcriptGroupPoints_of_mem_point
          change TranscriptElt.point aps.erase.multiopenQPrime ∈
            preX3Transcript init aps.erase
          exact qPrime_mem_preX3Transcript init aps.erase
        · omega
      · rcases hs with rfl | hs
        · apply lift_mem (i := 9)
          · apply mem_transcriptGroupPoints_of_mem_point
            change TranscriptElt.point aps.erase.ipaS ∈
              preIpaSqueezePoints init aps.erase 9
            exact ipaS_mem_preIpaSqueezePoints_nine init aps.erase
          · omega
        · simp at hs

/-- All final representations that can affect the IPA root at round `j`: the complete pre-IPA
source followed by every round pair through `j`. -/
def AlgebraicProofString.representationsBeforeRound
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (j : Fin shape.k) :
    List (AlgebraicPoint (F := Fp) basis) :=
  aps.representationsBefore 10 ++
    (((List.finRange shape.k).take (j.val + 1)).flatMap fun i =>
      [(aps.ipaRounds i).1, (aps.ipaRounds i).2])

/-- Coordinate-free points available before IPA round `j`, in the same order as
`representationsBeforeRound`. -/
def ProofString.commitmentPointsBeforeRound {G : Type*} {shape : Shape}
    (ps : ProofString shape Fp G) (j : Fin shape.k) : List G :=
  ps.commitmentPointsBefore 10 ++
    (((List.finRange shape.k).take (j.val + 1)).flatMap fun i =>
      [(ps.ipaRounds i).1, (ps.ipaRounds i).2])

@[simp] theorem AlgebraicProofString.representationsBeforeRound_points
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (j : Fin shape.k) :
    (aps.representationsBeforeRound j).map AlgebraicPoint.point =
      aps.erase.commitmentPointsBeforeRound j := by
  unfold AlgebraicProofString.representationsBeforeRound
    ProofString.commitmentPointsBeforeRound
  rw [List.map_append, aps.representationsBefore_points]
  congr 1
  generalize (List.finRange shape.k).take (j.val + 1) = rounds
  induction rounds with
  | nil => rfl
  | cons i rounds ih => simp [ih, AlgebraicProofString.erase]

/-- Every coordinate-free point available at round `j` occurs in its actual query transcript. -/
theorem ProofString.commitmentPointsBeforeRound_covered
    {shape : Shape} (init : List (TranscriptElt Fp VestaG))
    (ps : ProofString shape Fp VestaG) (hwf : PsWellFormed ps)
    (j : Fin shape.k) (P : VestaG) (hP : P ∈ ps.commitmentPointsBeforeRound j) :
    P ∈ transcriptGroupPoints
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) := by
  rw [ProofString.commitmentPointsBeforeRound] at hP
  rcases List.mem_append.mp hP with hpre | hround
  · have hin := ps.commitmentPointsBefore_covered init hwf 10 (by omega) P hpre
    apply (transcriptGroupPoints_prefix ?_).mem hin
    unfold roundTranscriptFin
    exact List.prefix_append _ _
  · obtain ⟨i, hi, hpair⟩ := List.mem_flatMap.mp hround
    have hij : i.val ≤ j.val := by
      obtain ⟨m, hm, hmi⟩ := List.mem_take_iff_getElem.mp hi
      have him : i.val = m := by
        have := congrArg Fin.val hmi
        simpa using this.symm
      simp only [List.length_finRange] at hm
      omega
    apply mem_transcriptGroupPoints_of_mem_point
    apply (roundTranscriptFin_prefix (preIpaTranscript init ps) ps.ipaRounds hij).mem
    rw [roundTranscriptFin_eq_append]
    rcases List.mem_cons.mp hpair with hL | hR
    · rw [hL]
      simp
    · have hR' : P = (ps.ipaRounds i).2 := by simpa using hR
      rw [hR']
      simp

/-- Every representation affecting round `j` occurs in the actual round-`j` query transcript. -/
theorem AlgebraicProofString.representationsBeforeRound_covered
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (j : Fin shape.k) (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.representationsBeforeRound j) :
    ap.point ∈ transcriptGroupPoints
      (roundTranscriptFin (preIpaTranscript init aps.erase) aps.erase.ipaRounds j) := by
  rw [AlgebraicProofString.representationsBeforeRound] at hap
  rcases List.mem_append.mp hap with hpre | hround
  · have hin := aps.representationsBefore_covered init hwf 10 (by omega) ap hpre
    apply (transcriptGroupPoints_prefix ?_).mem hin
    unfold roundTranscriptFin
    exact List.prefix_append _ _
  · obtain ⟨i, hi, hapPair⟩ := List.mem_flatMap.mp hround
    have hij : i.val ≤ j.val := by
      obtain ⟨m, hm, hmi⟩ := List.mem_take_iff_getElem.mp hi
      have him : i.val = m := by
        have := congrArg Fin.val hmi
        simpa using this.symm
      simp only [List.length_finRange] at hm
      omega
    apply mem_transcriptGroupPoints_of_mem_point
    apply (roundTranscriptFin_prefix (preIpaTranscript init aps.erase)
      aps.erase.ipaRounds hij).mem
    rw [roundTranscriptFin_eq_append]
    rcases List.mem_cons.mp hapPair with hL | hR
    · rw [hL]
      simp [AlgebraicProofString.erase]
    · have hR' : ap = (aps.ipaRounds i).2 := by simpa using hR
      rw [hR']
      simp [AlgebraicProofString.erase]

/-- Online AGM data attached to one random-oracle query.  The represented points are exactly the
group elements already absorbed into the queried transcript, in transcript order. -/
structure AlgebraicTranscriptQuery {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [Fintype ι]
    (basis : ι → G) {L : ℕ} (t : BTranscript F G L) where
  representedPoints : List (AlgebraicPoint (F := F) basis)
  points_eq : representedPoints.map AlgebraicPoint.point = transcriptGroupPoints t.val

namespace AlgebraicTranscriptQuery

/-- Recover the first query-time representation of a point occurring in the transcript. -/
def representationOfPoint {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) (P : G)
    (hP : P ∈ transcriptGroupPoints t.val) : AlgebraicPoint (F := F) basis := by
  have H : (query.representedPoints.find? (fun ap => ap.point = P)).isSome := by
    rw [List.find?_isSome]
    have hP' : P ∈ query.representedPoints.map AlgebraicPoint.point := by
      rw [query.points_eq]
      exact hP
    obtain ⟨ap, hap, hpoint⟩ := List.mem_map.mp hP'
    exact ⟨ap, hap, by simpa using hpoint⟩
  exact (query.representedPoints.find? (fun ap => ap.point = P)).get H

@[simp] theorem representationOfPoint_point {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) (P : G)
    (hP : P ∈ transcriptGroupPoints t.val) :
    (query.representationOfPoint P hP).point = P := by
  unfold representationOfPoint
  let H : (query.representedPoints.find? (fun ap => ap.point = P)).isSome := by
    rw [List.find?_isSome]
    have hP' : P ∈ query.representedPoints.map AlgebraicPoint.point := by
      rw [query.points_eq]
      exact hP
    obtain ⟨ap, hap, hpoint⟩ := List.mem_map.mp hP'
    exact ⟨ap, hap, by simpa using hpoint⟩
  have hsome := List.find?_some (Option.some_get H).symm
  simpa using hsome

/-- Select query-time AGM representations for an ordered list of transcript points. -/
def representationsForPoints {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) :
    (points : List G) → (∀ P ∈ points, P ∈ transcriptGroupPoints t.val) →
      List (AlgebraicPoint (F := F) basis)
  | [], _ => []
  | P :: rest, hcovered =>
      query.representationOfPoint P (hcovered P (by simp)) ::
        query.representationsForPoints rest (fun candidate hmem =>
          hcovered candidate (by simp [hmem]))

@[simp] theorem representationsForPoints_points {F G ι : Type*}
    [Field F] [DecidableEq G] [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t)
    (points : List G) (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints t.val) :
    (query.representationsForPoints points hcovered).map AlgebraicPoint.point = points := by
  induction points with
  | nil => rfl
  | cons P rest ih =>
      simp only [representationsForPoints, List.map_cons, representationOfPoint_point,
        List.cons.injEq, true_and]
      exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))

/-- Select query-time representations for a final list of points known to occur in the queried
transcript. -/
def representationsFor {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) :
    (final : List (AlgebraicPoint (F := F) basis)) →
      (∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) →
      List (AlgebraicPoint (F := F) basis)
  | [], _ => []
  | ap :: rest, hcovered =>
      query.representationOfPoint ap.point (hcovered ap (by simp)) ::
        query.representationsFor rest (fun candidate hmem =>
          hcovered candidate (by simp [hmem]))

/-- Selection preserves the final list's group points exactly. -/
theorem representationsFor_points {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    (query.representationsFor final hcovered).map AlgebraicPoint.point =
      final.map AlgebraicPoint.point := by
  induction final with
  | nil => rfl
  | cons ap rest ih =>
      simp only [representationsFor, List.map_cons, representationOfPoint_point,
        List.cons.injEq, true_and]
      exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))

/-- Selecting by represented algebraic points is the same deterministic lookup as selecting their
underlying ordinary points. -/
theorem representationsFor_eq_representationsForPoints
    {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    query.representationsFor final hcovered =
      query.representationsForPoints (final.map AlgebraicPoint.point) (by
        intro P hP
        obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
        exact hcovered ap hap) := by
  induction final with
  | nil => rfl
  | cons ap rest ih =>
      simp only [representationsFor, List.map_cons, representationsForPoints]
      congr 1
      exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))

/-- If selecting every final representation from the first query reproduces the final list, then
the query-time representation of each member is that member itself. -/
theorem representationOfPoint_eq_of_representationsFor_eq
    {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val)
    (hselected : query.representationsFor final hcovered = final)
    (ap : AlgebraicPoint (F := F) basis) (hap : ap ∈ final) :
    query.representationOfPoint ap.point (hcovered ap hap) = ap := by
  induction final with
  | nil => simp at hap
  | cons first rest ih =>
      have hhead : query.representationOfPoint first.point
          (hcovered first (by simp)) = first := by
        exact Option.some.inj (by
          simpa only [representationsFor, List.head?_cons] using
            congrArg List.head? hselected)
      have htail : query.representationsFor rest
          (fun candidate hmem => hcovered candidate (by simp [hmem])) = rest := by
        simpa only [representationsFor, List.tail_cons] using congrArg List.tail hselected
      rcases List.mem_cons.mp hap with rfl | hap
      · exact hhead
      · exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))
          htail hap

end AlgebraicTranscriptQuery

/-- An algebraic point is determined by its ordinary point and coefficient vector; representation
equalities themselves are proof-irrelevant. -/
theorem _root_.Zcash.AlgebraicPoint.eq_of_point_eq_of_coeffs_eq
    {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {P Q : AlgebraicPoint (F := F) basis}
    (hpoint : P.point = Q.point) (hcoeff : P.coeffs = Q.coeffs) : P = Q := by
  cases P with
  | mk point repr =>
      cases Q with
      | mk point' repr' =>
          simp only at hpoint
          subst point'
          cases repr with
          | mk coeffs hEq =>
              cases repr' with
              | mk coeffs' hEq' =>
                  simp only [AlgebraicPoint.coeffs] at hcoeff
                  subst coeffs'
                  rfl

/-- Pointwise point and coefficient maps jointly determine an algebraic-point list. -/
theorem algebraicPointList_eq_of_maps_eq
    {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {left right : List (AlgebraicPoint (F := F) basis)}
    (hpoints : left.map AlgebraicPoint.point = right.map AlgebraicPoint.point)
    (hcoeffs : left.map AlgebraicPoint.coeffs = right.map AlgebraicPoint.coeffs) :
    left = right := by
  induction left generalizing right with
  | nil => simpa using hpoints
  | cons P ps ih =>
      cases right with
      | nil => simp at hpoints
      | cons Q qs =>
          have hp : P.point = Q.point := by simpa using congrArg List.head? hpoints
          have hc : P.coeffs = Q.coeffs := by simpa using congrArg List.head? hcoeffs
          have hPQ := AlgebraicPoint.eq_of_point_eq_of_coeffs_eq hp hc
          subst Q
          congr 1
          · exact ih (by simpa using congrArg List.tail hpoints)
              (by simpa using congrArg List.tail hcoeffs)

/-- Compare two valid representations of the same point.  A coefficient mismatch computes an
explicit relation over the public basis; equality returns no relation. -/
def representationMismatchRelation? {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (P Q : AlgebraicPoint (F := F) basis) (hpoint : P.point = Q.point) :
    Option (AlgebraicRelationWitness (F := F) basis) :=
  if hcoeff : P.coeffs = Q.coeffs then none else
    some
      { coeffs := P.coeffs - Q.coeffs
        nontrivial := sub_ne_zero.mpr hcoeff
        relation := by
          calc
            representationEval basis (P.coeffs - Q.coeffs) =
                representationEval basis P.coeffs - representationEval basis Q.coeffs := by
              simp only [representationEval, Pi.sub_apply, sub_smul,
                Finset.sum_sub_distrib]
            _ = P.point - Q.point := by rw [P.hEq, Q.hEq]
            _ = 0 := by rw [hpoint, sub_self] }

@[simp] theorem representationMismatchRelation?_eq_none_iff
    {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (P Q : AlgebraicPoint (F := F) basis) (hpoint : P.point = Q.point) :
    representationMismatchRelation? P Q hpoint = none ↔ P.coeffs = Q.coeffs := by
  simp [representationMismatchRelation?]

/-- Compare two pointwise-equal representation lists.  Either every coefficient vector agrees or
the first mismatch is returned as an explicit relation.  This is executable: the only branching
is equality of finite coefficient vectors. -/
def representationListsEqualOrRelation
    {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (left right : List (AlgebraicPoint (F := F) basis))
    (hpoints : left.map AlgebraicPoint.point = right.map AlgebraicPoint.point) :
    (left.map AlgebraicPoint.coeffs = right.map AlgebraicPoint.coeffs) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact PSum.inl rfl
      | cons Q qs => simp at hpoints
  | cons P ps ih =>
      cases right with
      | nil => simp at hpoints
      | cons Q qs =>
          have hpoint : P.point = Q.point := by simpa using congrArg List.head? hpoints
          have htail : ps.map AlgebraicPoint.point = qs.map AlgebraicPoint.point := by
            simpa using congrArg List.tail hpoints
          cases hrel : representationMismatchRelation? P Q hpoint with
          | some relation => exact PSum.inr relation
          | none =>
              have hcoeff := (representationMismatchRelation?_eq_none_iff P Q hpoint).1 hrel
              match ih qs htail with
              | PSum.inr relation => exact PSum.inr relation
              | PSum.inl hrest => exact PSum.inl (by simp [hcoeff, hrest])

/-- Evidence that the representations used at a completed transcript were fixed by an actual
query annotation before the oracle answer was read. -/
structure QueryRepresentationPinned {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [Fintype ι] {α : Type*}
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis)) where
  query : AlgebraicTranscriptQuery (F := F) basis t
  found : A.findLabel O t = some query
  coefficients_eq : query.representedPoints.map AlgebraicPoint.coeffs =
    final.map AlgebraicPoint.coeffs

/-- At any completed transcript, either the adversary never queried it, its final coefficients
equal the pre-answer annotation, or the discrepancy is an explicit DLOG relation. -/
def queryRepresentationProvenanceOrRelation
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G]
    [Fintype ι] {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hfinal : final.map AlgebraicPoint.point = transcriptGroupPoints t.val) :
    (A.findLabel O t = none ⊕' QueryRepresentationPinned t A O final) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  match hfound : A.findLabel O t with
  | none => exact PSum.inl (PSum.inl rfl)
  | some query =>
      have hpoints : query.representedPoints.map AlgebraicPoint.point =
          final.map AlgebraicPoint.point := query.points_eq.trans hfinal.symm
      match representationListsEqualOrRelation query.representedPoints final hpoints with
      | PSum.inr relation => exact PSum.inr relation
      | PSum.inl hcoeff =>
          exact PSum.inl (PSum.inr
            { query := query
              found := hfound
              coefficients_eq := hcoeff })

/-- Query-time provenance for only the represented points relevant to one soundness check.  This
avoids requiring verifier-fixed points in the transcript to be duplicated in a final proof list. -/
structure SelectedQueryRepresentationPinned
    {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [Fintype ι] {α : Type*}
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis)) where
  query : AlgebraicTranscriptQuery (F := F) basis t
  found : A.findLabel O t = some query
  covered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val
  coefficients_eq :
    (query.representationsFor final covered).map AlgebraicPoint.coeffs =
      final.map AlgebraicPoint.coeffs

/-- For any selected final points already absorbed at `t`, either `t` was never queried, their
coefficients equal the first pre-answer query annotations, or a mismatch computes a relation. -/
def selectedQueryRepresentationProvenanceOrRelation
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    (A.findLabel O t = none ⊕' SelectedQueryRepresentationPinned t A O final) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  match hfound : A.findLabel O t with
  | none => exact PSum.inl (PSum.inl rfl)
  | some query =>
      let selected := query.representationsFor final hcovered
      have hpoints : selected.map AlgebraicPoint.point = final.map AlgebraicPoint.point :=
        query.representationsFor_points final hcovered
      match representationListsEqualOrRelation selected final hpoints with
      | PSum.inr relation => exact PSum.inr relation
      | PSum.inl hcoeff =>
          exact PSum.inl (PSum.inr
            { query := query
              found := hfound
              covered := hcovered
              coefficients_eq := hcoeff })

/-- Executable projection of selected query-time provenance onto its DLOG-relation branch.
`none` means either the verifier prefix was fresh or every selected final coefficient vector was
already fixed by the first query at that prefix. -/
def selectedQueryRepresentationRelation?
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    Option (AlgebraicRelationWitness (F := F) basis) :=
  match A.findLabel O t with
  | none => none
  | some query =>
      let selected := query.representationsFor final hcovered
      have hpoints : selected.map AlgebraicPoint.point = final.map AlgebraicPoint.point :=
        query.representationsFor_points final hcovered
      match representationListsEqualOrRelation selected final hpoints with
      | PSum.inr relation => some relation
      | PSum.inl _ => none

/-- Cached-log implementation of the selected provenance check.  Every lookup below is over the
retained annotation list, so a finite collection of checks shares the adversary/oracle traversal.
-/
def selectedQueryRepresentationRelationFromAnnotations?
    {F G ι : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (annotations : List (LabeledOracleComp.QueryAnnotation
      (BTranscript F G L) (AlgebraicTranscriptQuery (F := F) basis)))
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    Option (AlgebraicRelationWitness (F := F) basis) :=
  match LabeledOracleComp.findLabelInAnnotations annotations t with
  | none => none
  | some query =>
      let selected := query.representationsFor final hcovered
      have hpoints : selected.map AlgebraicPoint.point = final.map AlgebraicPoint.point :=
        query.representationsFor_points final hcovered
      match representationListsEqualOrRelation selected final hpoints with
      | PSum.inr relation => some relation
      | PSum.inl _ => none

/-- The cached-log provenance finder is extensionally the original finder when the log is the
one produced by the same adaptive execution. -/
theorem selectedQueryRepresentationRelationFromAnnotations?_eq
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    selectedQueryRepresentationRelationFromAnnotations? t (A.annotations O) final hcovered =
      selectedQueryRepresentationRelation? t A O final hcovered := by
  unfold selectedQueryRepresentationRelationFromAnnotations?
  rw [show LabeledOracleComp.findLabelInAnnotations (A.annotations O) t =
      A.findLabel O t from LabeledOracleComp.findLabelInAnnotations_annotations A O t]
  rfl

/-- If the selected executable finder returns no relation, the prefix was fresh or the final
selected coefficients equal their first pre-answer query representations. -/
def selectedQueryRepresentationRelation?_eq_none
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val)
    (hnone : selectedQueryRepresentationRelation? t A O final hcovered = none) :
    A.findLabel O t = none ⊕' SelectedQueryRepresentationPinned t A O final := by
  unfold selectedQueryRepresentationRelation? at hnone
  cases hfound : A.findLabel O t with
  | none => exact PSum.inl rfl
  | some query =>
      simp only [hfound] at hnone
      cases hrelation : representationListsEqualOrRelation
          (query.representationsFor final hcovered) final
          (query.representationsFor_points final hcovered) with
      | inr relation => simp [hrelation] at hnone
      | inl hcoeff =>
          exact PSum.inr
            { query := query
              found := hfound
              covered := hcovered
              coefficients_eq := hcoeff }

/-- A malicious adaptive online-AGM computation over the Halo2 transcript domain. -/
abbrev AdaptiveOnlineAGMComp {shape : Shape}
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (α : Type*) :=
  LabeledOracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicTranscriptQuery (F := Fp) basis) α

/-- Retained query annotations from one concrete adaptive online-AGM execution. -/
abbrev AdaptiveOnlineAGMAnnotationLog {shape : Shape}
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :=
  List (LabeledOracleComp.QueryAnnotation
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k))
    (AlgebraicTranscriptQuery (F := Fp) basis))

/-- The bare bounded adaptive online-AGM family.  No execution cuts or freshness proofs are fields:
the adversary may make arbitrary malicious random-oracle queries, and every query carries the AGM
representations fixed at that query. -/
structure ComputedAdaptiveOnlineAGMFSFamily (shape : Shape) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    Fin shape.numProofs → ℕ → VestaG
  fixedRepresentations : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    List (AlgebraicPoint (F := Fp) basis)
  /-- Public-instance commitments are verifier-known AGM points available before every squeeze. -/
  instanceRepresented : ∀ basis (p : Fin shape.numProofs) i,
    (∃ rotation, (i, rotation) ∈ (vk basis).instanceQueryLayout) →
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = instanceCommitment basis p i
  /-- Fixed-column commitments are verifier-known AGM points available before every squeeze. -/
  fixedRepresented : ∀ basis i,
    (∃ rotation, (i, rotation) ∈ (vk basis).fixedQueryLayout) →
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (vk basis).fixedCommitment i
  /-- Common permutation commitments are likewise part of the verifier-known source. -/
  permutationCommonRepresented : ∀ basis (c : Fin shape.numPermutationColumns),
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (vk basis).permutationCommonCommitment c
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    AdaptiveOnlineAGMComp init basis
      (OnlineMemberProofData (vk := vk basis)
        (instanceCommitment := instanceCommitment basis) basis (fixedRepresentations basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAdaptiveOnlineAGMFSFamily

variable {shape : Shape}

/-- Every retained output/annotation execution has at most the family's declared `Q` visited
query nodes.  Cached provenance lookup performs no further oracle calls. -/
theorem runWithAnnotations_log_length_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    ((family.adversary basis).runWithAnnotations O).2.length ≤ family.Q :=
  LabeledOracleComp.runWithAnnotations_log_length_le
    (family.adversary basis) (family.queryBound basis) O

/-- Forget only the per-query AGM annotations and assemble the canonical online-member family.
The erased random-oracle computation has definitionally the same outputs and query budget. -/
def toOnlineMemberFamily (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    ComputedOnlineMemberFSFamily shape :=
  ComputedOnlineMemberFSFamily.ofProofData family.init family.vk family.instanceCommitment
    family.fixedRepresentations (fun basis => (family.adversary basis).erase) family.Q
    family.queryBound

/-- Forget member coverage as well, yielding the existing arbitrary-query algebraic family. -/
abbrev toFamily (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toOnlineMemberFamily.toFamily

@[simp] theorem toOnlineMemberFamily_Q (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    family.toOnlineMemberFamily.Q = family.Q := rfl

@[simp] theorem toFamily_Q (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    family.toFamily.Q = family.Q := rfl

/-- Return the first relation produced by a finite list of executable checks.  This shared
accounting helper is independent of any particular adaptive reduction. -/
def firstAdaptiveRelation? {basis : AugmentedIndex (2 ^ shape.k) → VestaG} :
    List (Option (AlgebraicRelationWitness (F := Fp) basis)) →
      Option (AlgebraicRelationWitness (F := Fp) basis)
  | [] => none
  | some relation :: _ => some relation
  | none :: rest => firstAdaptiveRelation? rest

@[simp] theorem firstAdaptiveRelation?_eq_none_iff
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (checks : List (Option (AlgebraicRelationWitness (F := Fp) basis))) :
    firstAdaptiveRelation? checks = none ↔ ∀ check ∈ checks, check = none := by
  induction checks with
  | nil => simp [firstAdaptiveRelation?]
  | cons check rest ih =>
      cases check <;> simp [firstAdaptiveRelation?, ih]

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
