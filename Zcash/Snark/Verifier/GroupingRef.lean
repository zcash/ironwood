import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Verifier.Assemble

/-!
# The reference grouping: `constructIntermediateSets` naturality

`constructIntermediateSets` (the multiopen grouping) branches only on the *equality pattern* of
the query points and on the slot identities — never on the field or group payloads. This module
makes that a theorem: the grouping of any query list is determined, positionally and with full
provenance, by the grouping of its **reference** — the same list with every point replaced by
its first-appearance class index and every payload replaced by its flat position
(`refQueries`).

* `refQueries qs` — query `n` becomes `⟨cisPIdx qs qs[n].point, .point n, n, qs[n].commId⟩` over
  the carriers `F := ℕ`, `G := ℕ`: points are class indices, evals and commitments are flat
  positions, slot identities are preserved.
* `constructIntermediateSets_ref_ids` / `_ref_points` / `_ref_sets` — the grouping's three views
  are decoded positionally from the reference grouping: `ids` verbatim, `points` through the
  class table `cisPts qs`, `sets` through `decodeMember qs` (flat positions back to the original
  commitments and claimed evaluations).
* `hasDuplicateCommitmentPoint_ref` — the duplicate-query rejection is likewise reference-level.

The coefficient walk consumes these with the closed-form reference table of `assembleQueries`
(`Fingerprint/Rational/GroupingTable.lean`): on the good event the reference is a fixed
verifying-key constant, so the grouping of every good sample point is one combinatorial object
and the assembled coefficients become rational functions of the point.

The proofs run each internal stage of the grouping (`cisPts`/`cisPIdx`/`cisComms`/`cisData`/
`cisSetList`/`cisRouted`, the de-privatized mirrors in `Verifier/Assemble.lean`) over the common
index spine `List.range qs.length`, transporting a per-stage correspondence. The first-appearance
dedup folds are handled once, generically (`dedupFold`).
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- A default commitment reference, for `getD` lookups. -/
instance {k : ℕ} {F G : Type*} [Inhabited G] : Inhabited (CommitmentRef k F G) :=
  ⟨.point default⟩

/-- A default query, for `getD` lookups: the zero point and evaluation on a default commitment. -/
instance {k : ℕ} {F G : Type*} [Zero F] [Inhabited G] : Inhabited (VerifierQuery k F G) :=
  ⟨⟨0, default, 0, .vanishingH⟩⟩

/-! ## The first-appearance dedup fold, generically -/

/-- First-appearance deduplication: keep each value's first occurrence, in order. The grouping's
distinct-point list (`cisPts`) and distinct-index-set list (`cisSetList`) are both instances, as
is the rotation-class table of `Fingerprint/Rational/GroupingTable.lean`. (Mathlib's `List.dedup`
keeps *last* occurrences, so it does not fit.) -/
def dedupFold {α : Type*} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- `cisPts` is the dedup fold of the point stream. -/
theorem cisPts_eq_dedupFold {k : ℕ} {F G : Type*} [DecidableEq F]
    (qs : List (VerifierQuery k F G)) :
    cisPts qs = dedupFold (qs.map (·.point)) := by
  rw [cisPts, dedupFold, List.foldl_map]

/-- Membership in the dedup fold is membership in the source (workhorse, accumulator form). -/
theorem mem_dedupFold_foldl {α : Type*} [DecidableEq α] (l : List α) :
    ∀ (init : List α) (x : α),
      x ∈ l.foldl (fun acc a => if a ∈ acc then acc else acc ++ [a]) init ↔ x ∈ init ∨ x ∈ l := by
  induction l with
  | nil => intro init x; simp
  | cons a t ih =>
    intro init x
    rw [List.foldl_cons]
    by_cases h : a ∈ init
    · rw [if_pos h, ih]
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem _ hx)
      · rintro (hx | hx)
        · exact Or.inl hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl h
          · exact Or.inr hx
    · rw [if_neg h, ih]
      constructor
      · rintro (hx | hx)
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hx)))
        · exact Or.inr (List.mem_cons_of_mem _ hx)
      · rintro (hx | hx)
        · exact Or.inl (List.mem_append.mpr (Or.inl hx))
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          · exact Or.inr hx

/-- Membership in the dedup fold is membership in the source. -/
theorem mem_dedupFold {α : Type*} [DecidableEq α] {l : List α} {x : α} :
    x ∈ dedupFold l ↔ x ∈ l := by
  rw [dedupFold, mem_dedupFold_foldl]
  simp

/-- The dedup fold has no duplicates. -/
theorem dedupFold_nodup {α : Type*} [DecidableEq α] (l : List α) : (dedupFold l).Nodup := by
  have h := nodup_dedup_foldl l id [] List.nodup_nil
  simpa [dedupFold] using h

/-- The dedup fold commutes with a map that is injective on the source (workhorse form:
accumulators related by the map, with all accumulated values drawn from the source). -/
theorem dedupFold_map_foldl {α β : Type*} [DecidableEq α] [DecidableEq β] (φ : α → β)
    (src : List α) (hinj : ∀ a ∈ src, ∀ b ∈ src, φ a = φ b → a = b) :
    ∀ (l : List α), (∀ a ∈ l, a ∈ src) →
      ∀ (init : List α), (∀ a ∈ init, a ∈ src) →
        (l.map φ).foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) (init.map φ)
          = (l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) init).map φ := by
  intro l
  induction l with
  | nil => intro _ init _; simp
  | cons a t ih =>
    intro hl init hinit
    have ha : a ∈ src := hl a List.mem_cons_self
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hmem : φ a ∈ init.map φ ↔ a ∈ init := by
      constructor
      · intro h
        obtain ⟨b, hb, hba⟩ := List.mem_map.mp h
        exact (hinj b (hinit b hb) a ha hba) ▸ hb
      · intro h
        exact List.mem_map.mpr ⟨a, h, rfl⟩
    by_cases h : a ∈ init
    · rw [if_pos (hmem.mpr h), if_pos h]
      exact ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) init hinit
    · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h,
        show List.map φ init ++ [φ a] = List.map φ (init ++ [a]) by simp]
      refine ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (init ++ [a]) ?_
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hinit b hb
      · exact (List.mem_singleton.mp hb) ▸ ha

/-- The dedup fold commutes with a map injective on the source. -/
theorem dedupFold_map {α β : Type*} [DecidableEq α] [DecidableEq β] (φ : α → β) (l : List α)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, φ a = φ b → a = b) :
    dedupFold (l.map φ) = (dedupFold l).map φ := by
  simpa [dedupFold] using
    dedupFold_map_foldl φ l hinj l (fun a ha => ha) [] (by simp)

/-- `findIdx` of a present element commutes with a map injective on the list. -/
theorem findIdx_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] (φ : α → β) (l : List α)
    {x : α} (hx : x ∈ l) (hinj : ∀ a ∈ l, φ a = φ x → a = x) :
    (l.map φ).findIdx (fun y => decide (y = φ x)) = l.findIdx (fun y => decide (y = x)) := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a t ih =>
    rw [List.map_cons, List.findIdx_cons, List.findIdx_cons]
    by_cases h : a = x
    · subst h
      simp
    · have hφ : ¬ (φ a = φ x) := fun hc => h (hinj a List.mem_cons_self hc)
      rw [decide_eq_false hφ, decide_eq_false h]
      simp only [Bool.cond_false]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd rfl h
      · rw [ih hx' (fun b hb => hinj b (List.mem_cons_of_mem _ hb))]

/-- In a duplicate-free list, `findIdx` of the `j`-th element is `j`. -/
theorem findIdx_getElem_of_nodup {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {j : ℕ} (hj : j < l.length) :
    l.findIdx (fun y => decide (y = l[j])) = j := by
  have hmem : l[j] ∈ l := List.getElem_mem hj
  have h1 := getElem?_findIdx_self hmem
  have hlt : l.findIdx (fun y => decide (y = l[j])) < l.length :=
    List.findIdx_lt_length_of_exists ⟨l[j], hmem, by simp⟩
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h1
  exact List.Nodup.getElem_inj_iff hnd |>.mp h1

/-! ## The point-class toolkit -/

section PointClasses

variable {k : ℕ} {F G : Type*} [DecidableEq F]

/-- Every query's point appears in the distinct-point table. -/
theorem point_mem_cisPts {qs : List (VerifierQuery k F G)} {q : VerifierQuery k F G}
    (hq : q ∈ qs) : q.point ∈ cisPts qs :=
  mem_dedup_foldl qs (·.point) [] hq

/-- The distinct-point table has no duplicates. -/
theorem cisPts_nodup (qs : List (VerifierQuery k F G)) : (cisPts qs).Nodup := by
  rw [cisPts_eq_dedupFold]
  exact dedupFold_nodup _

/-- A present point's class index is in range. -/
theorem cisPIdx_lt_of_mem {qs : List (VerifierQuery k F G)} {p : F} (hp : p ∈ cisPts qs) :
    cisPIdx qs p < (cisPts qs).length :=
  List.findIdx_lt_length_of_exists ⟨p, hp, by simp⟩

/-- The class table retrieves a present point at its class index. -/
theorem cisPts_getD_cisPIdx {qs : List (VerifierQuery k F G)} {p : F} (d : F)
    (hp : p ∈ cisPts qs) : (cisPts qs).getD (cisPIdx qs p) d = p := by
  have h := getElem?_findIdx_self hp
  rw [List.getD_eq_getElem?_getD, cisPIdx, h, Option.getD_some]

/-- Class indices are injective on present points. -/
theorem cisPIdx_inj {qs : List (VerifierQuery k F G)} {p₁ p₂ : F} (h₁ : p₁ ∈ cisPts qs)
    (h₂ : p₂ ∈ cisPts qs) (h : cisPIdx qs p₁ = cisPIdx qs p₂) : p₁ = p₂ := by
  have e₁ := cisPts_getD_cisPIdx (qs := qs) p₂ h₁
  rw [h] at e₁
  exact e₁.symm.trans (cisPts_getD_cisPIdx (qs := qs) p₂ h₂)

/-- The class index of the `j`-th distinct point is `j`. -/
theorem cisPIdx_getElem {qs : List (VerifierQuery k F G)} {j : ℕ}
    (hj : j < (cisPts qs).length) : cisPIdx qs (cisPts qs)[j] = j :=
  findIdx_getElem_of_nodup (cisPts_nodup qs) hj

/-- A point of the query stream is in the distinct-point table. -/
theorem mem_cisPts_of_mem_stream {qs : List (VerifierQuery k F G)} {p : F}
    (hp : p ∈ qs.map (·.point)) : p ∈ cisPts qs := by
  rw [cisPts_eq_dedupFold, mem_dedupFold]
  exact hp

end PointClasses

/-! ## The reference query list -/

section RefQueries

variable {k : ℕ} {F G : Type*} [DecidableEq F] [Zero F] [Inhabited G]

/-- The reference of a query list: query `n` keeps its slot identity, its point becomes its
first-appearance class index, and its commitment and evaluation become the flat position `n` —
over the carriers `F := ℕ`, `G := ℕ`. Reference point equality is point-class equality of the
originals, and every payload names its source position, so the grouping of the reference
determines the grouping of the original with full provenance. -/
def refQueries (qs : List (VerifierQuery k F G)) : List (VerifierQuery k ℕ ℕ) :=
  (List.range qs.length).map fun n =>
    { point := cisPIdx qs (qs.getD n default).point
      commitment := .point n
      eval := n
      commId := (qs.getD n default).commId }

@[simp] theorem refQueries_length (qs : List (VerifierQuery k F G)) :
    (refQueries qs).length = qs.length := by
  simp [refQueries]

theorem refQueries_getElem (qs : List (VerifierQuery k F G)) {n : ℕ}
    (hn : n < (refQueries qs).length) :
    (refQueries qs)[n]
      = ⟨cisPIdx qs (qs.getD n default).point, .point n, n, (qs.getD n default).commId⟩ := by
  simp [refQueries]

/-- The reference preserves the slot-identity stream positionally. -/
theorem refQueries_map_commId (qs : List (VerifierQuery k F G)) :
    (refQueries qs).map (·.commId) = qs.map (·.commId) := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp only [List.length_map, refQueries_length] at h1
  simp only [refQueries, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, Option.getD_some]

/-- The reference's point stream is the original's, classed. -/
theorem refQueries_map_point (qs : List (VerifierQuery k F G)) :
    (refQueries qs).map (·.point) = (qs.map (·.point)).map (cisPIdx qs) := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp only [List.length_map, refQueries_length] at h1
  simp only [refQueries, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, Option.getD_some]

/-- The reference's distinct-point table is the original's, classed. -/
theorem cisPts_ref (qs : List (VerifierQuery k F G)) :
    cisPts (refQueries qs) = (cisPts qs).map (cisPIdx qs) := by
  have hinj : ∀ a ∈ qs.map (·.point), ∀ b ∈ qs.map (·.point),
      cisPIdx qs a = cisPIdx qs b → a = b := fun a ha b hb hab =>
    cisPIdx_inj (mem_cisPts_of_mem_stream ha) (mem_cisPts_of_mem_stream hb) hab
  rw [cisPts_eq_dedupFold, cisPts_eq_dedupFold (qs := qs), refQueries_map_point,
    dedupFold_map _ _ hinj]

/-- The reference's distinct-point table is an initial segment of `ℕ`: class `j` sits at
position `j`. -/
theorem cisPts_ref_range (qs : List (VerifierQuery k F G)) :
    cisPts (refQueries qs) = List.range (cisPts qs).length := by
  rw [cisPts_ref]
  refine List.ext_getElem (by simp) ?_
  intro j h1 h2
  simp only [List.length_map] at h1
  simp only [List.getElem_map, List.getElem_range]
  exact cisPIdx_getElem h1

/-- Reference class indices are fixed points: the class of class `v` is `v`. -/
theorem cisPIdx_ref_lt (qs : List (VerifierQuery k F G)) {v : ℕ}
    (hv : v < (cisPts qs).length) : cisPIdx (refQueries qs) v = v := by
  rw [cisPIdx, cisPts_ref_range]
  have h := findIdx_getElem_of_nodup (List.nodup_range (n := (cisPts qs).length))
    (j := v) (by simpa using hv)
  simpa using h

/-- Reference class indices fix every present point's class. -/
theorem cisPIdx_ref_point (qs : List (VerifierQuery k F G)) {q : VerifierQuery k F G}
    (hq : q ∈ qs) : cisPIdx (refQueries qs) (cisPIdx qs q.point) = cisPIdx qs q.point :=
  cisPIdx_ref_lt qs (cisPIdx_lt_of_mem (point_mem_cisPts hq))

/-- A list is the `getD` image of its index range. -/
theorem self_eq_range_map_getD {α : Type*} [Inhabited α] (l : List α) :
    l = (List.range l.length).map (fun n => l.getD n default) := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-! ## The keyed commitment stage -/

/-- Correspondence between a distinct-commitment entry and its reference: both carry the slot
identity and provenance of one source position, whose commitment the reference names as the
flat index. -/
def RefCommEntry (qs : List (VerifierQuery k F G)) :
    CommitmentId × CommitmentRef k F G → CommitmentId × CommitmentRef k ℕ ℕ → Prop :=
  fun e₁ e₂ => ∃ n < qs.length,
    e₁ = ((qs.getD n default).commId, (qs.getD n default).commitment)
      ∧ e₂ = ((qs.getD n default).commId, .point n)

omit [DecidableEq F] in
theorem RefCommEntry.fst_eq {qs : List (VerifierQuery k F G)}
    {e₁ : CommitmentId × CommitmentRef k F G} {e₂ : CommitmentId × CommitmentRef k ℕ ℕ}
    (h : RefCommEntry qs e₁ e₂) : e₁.1 = e₂.1 := by
  obtain ⟨n, _, rfl, rfl⟩ := h
  rfl

omit [DecidableEq F] in
/-- Related accumulators answer the keyed-dedup membership test identically. -/
theorem forall₂_any_fst {qs : List (VerifierQuery k F G)}
    {acc₁ : List (CommitmentId × CommitmentRef k F G)}
    {acc₂ : List (CommitmentId × CommitmentRef k ℕ ℕ)}
    (h : List.Forall₂ (RefCommEntry qs) acc₁ acc₂) (cid : CommitmentId) :
    acc₁.any (fun c => decide (c.1 = cid)) = acc₂.any (fun c => decide (c.1 = cid)) := by
  induction h with
  | nil => rfl
  | cons hR _ ih => simp only [List.any_cons, hR.fst_eq, ih]

omit [DecidableEq F] in
/-- The keyed dedup folds of a list and its reference correspond entry-for-entry (workhorse:
common index spine, related accumulators). -/
theorem cisComms_ref_foldl (qs : List (VerifierQuery k F G)) :
    ∀ (l : List ℕ),
      ∀ (acc₁ : List (CommitmentId × CommitmentRef k F G))
        (acc₂ : List (CommitmentId × CommitmentRef k ℕ ℕ)),
        List.Forall₂ (RefCommEntry qs) acc₁ acc₂ → (∀ n ∈ l, n < qs.length) →
        List.Forall₂ (RefCommEntry qs)
          (l.foldl (fun acc n =>
            if acc.any (fun c => decide (c.1 = (qs.getD n default).commId)) then acc
            else acc ++ [((qs.getD n default).commId, (qs.getD n default).commitment)]) acc₁)
          (l.foldl (fun acc n =>
            if acc.any (fun c => decide (c.1 = (qs.getD n default).commId)) then acc
            else acc ++ [((qs.getD n default).commId, .point n)]) acc₂) := by
  intro l
  induction l with
  | nil => intro acc₁ acc₂ hacc _; simpa using hacc
  | cons a t ih =>
    intro acc₁ acc₂ hacc hl
    rw [List.foldl_cons, List.foldl_cons,
      forall₂_any_fst hacc ((qs.getD a default).commId)]
    by_cases h : acc₂.any (fun c => decide (c.1 = (qs.getD a default).commId)) = true
    · rw [if_pos h, if_pos h]
      exact ih acc₁ acc₂ hacc (fun n hn => hl n (List.mem_cons_of_mem _ hn))
    · rw [if_neg h, if_neg h]
      refine ih _ _ ?_ (fun n hn => hl n (List.mem_cons_of_mem _ hn))
      exact List.rel_append hacc
        (List.Forall₂.cons ⟨a, hl a List.mem_cons_self, rfl, rfl⟩ List.Forall₂.nil)

/-- The distinct-commitment tables of a list and its reference correspond entry-for-entry. -/
theorem cisComms_ref (qs : List (VerifierQuery k F G)) :
    List.Forall₂ (RefCommEntry qs) (cisComms qs) (cisComms (refQueries qs)) := by
  have h1 : cisComms qs
      = (List.range qs.length).foldl (fun acc n =>
          if acc.any (fun c => decide (c.1 = (qs.getD n default).commId)) then acc
          else acc ++ [((qs.getD n default).commId, (qs.getD n default).commitment)]) [] := by
    conv_lhs => rw [cisComms, self_eq_range_map_getD qs]
    rw [List.foldl_map]
  have h2 : cisComms (refQueries qs)
      = (List.range qs.length).foldl (fun acc n =>
          if acc.any (fun c => decide (c.1 = (qs.getD n default).commId)) then acc
          else acc ++ [((qs.getD n default).commId, .point n)]) [] := by
    rw [cisComms, refQueries, List.foldl_map]
  rw [h1, h2]
  exact cisComms_ref_foldl qs (List.range qs.length) [] [] List.Forall₂.nil
    (fun n hn => List.mem_range.mp hn)

/-! ## The per-commitment data stage -/

/-- `find?` depends only on the predicate's values on the list. -/
theorem find?_congr_mem {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Map a `Forall₂` through functions that respect the relation. -/
theorem forall₂_map_map {α β γ δ : Type*} {R : α → β → Prop} {R' : γ → δ → Prop} {f : α → γ}
    {g : β → δ} : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, R a b → R' (f a) (g b)) → List.Forall₂ R' (l₁.map f) (l₂.map g) := by
  intro l₁ l₂ h hRR'
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRR' _ _ hab) ih

/-- Project equal components out of a `Forall₂`. -/
theorem forall₂_map_eq {α β γ : Type*} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      l₁.map f = l₂.map g := by
  intro l₁ l₂ h hfg
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hfg _ _ hab, ih]

/-- The source positions holding a given slot identity. Filters of the list and of its
reference by a slot identity are both images of this position list. -/
def commPositions (qs : List (VerifierQuery k F G)) (cid : CommitmentId) : List ℕ :=
  (List.range qs.length).filter fun n => decide ((qs.getD n default).commId = cid)

omit [DecidableEq F] in
theorem mem_commPositions_lt {qs : List (VerifierQuery k F G)} {cid : CommitmentId} {n : ℕ}
    (hn : n ∈ commPositions qs cid) : n < qs.length :=
  List.mem_range.mp (List.mem_filter.mp hn).1

omit [DecidableEq F] in
theorem getD_mem_of_lt {qs : List (VerifierQuery k F G)} {n : ℕ} (hn : n < qs.length) :
    qs.getD n default ∈ qs := by
  rw [List.getD_eq_getElem qs default hn]
  exact List.getElem_mem hn

omit [DecidableEq F] in
/-- Filtering by a slot identity is the `getD` image of the identity's positions. -/
theorem filter_commId_eq (qs : List (VerifierQuery k F G)) (cid : CommitmentId) :
    qs.filter (fun q => decide (q.commId = cid))
      = (commPositions qs cid).map (fun n => qs.getD n default) := by
  conv_lhs => rw [self_eq_range_map_getD qs]
  rw [List.filter_map]
  rfl

/-- Filtering the reference by a slot identity is the reference image of the same positions. -/
theorem filter_ref_commId_eq (qs : List (VerifierQuery k F G)) (cid : CommitmentId) :
    (refQueries qs).filter (fun q => decide (q.commId = cid))
      = (commPositions qs cid).map (fun n =>
          (⟨cisPIdx qs (qs.getD n default).point, .point n, n, (qs.getD n default).commId⟩ :
            VerifierQuery k ℕ ℕ)) := by
  rw [refQueries, List.filter_map]
  rfl

/-- The class-index streams of the two filtered lists agree. -/
theorem filter_idxs_ref_eq (qs : List (VerifierQuery k F G)) (cid : CommitmentId) :
    ((refQueries qs).filter (fun q => decide (q.commId = cid))).map
        (fun q => cisPIdx (refQueries qs) q.point)
      = (qs.filter (fun q => decide (q.commId = cid))).map (fun q => cisPIdx qs q.point) := by
  rw [filter_ref_commId_eq, filter_commId_eq, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro n hn
  have hmem : qs.getD n default ∈ qs := getD_mem_of_lt (mem_commPositions_lt hn)
  exact cisPIdx_ref_point qs hmem

/-- The two filtered `find?`s locate the same source position (original side). -/
theorem filter_find?_eq (qs : List (VerifierQuery k F G)) (cid : CommitmentId) (i : ℕ) :
    (qs.filter (fun q => decide (q.commId = cid))).find?
        (fun q => decide (cisPIdx qs q.point = i))
      = ((commPositions qs cid).find?
          (fun n => decide (cisPIdx qs (qs.getD n default).point = i))).map
          (fun n => qs.getD n default) := by
  rw [filter_commId_eq, List.find?_map]
  rfl

/-- The two filtered `find?`s locate the same source position (reference side). -/
theorem filter_ref_find?_eq (qs : List (VerifierQuery k F G)) (cid : CommitmentId) (i : ℕ) :
    ((refQueries qs).filter (fun q => decide (q.commId = cid))).find?
        (fun q => decide (cisPIdx (refQueries qs) q.point = i))
      = ((commPositions qs cid).find?
          (fun n => decide (cisPIdx qs (qs.getD n default).point = i))).map
          (fun n =>
            (⟨cisPIdx qs (qs.getD n default).point, .point n, n, (qs.getD n default).commId⟩ :
              VerifierQuery k ℕ ℕ)) := by
  rw [filter_ref_commId_eq, List.find?_map]
  refine congrArg _ (find?_congr_mem ?_)
  intro n hn
  have hmem : qs.getD n default ∈ qs := getD_mem_of_lt (mem_commPositions_lt hn)
  simp only [Function.comp_apply]
  rw [cisPIdx_ref_point qs hmem]

/-- Correspondence between a per-commitment data entry and its reference: same slot identity and
index set, commitment provenance as in `RefCommEntry`, and the original's eval vector decoded
positionally from the reference's (which carries flat source positions). -/
def RefDataEntry (qs : List (VerifierQuery k F G)) :
    CommitmentId × CommitmentRef k F G × List ℕ × List F →
    CommitmentId × CommitmentRef k ℕ ℕ × List ℕ × List ℕ → Prop :=
  fun d₁ d₂ =>
    d₁.1 = d₂.1
      ∧ RefCommEntry qs (d₁.1, d₁.2.1) (d₂.1, d₂.2.1)
      ∧ d₁.2.2.1 = d₂.2.2.1
      ∧ (∀ n ∈ d₂.2.2.2, n < qs.length)
      ∧ d₁.2.2.2 = d₂.2.2.2.map (fun n => (qs.getD n default).eval)

/-- The per-commitment data tables of a list and its reference correspond entry-for-entry. -/
theorem cisData_ref (qs : List (VerifierQuery k F G)) :
    List.Forall₂ (RefDataEntry qs) (cisData qs) (cisData (refQueries qs)) := by
  rw [cisData, cisData]
  refine forall₂_map_map (cisComms_ref qs) ?_
  intro e₁ e₂ hR
  obtain ⟨n, hn, he₁, he₂⟩ := hR
  subst he₁ he₂
  have hidxs := filter_idxs_ref_eq qs (qs.getD n default).commId
  have hlen : (cisPts (refQueries qs)).length = (cisPts qs).length := by
    rw [cisPts_ref_range, List.length_range]
  refine ⟨rfl, ⟨n, hn, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [hlen, hidxs]
  · intro m hm
    obtain ⟨i, _, hfind⟩ := List.mem_filterMap.mp hm
    rw [filter_ref_find?_eq] at hfind
    rcases hspine : (commPositions qs (qs.getD n default).commId).find?
        (fun n' => decide (cisPIdx qs (qs.getD n' default).point = i)) with _ | n'
    · rw [hspine, Option.map_none, Option.map_none] at hfind
      exact absurd hfind (by simp)
    · rw [hspine, Option.map_some, Option.map_some] at hfind
      have hm' : m = n' := by simpa using (Option.some.inj hfind).symm
      have hlt := mem_commPositions_lt (List.mem_of_find?_eq_some hspine)
      omega
  · simp only [hidxs, hlen]
    rw [List.map_filterMap]
    refine List.filterMap_congr ?_
    intro i _
    rw [filter_find?_eq, filter_ref_find?_eq]
    simp only [Option.map_map]
    congr 1

/-! ## The set-list and routing stages -/

omit [Zero F] [Inhabited G] in
/-- The distinct-index-set fold is the dedup fold of the index-set stream. -/
theorem cisSetList_eq_dedupFold (qs : List (VerifierQuery k F G)) :
    cisSetList qs = dedupFold ((cisData qs).map (·.2.2.1)) := by
  rw [cisSetList, dedupFold, List.foldl_map]
  congr 1
  funext acc cd
  by_cases h : cd.2.2.1 ∈ acc
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The reference has the same distinct point-index sets. -/
theorem cisSetList_ref (qs : List (VerifierQuery k F G)) :
    cisSetList (refQueries qs) = cisSetList qs := by
  rw [cisSetList_eq_dedupFold, cisSetList_eq_dedupFold]
  congr 1
  exact (forall₂_map_eq (cisData_ref qs) (fun a b hab => hab.2.2.1)).symm

omit [DecidableEq F] in
/-- Filter a `Forall₂` by predicates that agree on related pairs. -/
theorem forall₂_filter {α β : Type*} {R : α → β → Prop} {p : α → Bool} {q : β → Bool} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → p a = q b) →
      List.Forall₂ R (l₁.filter p) (l₂.filter q) := by
  intro l₁ l₂ h hpq
  induction h with
  | nil => exact .nil
  | @cons a b t₁ t₂ hab htail ih =>
    rw [List.filter_cons, List.filter_cons, ← hpq _ _ hab]
    by_cases hp : p a = true
    · rw [if_pos hp, if_pos hp]
      exact .cons hab ih
    · rw [if_neg hp, if_neg hp]
      exact ih

/-- The routed member lists of a list and its reference correspond entry-for-entry. -/
theorem cisRouted_ref (qs : List (VerifierQuery k F G)) (si : ℕ) :
    List.Forall₂ (RefDataEntry qs) (cisRouted qs si) (cisRouted (refQueries qs) si) := by
  rw [cisRouted, cisRouted]
  refine forall₂_filter (List.rel_reverse (cisData_ref qs)) ?_
  intro a b hab
  rw [hab.2.2.1, cisSetList_ref]

/-! ## The public naturality theorems -/

/-- Decode a reference grouping member back to the original carriers: the commitment at the flat
position it names, and the claimed evaluations at the flat positions its eval list names. The
`.msm` branch is unreachable on `refQueries` output (every reference commitment is a flat
position). -/
def decodeMember (qs : List (VerifierQuery k F G)) :
    CommitmentRef k ℕ ℕ × List ℕ → CommitmentRef k F G × List F
  | (.point n, ns) => ((qs.getD n default).commitment, ns.map fun m => (qs.getD m default).eval)
  | (.msm _, ns) => (default, ns.map fun m => (qs.getD m default).eval)

/-- **Naturality, `ids` view.** The grouping's slot identities are reference-level. -/
theorem constructIntermediateSets_ref_ids [DecidableEq G] (qs : List (VerifierQuery k F G)) :
    (constructIntermediateSets qs).ids = (constructIntermediateSets (refQueries qs)).ids := by
  show (List.range (cisSetList qs).length).map (fun si => (cisRouted qs si).map (·.1))
    = (List.range (cisSetList (refQueries qs)).length).map
        (fun si => (cisRouted (refQueries qs) si).map (·.1))
  rw [cisSetList_ref]
  refine List.map_congr_left ?_
  intro si _
  exact forall₂_map_eq (cisRouted_ref qs si) (fun a b hab => hab.1)

/-- **Naturality, `points` view.** The grouping's point lists are the reference grouping's class
lists, decoded through the distinct-point table. -/
theorem constructIntermediateSets_ref_points [DecidableEq G] (qs : List (VerifierQuery k F G)) :
    (constructIntermediateSets qs).points
      = ((constructIntermediateSets (refQueries qs)).points).map
          (List.map fun i => (cisPts qs).getD i 0) := by
  show (cisSetList qs).map (fun s => s.filterMap (fun i => (cisPts qs)[i]?))
    = ((cisSetList (refQueries qs)).map
        (fun s => s.filterMap (fun i => (cisPts (refQueries qs))[i]?))).map
        (List.map fun i => (cisPts qs).getD i 0)
  rw [cisSetList_ref, List.map_map]
  refine List.map_congr_left ?_
  intro s _
  simp only [Function.comp_apply, cisPts_ref_range, List.map_filterMap]
  refine List.filterMap_congr ?_
  intro i _
  rcases lt_or_ge i (cisPts qs).length with hi | hi
  · rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by simpa using hi),
      Option.map_some, List.getElem_range, List.getD_eq_getElem _ _ hi]
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by simpa using hi),
      Option.map_none]

/-- **Naturality, `sets` view.** The grouping's member lists are the reference grouping's,
decoded positionally: commitments and claimed evaluations are read back off the flat positions
the reference retains. -/
theorem constructIntermediateSets_ref_sets [DecidableEq G] (qs : List (VerifierQuery k F G)) :
    (constructIntermediateSets qs).sets
      = ((constructIntermediateSets (refQueries qs)).sets).map (List.map (decodeMember qs)) := by
  show (List.range (cisSetList qs).length).map
      (fun si => (cisRouted qs si).map fun cd => (cd.2.1, cd.2.2.2))
    = ((List.range (cisSetList (refQueries qs)).length).map
        (fun si => (cisRouted (refQueries qs) si).map fun cd => (cd.2.1, cd.2.2.2))).map
        (List.map (decodeMember qs))
  rw [cisSetList_ref, List.map_map]
  refine List.map_congr_left ?_
  intro si _
  simp only [Function.comp_apply, List.map_map]
  refine forall₂_map_eq (cisRouted_ref qs si) ?_
  intro d₁ d₂ hd
  obtain ⟨-, hcomm, -, -, hevals⟩ := hd
  obtain ⟨n, hn, h₁, h₂⟩ := hcomm
  have h₁' : d₁.2.1 = (qs.getD n default).commitment := congrArg Prod.snd h₁
  have h₂' : d₂.2.1 = CommitmentRef.point n := congrArg Prod.snd h₂
  simp only [Function.comp_apply, h₂', decodeMember, h₁', hevals]

/-- The grouping has as many point sets as the reference grouping. -/
theorem constructIntermediateSets_ref_sets_length [DecidableEq G]
    (qs : List (VerifierQuery k F G)) :
    (constructIntermediateSets qs).sets.length
      = (constructIntermediateSets (refQueries qs)).sets.length := by
  rw [constructIntermediateSets_ref_sets, List.length_map]

/-! ## Duplicate detection is reference-level -/

/-- Pointwise relation between a query and its reference entry: preserved slot identity, classed
point, and presence of the point in the class table. -/
def RefQ (qs : List (VerifierQuery k F G)) :
    VerifierQuery k F G → VerifierQuery k ℕ ℕ → Prop :=
  fun q q' => q'.commId = q.commId ∧ q'.point = cisPIdx qs q.point ∧ q.point ∈ cisPts qs

/-- A query list and its reference are pointwise related. -/
theorem forall₂_refQ (qs : List (VerifierQuery k F G)) :
    List.Forall₂ (RefQ qs) qs (refQueries qs) := by
  refine List.forall₂_iff_get.mpr ⟨by simp, ?_⟩
  intro i h₁ h₂
  have href := refQueries_getElem qs (n := i) (by simpa using h₂)
  simp only [List.get_eq_getElem, href]
  exact ⟨by simp [List.getElem?_eq_getElem h₁], by simp [List.getElem?_eq_getElem h₁],
    point_mem_cisPts (List.getElem_mem h₁)⟩

omit [Zero F] [Inhabited G] in
/-- The duplicate test of one query against a tail is reference-level. -/
theorem any_dup_congr_refQ (qs : List (VerifierQuery k F G))
    {a : VerifierQuery k F G} {b : VerifierQuery k ℕ ℕ} (hab : RefQ qs a b) :
    ∀ {t₁ : List (VerifierQuery k F G)} {t₂ : List (VerifierQuery k ℕ ℕ)},
      List.Forall₂ (RefQ qs) t₁ t₂ →
      t₁.any (fun r => decide (r.commId = a.commId ∧ r.point = a.point))
        = t₂.any (fun r => decide (r.commId = b.commId ∧ r.point = b.point)) := by
  intro t₁ t₂ h
  induction h with
  | nil => rfl
  | cons hrr htail ih =>
    rename_i r r' _ _
    rw [List.any_cons, List.any_cons, ih]
    congr 1
    obtain ⟨hbc, hbp, hbm⟩ := hab
    obtain ⟨hrc, hrp, hrm⟩ := hrr
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hrc, hbc, hrp, hbp]
    constructor
    · rintro ⟨hc, hp⟩
      exact ⟨hc, by rw [hp]⟩
    · rintro ⟨hc, hp⟩
      exact ⟨hc, cisPIdx_inj hrm hbm hp⟩

/-- **Duplicate detection is reference-level.** -/
theorem hasDuplicateCommitmentPoint_ref (qs : List (VerifierQuery k F G)) :
    hasDuplicateCommitmentPoint qs = hasDuplicateCommitmentPoint (refQueries qs) := by
  have h : ∀ {l₁ : List (VerifierQuery k F G)} {l₂ : List (VerifierQuery k ℕ ℕ)},
      List.Forall₂ (RefQ qs) l₁ l₂ →
      hasDuplicateCommitmentPoint l₁ = hasDuplicateCommitmentPoint l₂ := by
    intro l₁ l₂ hl
    induction hl with
    | nil => rfl
    | cons hab htail ih =>
      simp only [hasDuplicateCommitmentPoint]
      rw [ih, any_dup_congr_refQ qs hab htail]
  exact h (forall₂_refQ qs)

end RefQueries

end Zcash.Snark
