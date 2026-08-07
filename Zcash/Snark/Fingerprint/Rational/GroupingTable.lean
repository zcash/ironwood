import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Verifier.GroupingRef
import Zcash.Snark.Fingerprint.Rational.GoodEvent

/-!
# The reference table of `assembleQueries`

On the good event, the multiopen grouping of the assembled queries is one fixed combinatorial
object. This module produces it: the flat slot-identity and rotation streams of
`assembleQueries` are verifying-key constants (`queryCommIds`, `queryRots` — the sample point
enters queries only through claimed evaluations, commitment payloads, and the uniform point
factor `x`), so the reference of the assembled query list (`refQueries`,
`Verifier/GroupingRef.lean`) collapses to the closed-form `refTable` whenever `x ≠ 0` and the
opened `ω`-powers are distinct (`refQueries_eq_refTable`). Combined with the naturality
theorems, every good sample point produces the same grouping shape, and `assemble?` succeeds
with a fixed `other`-length MSM (`assembleAt_some`).

`VkSymbolicFacts` collects the decidable verifying-key facts this needs — all `native_decide`
material at a captured key, hypotheses generically.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-! ## Stream helpers -/

/-- Mapping a zip through a first-component function is mapping the truncated first list. -/
theorem zip_map_fst {α β γ : Type*} (g : α → γ) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.zip l₂).map (fun e => g e.1) = (l₁.take l₂.length).map g := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a t ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b u => simp [ih u]

/-- A `filterMap` whose per-element option is always `some` and whose result ignores the
payload is a plain `map`. -/
theorem filterMap_map_const_of_isSome {α β γ : Type*} {l : List α} {g : α → Option β}
    {c : α → γ} (h : ∀ a ∈ l, (g a).isSome) :
    l.filterMap (fun a => (g a).map (fun _ => c a)) = l.map c := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    rcases hg : g a with _ | v
    · rw [hg] at ha
      simp at ha
    · simp only [List.filterMap_cons, hg, Option.map_some, List.map_cons]
      rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-! ## The closed-form streams -/

variable {G : Type*}

/-- One sub-proof's slot-identity stream, in the verifier's order: instance and advice columns
(layouts truncated to the claimed evaluation counts), permutation products at `x`/`xNext` per
set then `xLast` over the non-last sets in reverse, and the five per-lookup queries. -/
def perProofCommIds (shape : Shape) (vk : VerifyingKey shape Fp G) (p : ℕ) :
    List CommitmentId :=
  (vk.instanceQueryLayout.take shape.numInstanceQueries).map (fun e => .instanceCol p e.1)
    ++ (vk.adviceQueryLayout.take shape.numAdviceQueries).map (fun e => .adviceCol p e.1)
    ++ ((List.range shape.numPermutationSets).flatMap
          (fun s => [.permProduct p s, .permProduct p s])
        ++ ((List.range (shape.numPermutationSets - 1)).reverse).map (.permProduct p ·))
    ++ (List.range shape.numLookups).flatMap (fun l =>
        [.lookupProduct p l, .lookupPermInput p l, .lookupPermTable p l, .lookupPermInput p l,
          .lookupProduct p l])

/-- One sub-proof's rotation stream, aligned with `perProofCommIds`. -/
def perProofRots (shape : Shape) (vk : VerifyingKey shape Fp G) : List ℤ :=
  (vk.instanceQueryLayout.take shape.numInstanceQueries).map (·.2)
    ++ (vk.adviceQueryLayout.take shape.numAdviceQueries).map (·.2)
    ++ ((List.range shape.numPermutationSets).flatMap (fun _ => [(0 : ℤ), 1])
        ++ List.replicate (shape.numPermutationSets - 1)
            (-((vk.blindingFactors : ℤ) + 1)))
    ++ (List.range shape.numLookups).flatMap (fun _ => [(0 : ℤ), 0, 0, -1, 1])

/-- The full slot-identity stream of `assembleQueries`: per-sub-proof blocks, then the fixed
columns, the common permutation columns, and the two vanishing queries. -/
def queryCommIds (shape : Shape) (vk : VerifyingKey shape Fp G) : List CommitmentId :=
  ((List.range shape.numProofs).map (perProofCommIds shape vk)).flatten
    ++ (vk.fixedQueryLayout.take shape.numFixedQueries).map (fun e => .fixedCol e.1)
    ++ (List.range shape.numPermutationColumns).map .permCommon
    ++ [.vanishingH, .randomPoly]

/-- The full rotation stream of `assembleQueries`, aligned with `queryCommIds`. -/
def queryRots (shape : Shape) (vk : VerifyingKey shape Fp G) : List ℤ :=
  ((List.range shape.numProofs).map (fun _ => perProofRots shape vk)).flatten
    ++ (vk.fixedQueryLayout.take shape.numFixedQueries).map (·.2)
    ++ List.replicate shape.numPermutationColumns (0 : ℤ)
    ++ [(0 : ℤ), 0]

/-! ## Builder stream lemmas -/

/-- Mapping a zip through a second-component function is mapping the truncated second list. -/
theorem zip_map_snd {α β γ : Type*} (g : β → γ) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.zip l₂).map (fun e => g e.2) = (l₂.take l₁.length).map g := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a t ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b u => simp [ih u]

/-- Flat-mapping a zip through a second-component function is flat-mapping the truncated second
list. -/
theorem zip_flatMap_snd {α β γ : Type*} (g : β → List γ) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.zip l₂).flatMap (fun e => g e.2) = (l₂.take l₁.length).flatMap g := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a t ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b u => simp [ih u]

/-- `ofFn` as a range map, given a value-level description. -/
theorem ofFn_eq_range_map {α : Type*} {n : ℕ} (g : Fin n → α) (f : ℕ → α)
    (h : ∀ i : Fin n, g i = f i.val) : List.ofFn g = (List.range n).map f := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

section Builders

variable {shape : Shape}

/-- `columnQueries` slot identities: the truncated layout's columns. -/
theorem columnQueries_map_commId {k : ℕ} (omega x : Fp) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List Fp) :
    (columnQueries (k := k) omega x commitment mkId layout evals).map (·.commId)
      = (layout.take evals.length).map (fun e => mkId e.1) := by
  rw [columnQueries, List.map_map, ← zip_map_fst (fun e => mkId e.1) layout evals]
  rfl

/-- `columnQueries` points: the truncated layout's rotations of `x`. -/
theorem columnQueries_map_point {k : ℕ} (omega x : Fp) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List Fp) :
    (columnQueries (k := k) omega x commitment mkId layout evals).map (·.point)
      = ((layout.take evals.length).map (·.2)).map (fun r => x * omega ^ r) := by
  rw [columnQueries, List.map_map, List.map_map]
  exact zip_map_fst (fun a : ℕ × ℤ => x * omega ^ a.2) layout evals

/-- `permutationCommonQueries` slot identities: one per column, in order. -/
theorem permutationCommonQueries_map_commId {k : ℕ} (x : Fp) (mkId : ℕ → CommitmentId)
    (commsEvals : List (G × Fp)) :
    (permutationCommonQueries (k := k) x mkId commsEvals).map (·.commId)
      = (List.range commsEvals.length).map mkId := by
  have h := zip_map_snd (γ := CommitmentId) mkId commsEvals (List.range commsEvals.length)
  rw [show (List.range commsEvals.length).take commsEvals.length
      = List.range commsEvals.length from by simp] at h
  rw [permutationCommonQueries, List.map_map]
  exact h

/-- `permutationCommonQueries` points: all at `x`. -/
theorem permutationCommonQueries_map_point {k : ℕ} (x : Fp) (mkId : ℕ → CommitmentId)
    (commsEvals : List (G × Fp)) :
    (permutationCommonQueries (k := k) x mkId commsEvals).map (·.point)
      = List.replicate commsEvals.length x := by
  rw [permutationCommonQueries, List.map_map]
  show (commsEvals.zip (List.range commsEvals.length)).map (fun _ => x)
    = List.replicate commsEvals.length x
  rw [List.map_const', List.length_zip, List.length_range, min_self]

/-- `lookupQueries` slot identities: the five per-lookup slots, in order. -/
theorem lookupQueries_map_commId {k : ℕ} (x xInv xNext : Fp)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval Fp)) :
    (lookupQueries (k := k) x xInv xNext mkProduct mkInput mkTable lookups).map (·.commId)
      = (List.range lookups.length).flatMap (fun l =>
          [mkProduct l, mkInput l, mkTable l, mkInput l, mkProduct l]) := by
  rw [lookupQueries, List.map_flatMap]
  have h := zip_flatMap_snd (γ := CommitmentId)
    (fun l => [mkProduct l, mkInput l, mkTable l, mkInput l, mkProduct l])
    lookups (List.range lookups.length)
  rw [show (List.range lookups.length).take lookups.length = List.range lookups.length
      from by simp] at h
  exact h

/-- `lookupQueries` points: `x`, `x`, `x`, `xInv`, `xNext` per lookup. -/
theorem lookupQueries_map_point {k : ℕ} (x xInv xNext : Fp)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval Fp)) :
    (lookupQueries (k := k) x xInv xNext mkProduct mkInput mkTable lookups).map (·.point)
      = (List.range lookups.length).flatMap (fun _ => [x, x, x, xInv, xNext]) := by
  rw [lookupQueries, List.map_flatMap]
  have h := zip_flatMap_snd (γ := Fp) (fun _ => [x, x, x, xInv, xNext])
    lookups (List.range lookups.length)
  rw [show (List.range lookups.length).take lookups.length = List.range lookups.length
      from by simp] at h
  exact h

variable (pt : Point shape) (base : ProofString shape Fp G)

/-- The permutation-set pair list every `permutationQueries` call receives at a sample point. -/
private abbrev permSets (p' : Fin shape.numProofs) (cs : Fin shape.numPermutationSets → G) :
    List (G × PermSetEval Fp) :=
  List.ofFn (fun s => (cs s, (Point.toProofString pt base).permutationSetEvals p' s))

/-- On sample points, every non-last permutation set carries a `some` last evaluation — the
`xLast` block's option pattern is fixed. -/
theorem permSets_lastEval_isSome (p' : Fin shape.numProofs)
    (cs : Fin shape.numPermutationSets → G) :
    ∀ e ∈ ((permSets pt base p' cs).zip
        (List.range (permSets pt base p' cs).length)).reverse.drop 1,
      (e.1.2.lastEval).isSome := by
  intro e he
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  have hlen : ((permSets pt base p' cs).zip
      (List.range (permSets pt base p' cs).length)).length = shape.numPermutationSets := by
    simp
  have hi' : i < shape.numPermutationSets - 1 := by
    simpa [hlen] using hi
  rw [List.getElem_drop, List.getElem_reverse] at hei
  have hj : ((permSets pt base p' cs).zip
        (List.range (permSets pt base p' cs).length)).length - 1 - (1 + i)
      < shape.numPermutationSets := by
    omega
  subst hei
  simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_range, hlen]
  rw [toProofString_permLastEval_of_lt pt base p' _ (by simp; omega)]
  rfl

/-- `permutationQueries` slot identities at a sample point: two per set, then the non-last sets
in reverse. -/
theorem permutationQueries_map_commId (p' : Fin shape.numProofs) {k : ℕ} (x xNext xLast : Fp)
    (mkId : ℕ → CommitmentId) (cs : Fin shape.numPermutationSets → G) :
    (permutationQueries (k := k) x xNext xLast mkId (permSets pt base p' cs)).map (·.commId)
      = (List.range shape.numPermutationSets).flatMap (fun s => [mkId s, mkId s])
        ++ ((List.range (shape.numPermutationSets - 1)).reverse).map mkId := by
  rw [permutationQueries, List.map_append]
  congr 1
  · rw [List.map_flatMap]
    simp only [List.length_ofFn]
    have h := zip_flatMap_snd (γ := CommitmentId) (fun s => [mkId s, mkId s])
      (permSets pt base p' cs) (List.range shape.numPermutationSets)
    rw [show (List.range shape.numPermutationSets).take (permSets pt base p' cs).length
        = List.range shape.numPermutationSets from by simp] at h
    exact h
  · rw [List.map_filterMap]
    have hstep : ∀ e ∈ ((permSets pt base p' cs).zip
        (List.range (permSets pt base p' cs).length)).reverse.drop 1,
        ((e.1.2.lastEval).map (fun le =>
            ({ point := xLast, commitment := .point e.1.1, eval := le, commId := mkId e.2 } :
              VerifierQuery k Fp G))).map (·.commId)
          = (e.1.2.lastEval).map (fun _ => mkId e.2) := by
      intro e _
      rw [Option.map_map]
      rfl
    rw [List.filterMap_congr hstep,
      filterMap_map_const_of_isSome (permSets_lastEval_isSome pt base p' cs)]
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_drop, List.getElem_reverse, List.getElem_zip,
      List.getElem_range]
    congr 1
    simp only [List.length_zip, List.length_ofFn, List.length_range, min_self] at h1 ⊢
    have h2' := h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h2'
    omega

/-- `permutationQueries` points at a sample point: `x`, `xNext` per set, then `xLast` over the
non-last sets. -/
theorem permutationQueries_map_point (p' : Fin shape.numProofs) {k : ℕ} (x xNext xLast : Fp)
    (mkId : ℕ → CommitmentId) (cs : Fin shape.numPermutationSets → G) :
    (permutationQueries (k := k) x xNext xLast mkId (permSets pt base p' cs)).map (·.point)
      = (List.range shape.numPermutationSets).flatMap (fun _ => [x, xNext])
        ++ List.replicate (shape.numPermutationSets - 1) xLast := by
  rw [permutationQueries, List.map_append]
  congr 1
  · rw [List.map_flatMap]
    simp only [List.length_ofFn]
    have h := zip_flatMap_snd (γ := Fp) (fun _ => [x, xNext])
      (permSets pt base p' cs) (List.range shape.numPermutationSets)
    rw [show (List.range shape.numPermutationSets).take (permSets pt base p' cs).length
        = List.range shape.numPermutationSets from by simp] at h
    exact h
  · rw [List.map_filterMap]
    have hstep : ∀ e ∈ ((permSets pt base p' cs).zip
        (List.range (permSets pt base p' cs).length)).reverse.drop 1,
        ((e.1.2.lastEval).map (fun le =>
            ({ point := xLast, commitment := .point e.1.1, eval := le, commId := mkId e.2 } :
              VerifierQuery k Fp G))).map (·.point)
          = (e.1.2.lastEval).map (fun _ => xLast) := by
      intro e _
      rw [Option.map_map]
      rfl
    rw [List.filterMap_congr hstep,
      filterMap_map_const_of_isSome (permSets_lastEval_isSome pt base p' cs)]
    rw [List.map_const']
    congr 1
    simp

end Builders

/-! ## The assembled streams -/

section Assembled

variable {shape : Shape} {G : Type*} [Inhabited G]

/-- **The slot-identity stream of `assembleQueries` is a verifying-key constant**: at every
sample point, the assembled queries carry exactly the identities of `queryCommIds`. -/
theorem assembleQueries_map_commId (vk : VerifyingKey shape Fp G)
    (ic : Fin shape.numProofs → ℕ → G) (pt : Point shape) (base : ProofString shape Fp G) :
    (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)).map (·.commId)
      = queryCommIds shape vk := by
  rw [assembleQueries, queryCommIds]
  simp only [List.map_append]
  congr 1
  · congr 1
    · congr 1
      · -- the per-sub-proof blocks
        rw [List.map_flatten, List.map_ofFn]
        congr 1
        refine ofFn_eq_range_map _ _ ?_
        intro p
        simp only [Function.comp_apply, List.map_append]
        rw [columnQueries_map_commId, columnQueries_map_commId,
          permutationQueries_map_commId pt base p, lookupQueries_map_commId,
          perProofCommIds]
        simp only [List.length_ofFn]
      · -- the fixed columns
        rw [columnQueries_map_commId]
        simp only [List.length_ofFn]
    · -- the common permutation columns
      rw [permutationCommonQueries_map_commId]
      simp only [List.length_ofFn]

/-- **The point stream of `assembleQueries` is the rotation stream scaled by `x`**: at every
sample point, the assembled queries open at exactly `x · ω^r` over `queryRots`. -/
theorem assembleQueries_map_point (vk : VerifyingKey shape Fp G)
    (ic : Fin shape.numProofs → ℕ → G) (pt : Point shape) (base : ProofString shape Fp G) :
    (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)).map (·.point)
      = (queryRots shape vk).map (fun r => pt .x * vk.omega ^ r) := by
  rw [assembleQueries, queryRots]
  simp only [List.map_append]
  congr 1
  · congr 1
    · congr 1
      · -- the per-sub-proof blocks
        rw [List.map_flatten, List.map_flatten, List.map_ofFn, List.map_map]
        congr 1
        refine ofFn_eq_range_map _ _ ?_
        intro p
        simp only [Function.comp_apply, List.map_append]
        rw [columnQueries_map_point, columnQueries_map_point,
          permutationQueries_map_point pt base p, lookupQueries_map_point,
          perProofRots]
        simp [List.map_flatMap, rotateOmega, toChallenges_x]
      · -- the fixed columns
        rw [columnQueries_map_point]
        simp only [List.length_ofFn, toChallenges_x]
    · -- the common permutation columns
      rw [permutationCommonQueries_map_point]
      simp only [List.length_ofFn, List.map_replicate, toChallenges_x, zpow_zero, mul_one]
  · -- the vanishing block
    simp [vanishingQueries, toChallenges_x]

end Assembled

/-! ## The reference table -/

section RefTable

variable {shape : Shape} {G : Type*}

/-- The rotation classes: first-appearance deduplication of the rotation stream. On the good
event, the assembled queries' distinct points are exactly these classes scaled by `x`. -/
def rotClasses (shape : Shape) (vk : VerifyingKey shape Fp G) : List ℤ :=
  dedupFold (queryRots shape vk)

/-- A rotation's point-class index. -/
def rotIdx (shape : Shape) (vk : VerifyingKey shape Fp G) (r : ℤ) : ℕ :=
  (rotClasses shape vk).findIdx (fun r' => decide (r' = r))

/-- The reference table: the closed form `refQueries` takes on the assembled query list at every
good sample point (`refQueries_eq_refTable`) — points are rotation-class indices, payloads are
flat positions, slot identities are the fixed stream. -/
def refTable (shape : Shape) (vk : VerifyingKey shape Fp G) :
    List (VerifierQuery shape.k ℕ ℕ) :=
  (List.range (queryCommIds shape vk).length).map fun n =>
    { point := rotIdx shape vk ((queryRots shape vk).getD n 0)
      commitment := .point n
      eval := n
      commId := (queryCommIds shape vk).getD n .vanishingH }

/-- One sub-proof's streams are aligned. -/
theorem perProof_length_eq (vk : VerifyingKey shape Fp G) (p : ℕ) :
    (perProofCommIds shape vk p).length = (perProofRots shape vk).length := by
  simp only [perProofCommIds, perProofRots, List.length_append, List.length_map,
    List.length_take, List.length_flatMap, List.length_replicate, List.length_reverse,
    List.length_range]
  simp [List.map_const', List.sum_replicate]

/-- The two streams are aligned: one rotation per slot identity. -/
theorem queryRots_length (vk : VerifyingKey shape Fp G) :
    (queryRots shape vk).length = (queryCommIds shape vk).length := by
  have hmap : ((List.range shape.numProofs).map (perProofCommIds shape vk)).map List.length
      = ((List.range shape.numProofs).map (fun _ => perProofRots shape vk)).map List.length := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro p _
    exact perProof_length_eq vk p
  simp only [queryRots, queryCommIds, List.length_append, List.length_flatten, hmap,
    List.length_map, List.length_replicate, List.length_range]
  simp

/-- Every stream rotation is an enumerated rotation of the good event: the `x₃`-avoidance
factors cover every opened point. -/
theorem queryRots_mem_queryRotations (vk : VerifyingKey shape Fp G) :
    ∀ r ∈ queryRots shape vk, r ∈ queryRotations vk := by
  have hbase : ∀ r,
      (r ∈ (vk.instanceQueryLayout ++ vk.adviceQueryLayout ++ vk.fixedQueryLayout).map (·.2)
        ∨ r ∈ [(0 : ℤ), 1, -1, -((vk.blindingFactors : ℤ) + 1)]) → r ∈ queryRotations vk := by
    intro r hr
    rw [queryRotations, List.mem_dedup, List.mem_append]
    exact hr
  intro r hr
  simp only [queryRots, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · -- the per-proof blocks
    obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hl
    simp only [perProofRots, List.mem_append] at hrl
    rcases hrl with ((hrl | hrl) | hrl | hrl) | hrl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hrl
      refine hbase _ (Or.inl (List.mem_map.mpr ⟨e, ?_, rfl⟩))
      simp only [List.mem_append]
      exact Or.inl (Or.inl (List.mem_of_mem_take he))
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hrl
      refine hbase _ (Or.inl (List.mem_map.mpr ⟨e, ?_, rfl⟩))
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_of_mem_take he))
    · obtain ⟨_, _, hr2⟩ := List.mem_flatMap.mp hrl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
      rcases hr2 with rfl | rfl <;> exact hbase _ (Or.inr (by simp))
    · have := List.eq_of_mem_replicate hrl
      subst this
      exact hbase _ (Or.inr (by simp))
    · obtain ⟨_, _, hr2⟩ := List.mem_flatMap.mp hrl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
      rcases hr2 with rfl | rfl | rfl | rfl | rfl <;> exact hbase _ (Or.inr (by simp))
  · -- the fixed columns
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    refine hbase _ (Or.inl (List.mem_map.mpr ⟨e, ?_, rfl⟩))
    simp only [List.mem_append]
    exact Or.inr (List.mem_of_mem_take he)
  · -- the common permutation columns
    have := List.eq_of_mem_replicate hr
    subst this
    exact hbase _ (Or.inr (by simp))
  · -- the vanishing block
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hbase _ (Or.inr (by simp))

/-- The decidable verifying-key facts the reference-table story needs: nondegenerate domain
size, injectivity of `ω`-powers on the opened rotations (the engine of grouping stability),
chunk alignment, and the two grouping-shape facts of the reference table itself. All fields are
decidable data — `native_decide` material at a captured key, hypotheses generically. -/
structure VkSymbolicFacts (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G) : Prop where
  n_pos : 0 < vk.n
  n_ne_zero : (vk.n : Fp) ≠ 0
  rot_pow_inj : ∀ r ∈ queryRots shape vk, ∀ r' ∈ queryRots shape vk,
    vk.omega ^ r = vk.omega ^ r' → r = r'
  chunks_len : vk.permutationChunks.length = shape.numPermutationSets
  ref_dup_free : hasDuplicateCommitmentPoint (refTable shape vk) = false
  ref_numSets : (constructIntermediateSets (refTable shape vk)).sets.length
    = shape.numPointSets

/-- Read a positional entry off a stream equation. -/
theorem map_getD_eq {α β : Type*} {l : List α} {m : List β} {f : α → β} (h : l.map f = m)
    {n : ℕ} (hn : n < l.length) (d : α) (d' : β) : f (l.getD n d) = m.getD n d' := by
  subst h
  rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ (by simpa using hn),
    List.getElem_map]

section Constancy

variable {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
variable (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
variable (base : ProofString shape Fp G)

omit [DecidableEq G] in
/-- **Event constancy.** On the good event, the reference of the assembled query list is the
fixed reference table: `x ≠ 0` makes scaling by `x` injective, and `rot_pow_inj` fixes the
`ω`-power classes, so every good sample point classes its query points identically. -/
theorem refQueries_eq_refTable {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    refQueries (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))
      = refTable shape vk := by
  have hx : pt .x ≠ 0 := ((goodEvent_iff vk pt).mp hgood).2.1
  set aq := assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)
    with haq
  have hcomm := assembleQueries_map_commId vk ic pt base
  have hpts := assembleQueries_map_point vk ic pt base
  have hlen : aq.length = (queryCommIds shape vk).length := by
    have h := congrArg List.length hcomm
    simpa using h
  have hlenR : (queryRots shape vk).length = aq.length := by
    have h := congrArg List.length hpts
    simp only [List.length_map] at h
    exact h.symm
  have hinj : ∀ a ∈ queryRots shape vk, ∀ b ∈ queryRots shape vk,
      pt .x * vk.omega ^ a = pt .x * vk.omega ^ b → a = b :=
    fun a ha b hb h => hf.rot_pow_inj a ha b hb (mul_left_cancel₀ hx h)
  have hcisPts : cisPts aq
      = (rotClasses shape vk).map (fun r => pt .x * vk.omega ^ r) := by
    rw [cisPts_eq_dedupFold, hpts, dedupFold_map _ _ hinj, rotClasses]
  refine List.ext_getElem (by simp [refQueries, refTable, hlen]) ?_
  intro n h1 h2
  have hn : n < aq.length := by simpa [refQueries] using h1
  have hnR : n < (queryRots shape vk).length := by omega
  have hrmem : (queryRots shape vk).getD n 0 ∈ queryRots shape vk := by
    rw [List.getD_eq_getElem _ _ hnR]
    exact List.getElem_mem hnR
  simp only [refQueries, refTable, List.getElem_map, List.getElem_range]
  have hcommn : (aq.getD n default).commId = (queryCommIds shape vk).getD n .vanishingH :=
    map_getD_eq hcomm hn default .vanishingH
  have hptn : (aq.getD n default).point
      = pt .x * vk.omega ^ ((queryRots shape vk).getD n 0) := by
    have h' := map_getD_eq hpts hn default (0 : Fp)
    rw [h', List.getD_eq_getElem _ _ (by simpa using hnR), List.getElem_map,
      List.getD_eq_getElem _ _ hnR]
  have hclass : cisPIdx aq (aq.getD n default).point
      = rotIdx shape vk ((queryRots shape vk).getD n 0) := by
    rw [hptn, cisPIdx, hcisPts, rotIdx, rotClasses]
    refine findIdx_map_inj (fun r => pt .x * vk.omega ^ r)
      (dedupFold (queryRots shape vk)) (mem_dedupFold.mpr hrmem) ?_
    intro a ha hEq
    exact hinj a (mem_dedupFold.mp ha) _ hrmem hEq
  rw [hclass, hcommn]

/-- Every grouped point of the assembled queries is an opened point of the flat list. -/
theorem constructIntermediateSets_points_subset {k : ℕ} {F G' : Type*} [DecidableEq F]
    [DecidableEq G'] (qs : List (VerifierQuery k F G')) :
    ∀ pts ∈ (constructIntermediateSets qs).points, ∀ p ∈ pts, p ∈ qs.map (·.point) := by
  intro pts hpts p hp
  have hview : (constructIntermediateSets qs).points
      = (cisSetList qs).map (fun s => s.filterMap (fun i => (cisPts qs)[i]?)) := rfl
  rw [hview] at hpts
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hpts
  obtain ⟨i, _, hip⟩ := List.mem_filterMap.mp hp
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hip
  have hmem : (cisPts qs)[i] ∈ dedupFold (qs.map (·.point)) := by
    rw [← cisPts_eq_dedupFold]
    exact List.getElem_mem hlt
  exact mem_dedupFold.mp hmem

/-- On the good event, `x₃` avoids every grouped point — the deployed panic set is missed. -/
theorem grouped_avoidX3 {pt : Point shape} (hgood : GoodEvent vk pt) :
    multiopenPointsAvoidX3 (Point.toChallenges pt).x3
      (constructIntermediateSets
        (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)))
      = true := by
  have hx3 := ((goodEvent_iff vk pt).mp hgood).2.2.2.1
  rw [multiopenPointsAvoidX3, List.all_eq_true]
  intro pts hpts
  rw [List.all_eq_true]
  intro q hq
  have hp := constructIntermediateSets_points_subset _ pts hpts q hq
  rw [assembleQueries_map_point vk ic pt base] at hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  have hne := hx3 r (queryRots_mem_queryRotations vk r hr)
  simp only [toChallenges_x3, decide_eq_true_iff]
  intro hEq
  exact hne (by rw [hEq, mul_comm])

/-- **Grouping stability, `ids` view**: on the good event, the grouped slot identities are the
reference table's — one fixed combinatorial object across the event. -/
theorem grouped_ids_eq {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    (constructIntermediateSets
        (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))).ids
      = (constructIntermediateSets (refTable shape vk)).ids := by
  rw [constructIntermediateSets_ref_ids, refQueries_eq_refTable vk ic base hf hgood]

/-- **Grouping stability, `points` view**: the grouped points are the reference table's class
lists, decoded through the rotation classes scaled by `x`. -/
theorem grouped_points_eq {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    (constructIntermediateSets
        (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))).points
      = ((constructIntermediateSets (refTable shape vk)).points).map
          (List.map fun i =>
            ((rotClasses shape vk).map (fun r => pt .x * vk.omega ^ r)).getD i 0) := by
  have hx : pt .x ≠ 0 := ((goodEvent_iff vk pt).mp hgood).2.1
  have hinj : ∀ a ∈ queryRots shape vk, ∀ b ∈ queryRots shape vk,
      pt .x * vk.omega ^ a = pt .x * vk.omega ^ b → a = b :=
    fun a ha b hb h => hf.rot_pow_inj a ha b hb (mul_left_cancel₀ hx h)
  have hcisPts : cisPts (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt))
      = (rotClasses shape vk).map (fun r => pt .x * vk.omega ^ r) := by
    rw [cisPts_eq_dedupFold, assembleQueries_map_point vk ic pt base,
      dedupFold_map _ _ hinj, rotClasses]
  rw [constructIntermediateSets_ref_points, refQueries_eq_refTable vk ic base hf hgood,
    hcisPts]

/-- **Grouping stability, `sets` view**: the grouped members are the reference table's, decoded
positionally back to the assembled queries' commitments and claimed evaluations. -/
theorem grouped_sets_eq {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    (constructIntermediateSets
        (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))).sets
      = ((constructIntermediateSets (refTable shape vk)).sets).map
          (List.map (decodeMember
            (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)))) := by
  rw [constructIntermediateSets_ref_sets, refQueries_eq_refTable vk ic base hf hgood]

/-- The assembled MSM at a sample point: the total `assemble` at the rebuilt inputs. -/
def assembleAt (pt : Point shape) : Msm shape.k Fp G :=
  assemble vk ic (Point.toProofString pt base) (Point.toChallenges pt)

/-- **`assemble?` succeeds on the whole good event**, with the fixed reference-table grouping
shape: the read schedule holds by construction, `xⁿ ≠ 1` and the `x₃`-avoidance are good-event
conjuncts, duplicate-freedom and the `u`-count check transport from the reference table. -/
theorem assembleAt_some {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    assemble? vk ic (Point.toProofString pt base) (Point.toChallenges pt)
      = some (assembleAt vk ic base pt) := by
  have hxn : ¬ ((Point.toChallenges pt).x ^ vk.n = 1) := by
    simpa [toChallenges_x] using ((goodEvent_iff vk pt).mp hgood).1
  have hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)) = false := by
    rw [hasDuplicateCommitmentPoint_ref, refQueries_eq_refTable vk ic base hf hgood]
    exact hf.ref_dup_free
  have hsets : (constructIntermediateSets
      (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt))).sets.length = shape.numPointSets := by
    rw [constructIntermediateSets_ref_sets_length,
      refQueries_eq_refTable vk ic base hf hgood]
    exact hf.ref_numSets
  have havoid := grouped_avoidX3 vk ic base hgood
  have hpl := constructIntermediateSets_points_length
    (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))
  have hsome : (assemble? vk ic (Point.toProofString pt base)
      (Point.toChallenges pt)).isSome := by
    rw [assemble?]
    simp only [proofStringWellFormed_toProofString, if_true, hxn, if_false,
      constructIntermediateSets?, hdup, Bool.false_eq_true, havoid,
      assembleFinalMsm?, assembleOpening?, List.length_ofFn]
    rw [if_pos ⟨hsets.symm, hpl.symm⟩]
    rfl
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  rw [assembleAt, assemble, hm]
  rfl

end Constancy

end RefTable

end Zcash.Snark
