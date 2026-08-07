import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Fingerprint.Rational.ConstraintWalk
import Zcash.Snark.Fingerprint.Rational.GroupingTable

/-!
# The opening-value walk

Ledger stages 6–9: on the good event, the multiopen **value side** of the assembly is a rational
function of the sample point. The pipeline computes, per point set, the `x₁`-compressed
evaluation vector (`compressSet`), interpolates it at `x₃` (`lagrangeEval`), clears the
`(x₃ − point)` factors into the per-set quotient claim (`multiopenEval`'s per-set step), folds
the sets by `x₂`, and folds the claimed `u`-values by `x₄` against the running evaluation
(`multiopenCombine`) — producing the opening value `v` that `ipaFold` places at `gScalars 0`.

The walk splits plumbing from representation:

* **Reified data.** On the good event the grouping is the fixed reference table
  (`Fingerprint/Rational/GroupingTable.lean`), so the per-set member evaluation index lists
  (`refMemberEvalIdx`) and rotation classes (`classRotsL`) are verifying-key constants, and the
  whole value computation factors through them (`openingValue_eq`): the only point dependence
  left is the claimed-evaluation stream (`queryEvalAt`) and the challenge coordinates.
* **Representation.** Each reified stage is closed under the `NumeratorRep` toolkit: the
  claimed-evaluation stream is represented over `vanDen` (`queryEval_rep` — the vanishing
  member's evaluation is `expectedHEval`, everything else is a slot variable), compression
  costs one `x₁` degree per member, interpolation clears the pair differences
  `x·(ω^{rᵢ} − ω^{rⱼ})` into a bare `x`-power denominator (the constants are nonzero by
  `rot_pow_inj`), the per-set quotient step divides by the enumerated `x₃`-avoidance factors,
  and the `x₂`/`x₄` folds cost one degree per step (`NumeratorRep.foldl_scale_add`).

The capstone `openingValue_rep` represents `(assembleOpening …).2` exactly as
`assembleFinalMsm` invokes it, over the full opening denominator `openDen` — the input the IPA
stage's `gScalars 0` representation consumes.
-/

namespace Zcash.Snark

open MvPolynomial
open Zcash.Arithmetic (Msm)

/-! ## Generic list and fold helpers -/

/-- `getD` through a `map`, with the mapped default. -/
theorem getD_map_eq {α β : Type*} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  rcases lt_or_ge n l.length with h | h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_map]
  · rw [List.getD_eq_default _ _ h, List.getD_eq_default _ _ (by simpa using h)]

/-- A `filterMap` whose per-element option is always `some` is the map of the defaulted
payloads. -/
theorem filterMap_map_getD_of_isSome {α β γ : Type*} {l : List α} {g : α → Option β}
    (h' : ∀ a ∈ l, (g a).isSome) (c : β → α → γ) (d : β) :
    l.filterMap (fun a => (g a).map (fun v => c v a)) = l.map (fun a => c ((g a).getD d) a) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h' a List.mem_cons_self
    rcases hg : g a with _ | v
    · rw [hg] at ha
      simp at ha
    · simp only [List.filterMap_cons, hg, Option.map_some, Option.getD_some, List.map_cons]
      rw [ih (fun b hb => h' b (List.mem_cons_of_mem _ hb))]

/-- Flat-mapping a zip through a first-component function is flat-mapping the truncated first
list. -/
theorem zip_flatMap_fst {α β γ : Type*} (g : α → List γ) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.zip l₂).flatMap (fun e => g e.1) = (l₁.take l₂.length).flatMap g := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a t ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b u => simp [ih u]

/-- The value component of the `compressSet` fold ignores the MSM component: it is the plain
fold of the member evaluation lists. -/
theorem compressSet_snd {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ) :
    (compressSet x1 setQueries numPoints).2
      = ((setQueries.map Prod.snd).foldl
          (fun (st : List F × F) evs =>
            ((st.1.zip evs).map (fun e => e.1 + e.2 * st.2), st.2 * x1))
          (List.replicate numPoints (0 : F), (1 : F))).1 := by
  suffices h : ∀ (sq : List (CommitmentRef k F G × List F)) (m : Msm k F G) (l : List F) (p : F),
      (sq.foldl (fun (st : Msm k F G × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) (m, l, p)).2
        = (sq.map Prod.snd).foldl
            (fun (st : List F × F) evs =>
              ((st.1.zip evs).map (fun e => e.1 + e.2 * st.2), st.2 * x1)) (l, p) by
    rw [compressSet]
    exact congrArg Prod.fst (h setQueries _ _ _)
  intro sq
  induction sq with
  | nil => intro m l p; rfl
  | cons qc t ih => intro m l p; exact ih _ _ _

/-- The value component of the `multiopenCombine` fold ignores the MSM component: it is the
`x₄`-fold of the (truncated) `u`-values seeded at the running evaluation. -/
theorem multiopenCombine_snd {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F) (incoming : Msm k F G) :
    (multiopenCombine x4 qPrime qCommitments u msmEval incoming).2
      = ((qCommitments.zip u).map Prod.snd).foldl (fun acc w => acc * x4 + w) msmEval := by
  rw [multiopenCombine]
  suffices h : ∀ (l : List (Msm k F G × F)) (m : Msm k F G) (v : F),
      (l.foldl (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
          (m, v)).2
        = (l.map Prod.snd).foldl (fun acc w => acc * x4 + w) v from h _ _ _
  intro l
  induction l with
  | nil => intro m v; rfl
  | cons p t ih => intro m v; exact ih _ _

/-- Zipping two maps over the same index list is mapping the pair. -/
theorem zip_map_same {α β γ : Type*} (f : α → β) (g : α → γ) (l : List α) :
    (l.map f).zip (l.map g) = l.map (fun x => (f x, g x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-! ## `ListRep` element access -/

namespace ListRep

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}
variable {den : MvPolynomial (ScalarSlot shape) Fp} {l : Point shape → List Fp} {d : ℕ}

/-- Every positional entry of a represented list is represented (out of range: the zero
default). -/
theorem getD (h : ListRep vk den l d) (j : ℕ) :
    NumeratorRep vk den (fun pt => (l pt).getD j 0) d := by
  obtain ⟨fns, heq, hrep⟩ := h
  rcases lt_or_ge j fns.length with hj | hj
  · refine (hrep (fns.getD j (fun _ => 0)) ?_).congr_event fun pt _ => ?_
    · rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    · rw [heq pt, show (0 : Fp) = (fun _ : Point shape => (0 : Fp)) pt from rfl,
        getD_map_eq (· pt) fns j (fun _ => 0)]
  · have h0 : NumeratorRep vk den (fun _ => (0 : Fp)) d := ⟨0, by simp, fun pt _ => by simp⟩
    refine h0.congr_event fun pt _ => ?_
    rw [heq pt, List.getD_eq_default _ _ (by simpa using hj)]

end ListRep

/-! ## The claimed-evaluation stream

The evaluation stream of `assembleQueries` factors through a fixed list of represented
functions: slot variables for every claimed evaluation, and `expectedHEval` for the vanishing
member. This is the stage-5 glue — the member evaluation lists the multiopen consumes are
positional lookups into this stream. -/

section EvalStream

variable {shape : Shape} {G : Type*}

/-- `columnQueries` evaluations: the claimed evaluations, truncated to the layout. -/
theorem columnQueries_map_eval {k : ℕ} (omega x : Fp) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List Fp) :
    (columnQueries (k := k) omega x commitment mkId layout evals).map (·.eval)
      = evals.take layout.length := by
  rw [columnQueries, List.map_map]
  have h := zip_map_snd (γ := Fp) id layout evals
  simpa using h

/-- `permutationCommonQueries` evaluations: the common evaluations, in order. -/
theorem permutationCommonQueries_map_eval {k : ℕ} (x : Fp) (mkId : ℕ → CommitmentId)
    (commsEvals : List (G × Fp)) :
    (permutationCommonQueries (k := k) x mkId commsEvals).map (·.eval)
      = commsEvals.map (·.2) := by
  rw [permutationCommonQueries, List.map_map]
  have h := zip_map_fst (fun ce : G × Fp => ce.2) commsEvals (List.range commsEvals.length)
  simpa using h

/-- `lookupQueries` evaluations: the five claimed evaluations per lookup, in query order. -/
theorem lookupQueries_map_eval {k : ℕ} (x xInv xNext : Fp)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval Fp)) :
    (lookupQueries (k := k) x xInv xNext mkProduct mkInput mkTable lookups).map (·.eval)
      = lookups.flatMap (fun l => [l.2.productEval, l.2.permutedInputEval,
          l.2.permutedTableEval, l.2.permutedInputInvEval, l.2.productNextEval]) := by
  rw [lookupQueries, List.map_flatMap]
  have h := zip_flatMap_fst (fun l : LookupCommitments G × LookupEval Fp =>
      [l.2.productEval, l.2.permutedInputEval, l.2.permutedTableEval,
        l.2.permutedInputInvEval, l.2.productNextEval])
    lookups (List.range lookups.length)
  rw [show (lookups.take (List.range lookups.length).length) = lookups from by simp] at h
  exact h

variable (pt : Point shape) (base : ProofString shape Fp G)

/-- The permutation-set pair list every `permutationQueries` call receives at a sample point
(the private `QueryTable` abbreviation, restated). -/
private abbrev permSetsO (p' : Fin shape.numProofs) (cs : Fin shape.numPermutationSets → G) :
    List (G × PermSetEval Fp) :=
  List.ofFn (fun s => (cs s, (Point.toProofString pt base).permutationSetEvals p' s))

/-- On sample points, every non-last permutation set carries a `some` last evaluation. -/
private theorem permSetsO_lastEval_isSome (p' : Fin shape.numProofs)
    (cs : Fin shape.numPermutationSets → G) :
    ∀ e ∈ ((permSetsO pt base p' cs).zip
        (List.range (permSetsO pt base p' cs).length)).reverse.drop 1,
      (e.1.2.lastEval).isSome := by
  intro e he
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  have hlen : ((permSetsO pt base p' cs).zip
      (List.range (permSetsO pt base p' cs).length)).length = shape.numPermutationSets := by
    simp
  have hi' : i < shape.numPermutationSets - 1 := by
    simpa [hlen] using hi
  rw [List.getElem_drop, List.getElem_reverse] at hei
  subst hei
  simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_range, hlen]
  rw [toProofString_permLastEval_of_lt pt base p' _ (by simp; omega)]
  rfl

/-- `permutationQueries` evaluations at a sample point: the per-set `eval`/`nextEval` slots, then
the non-last sets' `lastEval` slots in reverse. -/
theorem permutationQueries_map_eval (p' : Fin shape.numProofs) {k : ℕ} (x xNext xLast : Fp)
    (mkId : ℕ → CommitmentId) (cs : Fin shape.numPermutationSets → G) :
    (permutationQueries (k := k) x xNext xLast mkId (permSetsO pt base p' cs)).map (·.eval)
      = (List.ofFn (fun s : Fin shape.numPermutationSets =>
            [pt (.permEval p' s), pt (.permNextEval p' s)])).flatten
        ++ (List.ofFn (fun j : Fin (shape.numPermutationSets - 1) =>
            pt (.permLastEval p' j))).reverse := by
  rw [permutationQueries, List.map_append]
  congr 1
  · rw [List.map_flatMap]
    simp only [List.map_cons, List.map_nil]
    have h := zip_flatMap_fst (fun se : G × PermSetEval Fp => [se.2.eval, se.2.nextEval])
      (permSetsO pt base p' cs) (List.range (permSetsO pt base p' cs).length)
    rw [show ((permSetsO pt base p' cs).take
        (List.range (permSetsO pt base p' cs).length).length) = permSetsO pt base p' cs
      from by simp] at h
    rw [h, List.flatMap_def, List.map_ofFn]
    rfl
  · rw [List.map_filterMap]
    have hstep : ∀ e ∈ ((permSetsO pt base p' cs).zip
        (List.range (permSetsO pt base p' cs).length)).reverse.drop 1,
        ((e.1.2.lastEval).map (fun le =>
            ({ point := xLast, commitment := .point e.1.1, eval := le, commId := mkId e.2 } :
              VerifierQuery k Fp G))).map (·.eval)
          = (e.1.2.lastEval).map (fun le => le) := by
      intro e _
      rw [Option.map_map]
      rfl
    rw [List.filterMap_congr hstep,
      filterMap_map_getD_of_isSome (permSetsO_lastEval_isSome pt base p' cs)
        (fun le _ => le) 0]
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    have h1' : i < shape.numPermutationSets - 1 := by
      simpa using h1
    rw [List.getElem_map, List.getElem_drop, List.getElem_reverse, List.getElem_reverse]
    simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_range]
    have hlen : ((permSetsO pt base p' cs).zip
        (List.range (permSetsO pt base p' cs).length)).length = shape.numPermutationSets := by
      simp
    rw [toProofString_permLastEval_of_lt pt base p' _ (by simp; omega)]
    simp only [Option.getD_some]
    exact congrArg pt (congrArg (ScalarSlot.permLastEval p') (Fin.ext (by
      simp only [List.length_zip, List.length_ofFn, List.length_range, min_self]
      omega)))

end EvalStream

section EvalFns

variable {shape : Shape} {G : Type*} [Inhabited G] (vk : VerifyingKey shape Fp G)

/-- One sub-proof's fixed evaluation-function block, aligned with the builders' query order. -/
def perProofEvalFns (p : Fin shape.numProofs) : List (Point shape → Fp) :=
  (List.ofFn (fun q : Fin shape.numInstanceQueries =>
      fun pt : Point shape => pt (.instanceEval p q))).take vk.instanceQueryLayout.length
    ++ (List.ofFn (fun q : Fin shape.numAdviceQueries =>
      fun pt : Point shape => pt (.adviceEval p q))).take vk.adviceQueryLayout.length
    ++ ((List.ofFn (fun s : Fin shape.numPermutationSets =>
          [fun pt : Point shape => pt (.permEval p s),
           fun pt : Point shape => pt (.permNextEval p s)])).flatten
        ++ (List.ofFn (fun j : Fin (shape.numPermutationSets - 1) =>
          fun pt : Point shape => pt (.permLastEval p j))).reverse)
    ++ (List.ofFn (fun l : Fin shape.numLookups =>
        [fun pt : Point shape => pt (.lookupProductEval p l),
         fun pt : Point shape => pt (.lookupPermInputEval p l),
         fun pt : Point shape => pt (.lookupPermTableEval p l),
         fun pt : Point shape => pt (.lookupPermInputInvEval p l),
         fun pt : Point shape => pt (.lookupProductNextEval p l)])).flatten

variable (base : ProofString shape Fp G)

/-- The vanishing member's evaluation, exactly as `assembleQueries` computes it. -/
def expectedHEvalFn : Point shape → Fp := fun pt =>
  expectedHEval
    (allExpressions vk (Point.toProofString pt base) (Point.toChallenges pt)
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
        (pt ScalarSlot.x)).1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
        (pt ScalarSlot.x)).2.1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
        (pt ScalarSlot.x)).2.2)
    (pt ScalarSlot.y) (pt ScalarSlot.x ^ vk.n)

/-- The fixed evaluation-function stream of `assembleQueries`: per-sub-proof slot blocks, the
fixed and common-permutation slots, then the vanishing pair. -/
def queryEvalFns : List (Point shape → Fp) :=
  (List.ofFn (fun p : Fin shape.numProofs => perProofEvalFns vk p)).flatten
    ++ (List.ofFn (fun q : Fin shape.numFixedQueries =>
      fun pt : Point shape => pt (.fixedEval q))).take vk.fixedQueryLayout.length
    ++ List.ofFn (fun c : Fin shape.numPermutationColumns =>
      fun pt : Point shape => pt (.permCommonEval c))
    ++ [expectedHEvalFn vk base, fun pt : Point shape => pt .vanishingRandomEval]

/-- **The evaluation stream factors through the fixed function list**: at every sample point,
the assembled queries' claimed evaluations are `queryEvalFns` applied at the point. -/
theorem assembleQueries_map_eval (ic : Fin shape.numProofs → ℕ → G) (pt : Point shape) :
    (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)).map (·.eval)
      = (queryEvalFns vk base).map (· pt) := by
  rw [assembleQueries, queryEvalFns]
  simp only [List.map_append]
  congr 1
  · congr 1
    · congr 1
      · -- the per-sub-proof blocks
        rw [List.map_flatten, List.map_ofFn, List.map_flatten, List.map_ofFn]
        congr 1
        refine congrArg List.ofFn (funext fun p => ?_)
        simp only [Function.comp_apply, List.map_append]
        rw [columnQueries_map_eval, columnQueries_map_eval,
          permutationQueries_map_eval pt base p, lookupQueries_map_eval, perProofEvalFns,
          List.flatMap_def, List.map_ofFn]
        simp only [List.map_append, List.map_take, List.map_ofFn, List.map_flatten,
          List.map_reverse, Function.comp_def]
        rfl
      · -- the fixed columns
        rw [columnQueries_map_eval]
        simp only [List.map_take, List.map_ofFn, Function.comp_def]
        rfl
    · -- the common permutation columns
      rw [permutationCommonQueries_map_eval]
      simp only [List.map_ofFn, Function.comp_def]
      rfl

end EvalFns

/-! ## Representing the evaluation stream -/

section EvalRep

variable {shape : Shape} {G : Type*} [Inhabited G] {vk : VerifyingKey shape Fp G}

omit [Inhabited G] in
/-- Extend a trivial-denominator representation to `vanDen`, at the `lagBudget` degree price. -/
theorem NumeratorRep.extendToVanDen {f : Point shape → Fp} {a : ℕ}
    (h : NumeratorRep vk 1 f a) : NumeratorRep vk (vanDen vk) f (a + lagBudget vk) :=
  (((h.extend (vanDen vk)).denCongr (one_mul _)).mono
    (Nat.add_le_add_left (vanDen_totalDegree_le (vk := vk)) a))

omit [Inhabited G] in
/-- Every per-sub-proof evaluation function is a slot variable. -/
theorem perProofEvalFns_rep (p : Fin shape.numProofs) :
    ∀ f ∈ perProofEvalFns vk p, NumeratorRep vk 1 f 1 := by
  intro f hf
  simp only [perProofEvalFns, List.mem_append] at hf
  rcases hf with ((hf | hf) | (hf | hf)) | hf
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hf)
    exact NumeratorRep.var _
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hf)
    exact NumeratorRep.var _
  · obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hf
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfl
    rcases hfl with rfl | rfl
    · exact NumeratorRep.var _
    · exact NumeratorRep.var _
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hf)
    exact NumeratorRep.var _
  · obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hf
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfl
    rcases hfl with rfl | rfl | rfl | rfl | rfl
    · exact NumeratorRep.var _
    · exact NumeratorRep.var _
    · exact NumeratorRep.var _
    · exact NumeratorRep.var _
    · exact NumeratorRep.var _

variable (base : ProofString shape Fp G)

omit [Inhabited G] in
/-- Every evaluation-stream function is represented over `vanDen` at the `hEvalBudget` cap: the
vanishing member is `expectedHEval`, everything else a slot variable. -/
theorem queryEvalFns_rep
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) :
    ∀ f ∈ queryEvalFns vk base, NumeratorRep vk (vanDen vk) f (hEvalBudget shape vk) := by
  have hbudget : 1 + lagBudget vk ≤ hEvalBudget shape vk := by
    simp only [hEvalBudget, constraintValBudget]
    omega
  intro f hf
  simp only [queryEvalFns, List.mem_append] at hf
  rcases hf with ((hf | hf) | hf) | hf
  · obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hf
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
    exact ((perProofEvalFns_rep p f hfl).extendToVanDen).mono hbudget
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hf)
    exact ((NumeratorRep.var _).extendToVanDen).mono hbudget
  · obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hf
    exact ((NumeratorRep.var _).extendToVanDen).mono hbudget
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact expectedHEval_rep base hchunkW hchunks hS
    · exact ((NumeratorRep.var _).extendToVanDen).mono hbudget

/-- **Stage-5 glue.** Every positional claimed evaluation of the assembled query list is
represented over `vanDen` at the `hEvalBudget` cap — the entries the multiopen's member
evaluation lists look up. -/
theorem queryEval_rep (ic : Fin shape.numProofs → ℕ → G)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) (m : ℕ) :
    NumeratorRep vk (vanDen vk)
      (fun pt => ((assembleQueries vk ic (Point.toProofString pt base)
          (Point.toChallenges pt)).getD m default).eval)
      (hEvalBudget shape vk) := by
  have hlist : ListRep vk (vanDen vk)
      (fun pt => (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt)).map (·.eval)) (hEvalBudget shape vk) :=
    ⟨queryEvalFns vk base, fun pt => assembleQueries_map_eval vk base ic pt,
      queryEvalFns_rep base hchunkW hchunks hS⟩
  refine (hlist.getD m).congr_event fun pt _ => ?_
  have h0 : (default : VerifierQuery shape.k Fp G).eval = 0 := rfl
  rw [← h0]
  exact getD_map_eq (fun q : VerifierQuery shape.k Fp G => q.eval) _ m default

end EvalRep

/-! ## The compression-fold value side -/

section CompressVals

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}
variable {den : MvPolynomial (ScalarSlot shape) Fp}

/-- The value fold of `compressSet` over fixed member evaluation-function lists, with a general
accumulator: entries stay represented, each member costing one `x₁` degree. -/
theorem compressVals_rep_aux {E : ℕ} :
    ∀ (evsFns : List (List (Point shape → Fp))),
      (∀ l ∈ evsFns, ∀ f ∈ l, NumeratorRep vk den f E) →
      ∀ (accFns : List (Point shape → Fp)) (a : ℕ),
        (∀ f ∈ accFns, NumeratorRep vk den f a) →
      ∀ (powFn : Point shape → Fp) (c : ℕ), NumeratorRep vk 1 powFn c →
      ListRep vk den
        (fun pt => ((evsFns.map (List.map (· pt))).foldl
            (fun (st : List Fp × Fp) evs =>
              ((st.1.zip evs).map (fun e => e.1 + e.2 * st.2), st.2 * pt ScalarSlot.x1))
            (accFns.map (· pt), powFn pt)).1)
        (max a (E + c) + evsFns.length) := by
  intro evsFns
  induction evsFns with
  | nil =>
    intro _ accFns a hacc powFn c _
    refine ListRep.mono (le_max_left a (E + c)) ?_
    exact ⟨accFns, fun pt => rfl, hacc⟩
  | cons evs t ih =>
    intro h accFns a hacc powFn c hpow
    have hevs := h evs List.mem_cons_self
    have ht := fun l hl => h l (List.mem_cons_of_mem _ hl)
    set accFns' : List (Point shape → Fp) :=
      (accFns.zip evs).map (fun fg => fun pt => fg.1 pt + fg.2 pt * powFn pt) with haccFns'
    have hacc' : ∀ f ∈ accFns', NumeratorRep vk den f (max a (E + c)) := by
      intro f hf
      obtain ⟨fg, hfg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨fg1, fg2⟩ := fg
      obtain ⟨hm1, hm2⟩ := List.of_mem_zip hfg
      have h1 := hacc fg1 hm1
      have h2 := (hevs fg2 hm2).mul hpow
      have h2' : NumeratorRep vk den (fun pt => fg2 pt * powFn pt) (E + c) :=
        h2.denCongr (mul_one den)
      exact ((h1.mono (le_max_left _ _)).add (h2'.mono (le_max_right _ _))).mono
        (le_of_eq (max_self _))
    have hpow' : NumeratorRep vk 1 (fun pt => powFn pt * pt ScalarSlot.x1) (c + 1) :=
      ((hpow.mul (NumeratorRep.var ScalarSlot.x1)).denCongr (mul_one 1))
    have hstep := ih ht accFns' (max a (E + c)) hacc'
      (fun pt => powFn pt * pt ScalarSlot.x1) (c + 1) hpow'
    refine (hstep.congr fun pt => ?_).mono ?_
    · show ((t.map (List.map (· pt))).foldl _ (accFns'.map (· pt), _)).1 = _
      have hzip : accFns'.map (· pt)
          = ((accFns.map (· pt)).zip (evs.map (· pt))).map (fun e => e.1 + e.2 * powFn pt) := by
        rw [haccFns', List.map_map, List.zip_map, List.map_map]
        rfl
      rw [hzip]
      rfl
    · simp only [List.length_cons]
      omega

/-- The value side of `compressSet` over fixed member evaluation-function lists: a represented
per-point vector, each member costing one `x₁` degree. -/
theorem compressVals_rep {E : ℕ} (evsFns : List (List (Point shape → Fp)))
    (h : ∀ l ∈ evsFns, ∀ f ∈ l, NumeratorRep vk den f E) (n : ℕ) :
    ListRep vk den
      (fun pt => ((evsFns.map (List.map (· pt))).foldl
          (fun (st : List Fp × Fp) evs =>
            ((st.1.zip evs).map (fun e => e.1 + e.2 * st.2), st.2 * pt ScalarSlot.x1))
          (List.replicate n (0 : Fp), (1 : Fp))).1)
      (E + evsFns.length) := by
  have h0 : ∀ f ∈ List.replicate n (fun _ : Point shape => (0 : Fp)),
      NumeratorRep vk den f 0 := by
    intro f hf
    rw [List.eq_of_mem_replicate hf]
    exact ⟨0, by simp, fun pt _ => by simp⟩
  have h1 : NumeratorRep vk 1 (fun _ : Point shape => (1 : Fp)) 0 := NumeratorRep.const 1
  have := compressVals_rep_aux evsFns h (List.replicate n (fun _ => 0)) 0 h0
    (fun _ => 1) 0 h1
  refine (this.congr fun pt => ?_).mono (by omega)
  rw [List.map_replicate]

end CompressVals

/-! ## The reified per-set data

On the good event the grouping is the fixed reference table, so the per-set combinatorics — the
rotation class of every opened point and the flat evaluation positions of every member — are
verifying-key constants. -/

section Reified

variable (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G)

/-- The reference grouping's sets: fixed member data per point set. -/
def refSetsL : List (List (CommitmentRef shape.k ℕ ℕ × List ℕ)) :=
  (constructIntermediateSets (refTable shape vk)).sets

/-- The reference grouping's point-class lists per set. -/
def refPointsL : List (List ℕ) :=
  (constructIntermediateSets (refTable shape vk)).points

/-- The number of point sets (equal to `shape.numPointSets` under `VkSymbolicFacts`). -/
def numSetsD : ℕ := (refSetsL shape vk).length

/-- One set's opened rotations: its point classes decoded through `rotClasses`. -/
def classRotsL (si : ℕ) : List ℤ :=
  ((refPointsL shape vk).getD si []).map (fun i => (rotClasses shape vk).getD i 0)

/-- One set's member evaluation-position lists. -/
def memberEvalIdx (si : ℕ) : List (List ℕ) :=
  ((refSetsL shape vk).getD si []).map (·.2)

/-- The reference table's point stream: rotation-class indices over the flat positions. -/
theorem refTable_map_point :
    (refTable shape vk).map (·.point)
      = (List.range (queryCommIds shape vk).length).map
          (fun n => rotIdx shape vk ((queryRots shape vk).getD n 0)) := by
  rw [refTable, List.map_map]
  rfl

/-- Decoding a stream rotation's class index recovers the rotation. -/
theorem rotClasses_getD_rotIdx {r : ℤ} (hr : r ∈ queryRots shape vk) :
    (rotClasses shape vk).getD (rotIdx shape vk r) 0 = r := by
  have hmem : r ∈ rotClasses shape vk := mem_dedupFold.mpr hr
  have h := getElem?_findIdx_self (l := rotClasses shape vk) (x := r) hmem
  rw [rotIdx, List.getD_eq_getElem?_getD, h]
  rfl

/-- Every reference point-class index is a stream rotation's class index. -/
theorem refPoints_mem_spec (si : ℕ) :
    ∀ i ∈ (refPointsL shape vk).getD si [],
      ∃ r ∈ queryRots shape vk, i = rotIdx shape vk r := by
  intro i hi
  have himem : i ∈ (refTable shape vk).map (·.point) := by
    rcases lt_or_ge si (refPointsL shape vk).length with hsi | hsi
    · refine constructIntermediateSets_points_subset (refTable shape vk)
        ((refPointsL shape vk).getD si []) ?_ i hi
      rw [List.getD_eq_getElem _ _ hsi]
      exact List.getElem_mem hsi
    · rw [List.getD_eq_default _ _ hsi] at hi
      exact absurd hi (List.not_mem_nil)
  rw [refTable_map_point] at himem
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp himem
  rw [List.mem_range] at hn
  have hnR : n < (queryRots shape vk).length := by
    rw [queryRots_length]
    exact hn
  refine ⟨(queryRots shape vk).getD n 0, ?_, rfl⟩
  rw [List.getD_eq_getElem _ _ hnR]
  exact List.getElem_mem hnR

/-- Every opened rotation of a set is a stream rotation. -/
theorem classRotsL_mem (si : ℕ) :
    ∀ r ∈ classRotsL shape vk si, r ∈ queryRots shape vk := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  obtain ⟨r₀, hr₀, rfl⟩ := refPoints_mem_spec shape vk si i hi
  rw [rotClasses_getD_rotIdx shape vk hr₀]
  exact hr₀

/-- Every reference point-class index is in range of the class list. -/
theorem refPoints_lt (si : ℕ) :
    ∀ i ∈ (refPointsL shape vk).getD si [], i < (rotClasses shape vk).length := by
  intro i hi
  obtain ⟨r₀, hr₀, rfl⟩ := refPoints_mem_spec shape vk si i hi
  exact List.findIdx_lt_length_of_exists ⟨r₀, mem_dedupFold.mpr hr₀, by simp⟩

/-- One set's opened rotations are distinct: the class-index list is duplicate-free and decoding
is injective on in-range indices. -/
theorem classRotsL_nodup (si : ℕ) : (classRotsL shape vk si).Nodup := by
  have hnd : ((refPointsL shape vk).getD si []).Nodup :=
    constructIntermediateSets_points_nodup (refTable shape vk) si
  refine List.Nodup.map_on ?_ hnd
  intro i₁ h₁ i₂ h₂ hEq
  have hi₁ := refPoints_lt shape vk si i₁ h₁
  have hi₂ := refPoints_lt shape vk si i₂ h₂
  rw [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at hEq
  exact (List.Nodup.getElem_inj_iff (dedupFold_nodup _)).mp hEq

/-- The `x₃`-avoidance factor of an enumerated rotation is an enumerated denominator factor. -/
theorem x3Factor_mem_denFactors {r : ℤ} (hr : r ∈ queryRotations vk) :
    (X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp)
      ∈ denFactors vk := by
  simp only [denFactors, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))

/-- The bare `x` is an enumerated denominator factor. -/
theorem xFactor_mem_denFactors :
    (X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp) ∈ denFactors vk := by
  simp [denFactors]

/-! ### The per-set and opening denominators -/

/-- One set's denominator: the interpolation's cleared `x`-power and the set's `x₃`-avoidance
factors. -/
noncomputable def setDen (si : ℕ) : MvPolynomial (ScalarSlot shape) Fp :=
  X ScalarSlot.x ^ ((classRotsL shape vk si).length - 1)
    * ((classRotsL shape vk si).map
        (fun r => X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x)).prod

/-- The full opening denominator: the vanishing denominator and every set's denominator. -/
noncomputable def openDen : MvPolynomial (ScalarSlot shape) Fp :=
  vanDen vk * ∏ si ∈ Finset.range (numSetsD shape vk), setDen shape vk si

/-- Every set denominator is a product of enumerated factors. -/
theorem setDen_mem (si : ℕ) :
    setDen shape vk si ∈ Submonoid.closure {φ | φ ∈ denFactors vk} := by
  have hx : (X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp)
      ∈ Submonoid.closure {φ | φ ∈ denFactors vk} :=
    Submonoid.subset_closure (xFactor_mem_denFactors shape vk)
  have hgen : ∀ (l : List ℤ), (∀ r ∈ l, r ∈ queryRots shape vk) →
      ((l.map (fun r => X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x :
          ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod)
        ∈ Submonoid.closure {φ | φ ∈ denFactors vk} := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil]
      exact one_mem _
    | cons r t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      refine mul_mem (Submonoid.subset_closure ?_)
        (ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      exact x3Factor_mem_denFactors shape vk
        (queryRots_mem_queryRotations vk r (h r List.mem_cons_self))
  exact mul_mem (pow_mem hx _) (hgen _ (classRotsL_mem shape vk si))

/-- The opening denominator is a product of enumerated factors. -/
theorem openDen_mem : openDen shape vk ∈ Submonoid.closure {φ | φ ∈ denFactors vk} := by
  refine mul_mem (vanDen_mem (vk := vk)) ?_
  exact prod_mem (fun si _ => setDen_mem shape vk si)

/-- The summed class sizes: the total `x₃`-factor count across the sets. -/
def classBudget : ℕ :=
  ∑ si ∈ Finset.range (numSetsD shape vk), (classRotsL shape vk si).length

/-- Degree budget for the opening denominator. -/
def openDenBudget : ℕ := lagBudget vk + 2 * classBudget shape vk

/-- Every `x₃`-avoidance factor has total degree at most one. -/
theorem x3Factor_totalDegree_le (r : ℤ) :
    ((X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x :
      MvPolynomial (ScalarSlot shape) Fp)).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  refine max_le (by simp [totalDegree_X]) (le_trans (totalDegree_mul _ _) ?_)
  simp [totalDegree_X, totalDegree_C]

/-- One set denominator's degree is at most twice the set's class size. -/
theorem setDen_totalDegree_le (si : ℕ) :
    (setDen shape vk si).totalDegree ≤ 2 * (classRotsL shape vk si).length := by
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 : ((X ScalarSlot.x ^ ((classRotsL shape vk si).length - 1) :
      MvPolynomial (ScalarSlot shape) Fp)).totalDegree
      ≤ (classRotsL shape vk si).length - 1 := by
    simp [totalDegree_X_pow]
  have h2 : (((classRotsL shape vk si).map
      (fun r => X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x :
        ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod).totalDegree
      ≤ (classRotsL shape vk si).length := by
    induction classRotsL shape vk si with
    | nil => simp
    | cons r t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      refine le_trans (totalDegree_mul _ _) ?_
      have := x3Factor_totalDegree_le shape vk r
      omega
  omega

/-- The opening denominator's degree stays under its budget. -/
theorem openDen_totalDegree_le : (openDen shape vk).totalDegree ≤ openDenBudget shape vk := by
  rw [openDen, openDenBudget]
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 := vanDen_totalDegree_le (vk := vk)
  have h2 : ((∏ si ∈ Finset.range (numSetsD shape vk), setDen shape vk si)).totalDegree
      ≤ 2 * classBudget shape vk := by
    refine le_trans (totalDegree_finsetProd _ _) ?_
    rw [classBudget, Finset.mul_sum]
    exact Finset.sum_le_sum fun si _ => setDen_totalDegree_le shape vk si
  omega

end Reified

/-! ## Interpolation at `x₃`

`lagrangeEval` over one set's opened points `x·ω^r`: the pair differences factor as
`x·(ω^{rᵢ} − ω^{rⱼ})` — nonzero constants by rotation-power injectivity times the enumerated
bare-`x` factor — so each basis value clears into an `x`-power denominator, and the interpolant
is represented over `den · x^(a−1)`. -/

section Lagrange

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}

/-- Removing one in-range index from a range costs exactly one element. -/
theorem length_filter_ne_range {n i : ℕ} (hi : i < n) :
    ((List.range n).filter (fun j => !decide (j = i))).length = n - 1 := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    by_cases h : i = n
    · subst h
      have hall : (List.range i).filter (fun j => !decide (j = i)) = List.range i := by
        refine List.filter_eq_self.mpr ?_
        intro j hj
        rw [List.mem_range] at hj
        simp [Nat.ne_of_lt hj]
      simp [hall]
    · have hi' : i < n := by omega
      rw [List.length_append, ih hi']
      have hb : (List.filter (fun j => !decide (j = i)) [n]).length = 1 := by
        simp [Ne.symm h]
      rw [hb]
      omega

/-- The Lagrange basis-value fold, accumulator-generalized: every `j ≠ i` step multiplies by an
`(x₃ − x·ω^{r_j})` numerator and clears one pair difference into the bare-`x` denominator. -/
theorem lagrange_li_rep (rs : List ℤ)
    (hrs : ∀ r ∈ rs, r ∈ queryRots shape vk)
    (hinj : ∀ r ∈ queryRots shape vk, ∀ r' ∈ queryRots shape vk,
      vk.omega ^ r = vk.omega ^ r' → r = r')
    (hnd : rs.Nodup) (i : ℕ) (hi : i < rs.length) :
    ∀ (js : List ℕ), (∀ j ∈ js, j < rs.length) →
    ∀ (accFn : Point shape → Fp) (b e : ℕ),
      NumeratorRep vk (X ScalarSlot.x ^ e) accFn b →
      NumeratorRep vk
        (X ScalarSlot.x ^ (e + (js.filter (fun j => !decide (j = i))).length))
        (fun pt => js.foldl (fun p j =>
            if j = i then p
            else p * (pt ScalarSlot.x3
                - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0)
              / ((rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD i 0
                - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0))
          (accFn pt))
        (b + (js.filter (fun j => !decide (j = i))).length) := by
  intro js
  induction js with
  | nil =>
    intro _ accFn b e hacc
    simpa using hacc
  | cons j t ih =>
    intro hjs accFn b e hacc
    by_cases hji : j = i
    · subst hji
      have ht := ih (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) accFn b e hacc
      have hfl : ((j :: t).filter (fun j' => !decide (j' = j))).length
          = (t.filter (fun j' => !decide (j' = j))).length := by
        simp
      rw [hfl]
      refine ht.congr_event fun pt _ => ?_
      rw [List.foldl_cons, if_pos rfl]
    · have hjlt := hjs j List.mem_cons_self
      have hrjm : rs[j] ∈ rs := List.getElem_mem hjlt
      have hrim : rs[i] ∈ rs := List.getElem_mem hi
      have hcne : vk.omega ^ rs[i] - vk.omega ^ rs[j] ≠ 0 := by
        refine sub_ne_zero.mpr fun hEq => ?_
        have hij := (List.Nodup.getElem_inj_iff hnd).mp
          (hinj rs[i] (hrs _ hrim) rs[j] (hrs _ hrjm) hEq)
        exact hji hij.symm
      -- the step value, in toolkit form
      have h1 : NumeratorRep vk (X ScalarSlot.x ^ e)
          (fun pt => accFn pt * (pt ScalarSlot.x3 - vk.omega ^ rs[j] * pt ScalarSlot.x))
          (b + 1) := by
        have hf := (NumeratorRep.ofPoly (vk := vk)
            (X ScalarSlot.x3 - C (vk.omega ^ rs[j]) * X ScalarSlot.x)).mono
          (x3Factor_totalDegree_le shape vk rs[j])
        refine ((hacc.mul hf).denCongr (mul_one _)).congr_event fun pt _ => ?_
        simp
      have h2 := h1.smul (vk.omega ^ rs[i] - vk.omega ^ rs[j])⁻¹
      have h3 := h2.divFactor (X ScalarSlot.x) (xFactor_mem_denFactors shape vk)
      have h4 := h3.denCongr (pow_succ (X ScalarSlot.x) e).symm
      have hstep : NumeratorRep vk (X ScalarSlot.x ^ (e + 1))
          (fun pt => accFn pt * (pt ScalarSlot.x3
              - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0)
            / ((rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD i 0
              - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0))
          (b + 1) := by
        refine h4.congr_event fun pt _ => ?_
        have hgj : (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0
            = pt ScalarSlot.x * vk.omega ^ rs[j] := by
          rw [List.getD_eq_getElem _ _ (by simpa using hjlt), List.getElem_map]
        have hgi : (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD i 0
            = pt ScalarSlot.x * vk.omega ^ rs[i] := by
          rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
        rw [hgj, hgi, ← mul_sub, div_eq_mul_inv, mul_inv]
        simp only [eval_X]
        ring
      have ht := ih (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) _ (b + 1) (e + 1) hstep
      have hfl : ((j :: t).filter (fun j' => !decide (j' = i))).length
          = (t.filter (fun j' => !decide (j' = i))).length + 1 := by
        simp [hji]
      rw [hfl]
      have hden : (X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp)
          ^ (e + 1 + (t.filter (fun j' => !decide (j' = i))).length)
          = X ScalarSlot.x ^ (e + ((t.filter (fun j' => !decide (j' = i))).length + 1)) := by
        rw [show e + 1 + (t.filter (fun j' => !decide (j' = i))).length
          = e + ((t.filter (fun j' => !decide (j' = i))).length + 1) from by omega]
      refine ((ht.denCongr hden).congr_event fun pt _ => ?_).mono (by omega)
      rw [List.foldl_cons, if_neg hji]

/-- **Stage 7.** The Lagrange interpolant of a represented evaluation vector at one set's opened
points, represented over `den · x^(a−1)`. -/
theorem lagrangeEval_rep {den : MvPolynomial (ScalarSlot shape) Fp} {E : ℕ} (rs : List ℤ)
    (hrs : ∀ r ∈ rs, r ∈ queryRots shape vk)
    (hinj : ∀ r ∈ queryRots shape vk, ∀ r' ∈ queryRots shape vk,
      vk.omega ^ r = vk.omega ^ r' → r = r')
    (hnd : rs.Nodup) (evals : Point shape → List Fp) (hev : ListRep vk den evals E) :
    NumeratorRep vk (den * X ScalarSlot.x ^ (rs.length - 1))
      (fun pt => lagrangeEval (pt ScalarSlot.x3)
        (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)) (evals pt))
      (E + rs.length) := by
  classical
  set n := rs.length with hn
  -- the per-index terms, as fixed represented functions
  set termFn : ℕ → Point shape → Fp := fun i pt =>
    (evals pt).getD i 0 * (List.range n).foldl (fun p j =>
        if j = i then p
        else p * (pt ScalarSlot.x3
            - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0)
          / ((rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD i 0
            - (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).getD j 0)) 1
    with htermFn
  have hterm : ∀ i ∈ List.range n, NumeratorRep vk (den * X ScalarSlot.x ^ (n - 1))
      (termFn i) (E + n) := by
    intro i hi
    rw [List.mem_range] at hi
    have hone : NumeratorRep vk ((X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp) ^ 0)
        (fun _ => (1 : Fp)) 0 := by
      refine (NumeratorRep.const 1).denCongr ?_
      rw [pow_zero]
    have hli := lagrange_li_rep rs hrs hinj hnd i hi (List.range n)
      (fun j hj => by simpa [hn] using List.mem_range.mp hj) _ 0 0 hone
    rw [length_filter_ne_range hi] at hli
    have hmul := (hev.getD i).mul hli
    have hden : (den * (X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp) ^ (0 + (n - 1)))
        = den * X ScalarSlot.x ^ (n - 1) := by
      rw [Nat.zero_add]
    exact (hmul.denCongr hden).mono (by omega)
  have hsum := NumeratorRep.listSum ((List.range n).map termFn)
    (by
      intro f hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      exact hterm i hi)
  refine hsum.congr_event fun pt _ => ?_
  show (((List.range n).map termFn).map (· pt)).sum = _
  rw [lagrangeEval]
  simp only [List.length_map, ← hn]
  have hfold : (List.range n).foldl (fun acc i => acc + termFn i pt) 0
      = (((List.range n).map termFn).map (· pt)).sum := by
    rw [List.map_map]
    have h1 : (List.range n).foldl (fun acc i => acc + termFn i pt) 0
        = ((List.range n).map (fun i => termFn i pt)).foldl (· + ·) 0 := by
      rw [List.foldl_map]
    rw [h1, foldl_add_eq_add_sum, zero_add]
    rfl
  rw [← hfold]

end Lagrange

/-! ## The reified value functions and their representations -/

section ValueFn

variable {shape : Shape} {G : Type*} [Inhabited G]
variable (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
variable (base : ProofString shape Fp G)

/-- The claimed `u`-value of a set position: the `multiopenU` slot, `0` past the set count. -/
def uAt (si : ℕ) : Point shape → Fp := fun pt =>
  (List.ofFn (fun u : Fin shape.numPointSets => pt (ScalarSlot.multiopenU u))).getD si 0

/-- One flat query position's claimed evaluation. -/
def queryEvalAt (m : ℕ) : Point shape → Fp := fun pt =>
  ((assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)).getD m
    default).eval

/-- One set's member evaluation functions: the fixed position lists, looked up in the
evaluation stream. -/
def memberEvalFns (si : ℕ) : List (List (Point shape → Fp)) :=
  (memberEvalIdx shape vk si).map (List.map (queryEvalAt vk ic base))

/-- One set's compressed evaluation vector, reified. -/
def cEvalsFn (si : ℕ) : Point shape → List Fp := fun pt =>
  (((memberEvalFns vk ic base si).map (List.map (· pt))).foldl
      (fun (st : List Fp × Fp) evs =>
        ((st.1.zip evs).map (fun e => e.1 + e.2 * st.2), st.2 * pt ScalarSlot.x1))
      (List.replicate ((classRotsL shape vk si).length) (0 : Fp), (1 : Fp))).1

/-- One set's interpolated evaluation at `x₃`, reified. -/
def rEvalFn (si : ℕ) : Point shape → Fp := fun pt =>
  lagrangeEval (pt ScalarSlot.x3)
    ((classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r))
    (cEvalsFn vk ic base si pt)

/-- One set's quotient-claim step of `multiopenEval`, reified. -/
def setEvalFn (si : ℕ) : Point shape → Fp := fun pt =>
  ((classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)).foldl
    (fun e point => e * (pt ScalarSlot.x3 - point)⁻¹)
    (uAt si pt - rEvalFn vk ic base si pt)

/-- The combined multiopen evaluation, reified as an `x₂`-fold over the sets. -/
def msmEvalFn : Point shape → Fp := fun pt =>
  (((List.range (numSetsD shape vk)).map (setEvalFn vk ic base)).map (· pt)).foldl
    (fun acc v => acc * pt ScalarSlot.x2 + v) 0

/-- The opening value, reified as an `x₄`-fold of the `u`-claims over the running evaluation. -/
def openValFn : Point shape → Fp := fun pt =>
  (((List.range (numSetsD shape vk)).map (fun si => uAt (shape := shape) si)).map (· pt)).foldl
    (fun acc v => acc * pt ScalarSlot.x4 + v) (msmEvalFn vk ic base pt)

/-! ### Budgets -/

/-- The largest member count across the reference sets. -/
def memberBudget : ℕ := ((refSetsL shape vk).map List.length).foldr max 0

/-- Degree budget for one set's quotient claim over `vanDen · setDen`. -/
def setEvalBudget : ℕ :=
  hEvalBudget shape vk + memberBudget vk + 2 * classBudget shape vk + lagBudget vk + 2

/-- Degree budget for the combined multiopen evaluation over `openDen`. -/
def mEvalBudget : ℕ :=
  setEvalBudget vk + 2 * classBudget shape vk + numSetsD shape vk + 1

/-- Degree budget for the opening value over `openDen`. -/
def vBudget : ℕ :=
  mEvalBudget vk + openDenBudget shape vk + numSetsD shape vk + 2

/-! ### Size facts -/

omit [Inhabited G] in
/-- Every set's class size is bounded by the summed class budget. -/
theorem classRotsL_length_le (si : ℕ) :
    (classRotsL shape vk si).length ≤ classBudget shape vk := by
  have hlen : (refPointsL shape vk).length = numSetsD shape vk :=
    (constructIntermediateSets_points_length (refTable shape vk)).symm
  rcases lt_or_ge si (numSetsD shape vk) with hsi | hsi
  · rw [classBudget]
    exact Finset.single_le_sum (f := fun sj => (classRotsL shape vk sj).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hsi)
  · rw [classRotsL, List.getD_eq_default _ _ (by omega)]
    simp

/-- Every set's member count is bounded by the member budget. -/
theorem memberEvalFns_length_le (si : ℕ) :
    (memberEvalFns vk ic base si).length ≤ memberBudget vk := by
  rw [memberEvalFns, List.length_map, memberEvalIdx, List.length_map]
  rcases lt_or_ge si (numSetsD shape vk) with hsi | hsi
  · refine le_foldr_max (List.mem_map.mpr ⟨(refSetsL shape vk).getD si [], ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ hsi]
    exact List.getElem_mem hsi
  · rw [List.getD_eq_default _ _ (by simpa [numSetsD] using hsi)]
    simp

/-! ### The representation chain -/

variable {vk}

omit [Inhabited G] in
/-- The `u`-claim of a set position is a degree-one slot read. -/
theorem uAt_rep (si : ℕ) : NumeratorRep vk 1 (uAt (shape := shape) si) 1 := by
  by_cases h : si < shape.numPointSets
  · refine (NumeratorRep.var (ScalarSlot.multiopenU ⟨si, h⟩)).congr_event fun pt _ => ?_
    rw [uAt, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · have h0 : NumeratorRep vk 1 (fun _ : Point shape => (0 : Fp)) 1 :=
      (NumeratorRep.const 0).mono (by omega)
    refine h0.congr_event fun pt _ => ?_
    rw [uAt, List.getD_eq_default _ _ (by simpa using h)]

omit [Inhabited G] in
/-- The `x₃`-clearing fold: dividing a represented accumulator by every opened point's
avoidance factor. -/
theorem invFactor_fold_rep :
    ∀ (rs : List ℤ), (∀ r ∈ rs, r ∈ queryRotations vk) →
    ∀ (den : MvPolynomial (ScalarSlot shape) Fp) (b : ℕ) (accFn : Point shape → Fp),
      NumeratorRep vk den accFn b →
    NumeratorRep vk (den * ((rs.map (fun r => X ScalarSlot.x3 - C (vk.omega ^ r)
        * X ScalarSlot.x : ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod))
      (fun pt => (rs.map (fun r => pt ScalarSlot.x * vk.omega ^ r)).foldl
        (fun e point => e * (pt ScalarSlot.x3 - point)⁻¹) (accFn pt))
      b := by
  intro rs
  induction rs with
  | nil =>
    intro _ den b accFn hacc
    simp only [List.map_nil, List.prod_nil, List.foldl_nil]
    exact hacc.denCongr (mul_one den).symm
  | cons r t ih =>
    intro hrs den b accFn hacc
    have hstep := hacc.divFactor _
      (x3Factor_mem_denFactors shape vk (hrs r List.mem_cons_self))
    have hstep' : NumeratorRep vk
        (den * (X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x))
        (fun pt => accFn pt * (pt ScalarSlot.x3 - pt ScalarSlot.x * vk.omega ^ r)⁻¹) b := by
      refine hstep.congr_event fun pt _ => ?_
      have hev : eval pt (X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x)
          = pt ScalarSlot.x3 - pt ScalarSlot.x * vk.omega ^ r := by
        simp [mul_comm]
      rw [hev]
    have ht := ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) _ _ _ hstep'
    have hden : den * (X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x)
          * ((t.map (fun r' => X ScalarSlot.x3 - C (vk.omega ^ r') * X ScalarSlot.x :
              ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod)
        = den * (((r :: t).map (fun r' => X ScalarSlot.x3 - C (vk.omega ^ r') * X ScalarSlot.x :
            ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod) := by
      rw [List.map_cons, List.prod_cons, mul_assoc]
    refine (ht.denCongr hden).congr_event fun pt _ => ?_
    rw [List.map_cons, List.foldl_cons]

variable (vk)

/-- One set's compressed evaluation vector is represented over `vanDen`. -/
theorem cEvalsFn_rep
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) (si : ℕ) :
    ListRep vk (vanDen vk) (cEvalsFn vk ic base si)
      (hEvalBudget shape vk + memberBudget vk) := by
  have hmem : ∀ l ∈ memberEvalFns vk ic base si, ∀ f ∈ l,
      NumeratorRep vk (vanDen vk) f (hEvalBudget shape vk) := by
    intro l hl f hf
    obtain ⟨ns, _, rfl⟩ := List.mem_map.mp hl
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hf
    exact queryEval_rep base ic hchunkW hchunks hS m
  have := compressVals_rep (vk := vk) (memberEvalFns vk ic base si) hmem
    ((classRotsL shape vk si).length)
  exact this.mono (Nat.add_le_add_left (memberEvalFns_length_le vk ic base si) _)

/-- One set's quotient claim is represented over `vanDen · setDen`. -/
theorem setEvalFn_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) (si : ℕ) :
    NumeratorRep vk (vanDen vk * setDen shape vk si) (setEvalFn vk ic base si)
      (setEvalBudget vk) := by
  have haLe := classRotsL_length_le vk si
  -- the interpolant
  have hr := lagrangeEval_rep (classRotsL shape vk si) (classRotsL_mem shape vk si)
    hf.rot_pow_inj (classRotsL_nodup shape vk si) _ (cEvalsFn_rep vk ic base hchunkW hchunks hS si)
  -- the u-claim, extended to the interpolant's denominator
  have hu : NumeratorRep vk
      (vanDen vk * X ScalarSlot.x ^ ((classRotsL shape vk si).length - 1))
      (uAt (shape := shape) si) (1 + (lagBudget vk + classBudget shape vk)) := by
    have h1 := (uAt_rep (vk := vk) si).extend
      (vanDen vk * X ScalarSlot.x ^ ((classRotsL shape vk si).length - 1))
    have h2 := h1.denCongr (one_mul _)
    refine h2.mono (Nat.add_le_add_left ?_ 1)
    refine le_trans (totalDegree_mul _ _) ?_
    have h3 := vanDen_totalDegree_le (vk := vk)
    have h4 : ((X ScalarSlot.x : MvPolynomial (ScalarSlot shape) Fp)
        ^ ((classRotsL shape vk si).length - 1)).totalDegree
        ≤ (classRotsL shape vk si).length := by
      simp only [totalDegree_X_pow]
      omega
    omega
  -- the seed
  have hseed := hu.sub hr
  -- the clearing fold
  have hfold := invFactor_fold_rep (classRotsL shape vk si)
    (fun r hr' => queryRots_mem_queryRotations vk r (classRotsL_mem shape vk si r hr'))
    _ _ _ hseed
  have hden : vanDen vk * X ScalarSlot.x ^ ((classRotsL shape vk si).length - 1)
        * (((classRotsL shape vk si).map
            (fun r => X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x :
              ℤ → MvPolynomial (ScalarSlot shape) Fp)).prod)
      = vanDen vk * setDen shape vk si := by
    rw [setDen, mul_assoc]
  refine ((hfold.denCongr hden).congr_event fun pt _ => rfl).mono ?_
  simp only [setEvalBudget]
  omega

/-- One set's quotient claim, extended to the full opening denominator. -/
theorem setEvalFn_openDen_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) {si : ℕ} (hsi : si < numSetsD shape vk) :
    NumeratorRep vk (openDen shape vk) (setEvalFn vk ic base si)
      (setEvalBudget vk + 2 * classBudget shape vk) := by
  have h1 := (setEvalFn_rep vk ic base hf hchunkW hchunks hS si).extend
    (∏ sj ∈ (Finset.range (numSetsD shape vk)).erase si, setDen shape vk sj)
  have hden : vanDen vk * setDen shape vk si
        * ∏ sj ∈ (Finset.range (numSetsD shape vk)).erase si, setDen shape vk sj
      = openDen shape vk := by
    rw [openDen, mul_assoc,
      Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hsi)]
  refine (h1.denCongr hden).mono (Nat.add_le_add_left ?_ _)
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum_of_subset (Finset.erase_subset ..)) ?_
  rw [classBudget, Finset.mul_sum]
  exact Finset.sum_le_sum fun sj _ => setDen_totalDegree_le shape vk sj

/-- The combined multiopen evaluation, represented over `openDen`. -/
theorem msmEvalFn_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) :
    NumeratorRep vk (openDen shape vk) (msmEvalFn vk ic base) (mEvalBudget vk) := by
  have hfns : ∀ f ∈ (List.range (numSetsD shape vk)).map (setEvalFn vk ic base),
      NumeratorRep vk (openDen shape vk) f
        (setEvalBudget vk + 2 * classBudget shape vk) := by
    intro f hfm
    obtain ⟨si, hsi, rfl⟩ := List.mem_map.mp hfm
    exact setEvalFn_openDen_rep vk ic base hf hchunkW hchunks hS (List.mem_range.mp hsi)
  have := NumeratorRep.foldl_scale_add ScalarSlot.x2 _ hfns
  refine (this.congr_event fun pt _ => rfl).mono ?_
  simp only [List.length_map, List.length_range, mEvalBudget]
  omega

/-- **The opening value, represented over `openDen`** — the `x₄`-fold of the `u`-claims over
the combined evaluation. -/
theorem openValFn_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) :
    NumeratorRep vk (openDen shape vk) (openValFn vk ic base) (vBudget vk) := by
  have hus : ∀ f ∈ (List.range (numSetsD shape vk)).map
      (fun si => uAt (shape := shape) si),
      NumeratorRep vk (openDen shape vk) f (1 + openDenBudget shape vk) := by
    intro f hfm
    obtain ⟨si, _, rfl⟩ := List.mem_map.mp hfm
    have h1 := (uAt_rep (vk := vk) si).extend (openDen shape vk)
    have h2 := h1.denCongr (one_mul _)
    exact h2.mono (Nat.add_le_add_left (openDen_totalDegree_le shape vk) 1)
  have := NumeratorRep.foldl_scale_add_aux ScalarSlot.x4 _ hus _ _
    (msmEvalFn_rep vk ic base hf hchunkW hchunks hS)
  refine (this.congr_event fun pt _ => rfl).mono ?_
  simp only [List.length_map, List.length_range, vBudget]
  omega

end ValueFn

/-! ## The plumbing: the pipeline value is the reified function on the good event -/

section Plumbing

variable {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
variable (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
variable (base : ProofString shape Fp G)

omit [DecidableEq G] in
/-- The value side of a decoded member is its positional evaluation lookups — independent of
the commitment branch. -/
theorem decodeMember_snd (qs : List (VerifierQuery shape.k Fp G))
    (x : CommitmentRef shape.k ℕ ℕ × List ℕ) :
    (decodeMember qs x).2 = x.2.map (fun m => (qs.getD m default).eval) := by
  obtain ⟨cr, ns⟩ := x
  cases cr <;> rfl

omit [DecidableEq G] [Inhabited G] in
/-- Decoding one set's point-class indices yields its opened rotations, scaled by `x`. -/
theorem points_decode (si : ℕ) (pt : Point shape) :
    ((refPointsL shape vk).getD si []).map
        (fun i => (((rotClasses shape vk).map
          (fun r => pt ScalarSlot.x * vk.omega ^ r))).getD i 0)
      = (classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r) := by
  rw [classRotsL, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hlt := refPoints_lt shape vk si i hi
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    List.getD_eq_getElem _ _ hlt]

omit [DecidableEq G] [Inhabited G] in
/-- The claimed `u`-list is the reified `u`-claims over the set positions. -/
theorem u_ofFn_eq (pt : Point shape) :
    List.ofFn ((Point.toProofString pt base).multiopenU)
      = (List.range shape.numPointSets).map (fun si => uAt (shape := shape) si pt) := by
  refine ofFn_eq_range_map _ _ fun i => ?_
  show pt (ScalarSlot.multiopenU i) = uAt i.val pt
  rw [uAt, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- Folds agree when their step functions agree on the list. -/
theorem foldl_congr_mem {α β : Type*} {l : List β} {f g : α → β → α} :
    (∀ acc, ∀ b ∈ l, f acc b = g acc b) → ∀ a : α, l.foldl f a = l.foldl g a := by
  induction l with
  | nil => intro _ a; rfl
  | cons x t ih =>
    intro h a
    rw [List.foldl_cons, List.foldl_cons, h a x List.mem_cons_self]
    exact ih (fun acc b hb => h acc b (List.mem_cons_of_mem _ hb)) _

omit [DecidableEq G] in
/-- One set's compressed evaluation vector, decoded: the pipeline's `compressSet` value side on
the decoded members is the reified `cEvalsFn`. -/
theorem cEvals_decode (pt : Point shape) (si : ℕ) :
    (compressSet (pt ScalarSlot.x1)
        (((refSetsL shape vk).getD si []).map (decodeMember
          (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))))
        (((classRotsL shape vk si).map
          (fun r => pt ScalarSlot.x * vk.omega ^ r)).length)).2
      = cEvalsFn vk ic base si pt := by
  rw [compressSet_snd]
  have hin : ((((refSetsL shape vk).getD si []).map (decodeMember
        (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt)))).map
        Prod.snd)
      = (memberEvalFns vk ic base si).map (List.map (· pt)) := by
    rw [memberEvalFns, memberEvalIdx, List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun mem _ => ?_
    simp only [Function.comp_apply]
    rw [decodeMember_snd, List.map_map]
    rfl
  rw [hin, cEvalsFn]
  simp only [List.length_map]

set_option maxHeartbeats 1000000 in
/-- **The plumbing.** On the good event, the pipeline's opening value — the second component of
`assembleOpening` exactly as `assembleFinalMsm` invokes it — is the reified `openValFn`. -/
theorem openingValue_eq (hf : VkSymbolicFacts shape vk) {pt : Point shape}
    (hgood : GoodEvent vk pt) :
    (assembleOpening (Point.toChallenges pt).x1 (Point.toChallenges pt).x2
        (Point.toChallenges pt).x3 (Point.toChallenges pt).x4
        ((Point.toProofString pt base).multiopenQPrime)
        (List.ofFn ((Point.toProofString pt base).multiopenU))
        (constructIntermediateSets (assembleQueries vk ic (Point.toProofString pt base)
          (Point.toChallenges pt)))
        (Msm.zero shape.k Fp G)).2
      = openValFn vk ic base pt := by
  classical
  have hS : numSetsD shape vk = shape.numPointSets := hf.ref_numSets
  have hPlen : (refPointsL shape vk).length = numSetsD shape vk :=
    (constructIntermediateSets_points_length (refTable shape vk)).symm
  -- the three normal forms
  have hsetsR : (constructIntermediateSets (assembleQueries vk ic
        (Point.toProofString pt base) (Point.toChallenges pt))).sets
      = (List.range (numSetsD shape vk)).map (fun si =>
          ((refSetsL shape vk).getD si []).map (decodeMember
            (assembleQueries vk ic (Point.toProofString pt base)
              (Point.toChallenges pt)))) := by
    rw [grouped_sets_eq vk ic base hf hgood]
    conv_lhs => rw [show (constructIntermediateSets (refTable shape vk)).sets
      = refSetsL shape vk from rfl, self_eq_range_map_getD (refSetsL shape vk)]
    rw [List.map_map]
    rfl
  have hptsR : (constructIntermediateSets (assembleQueries vk ic
        (Point.toProofString pt base) (Point.toChallenges pt))).points
      = (List.range (numSetsD shape vk)).map (fun si =>
          (classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)) := by
    rw [grouped_points_eq vk ic base hf hgood]
    conv_lhs => rw [show (constructIntermediateSets (refTable shape vk)).points
      = refPointsL shape vk from rfl, self_eq_range_map_getD (refPointsL shape vk)]
    rw [List.map_map, hPlen]
    refine List.map_congr_left fun si _ => ?_
    exact points_decode vk si pt
  have hu : List.ofFn ((Point.toProofString pt base).multiopenU)
      = (List.range (numSetsD shape vk)).map (fun si => uAt (shape := shape) si pt) := by
    rw [u_ofFn_eq base pt, hS]
  -- unfold and fuse: every list becomes a map over `range numSetsD`, and the challenge
  -- projections reduce to slot reads so both sides' fold steps align syntactically
  rw [assembleOpening, multiopenCombine_snd, hsetsR, hptsR, hu]
  simp only [List.map_map, zip_map_same, Function.comp_def, toChallenges_x1, toChallenges_x2,
    toChallenges_x3, toChallenges_x4]
  rw [multiopenEval, openValFn, msmEvalFn]
  simp only [List.map_map, List.foldl_map, Function.comp_def]
  -- identical steps: only the seeds — the two spellings of the combined evaluation — remain
  refine congrArg₂ (List.foldl _) ?_ rfl
  refine foldl_congr_mem (fun acc si hsi => ?_) 0
  congr 1
  rw [setEvalFn, rEvalFn, ← cEvals_decode vk ic base pt si, List.foldl_map]

/-- **The stage 6–9 capstone.** The opening value of the deployed assembly — the second
component of `assembleOpening` exactly as `assembleFinalMsm` invokes it, on the grouping of the
assembled queries — is represented over the opening denominator at the `vBudget` cap. This is
the input the IPA stage's `gScalars 0` representation consumes. -/
theorem openingValue_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hPerm : 1 ≤ shape.numPermutationSets) :
    NumeratorRep vk (openDen shape vk)
      (fun pt => (assembleOpening (Point.toChallenges pt).x1 (Point.toChallenges pt).x2
          (Point.toChallenges pt).x3 (Point.toChallenges pt).x4
          ((Point.toProofString pt base).multiopenQPrime)
          (List.ofFn ((Point.toProofString pt base).multiopenU))
          (constructIntermediateSets (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)))
          (Msm.zero shape.k Fp G)).2)
      (vBudget vk) := by
  refine (openValFn_rep vk ic base hf hchunkW hchunks hPerm).congr_event fun pt hgood => ?_
  exact (openingValue_eq vk ic base hf hgood).symm

end Plumbing

end Zcash.Snark
