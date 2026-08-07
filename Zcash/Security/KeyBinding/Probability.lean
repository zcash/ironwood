import Zcash.Common.UniformMeasure
import Zcash.Security.KeyBinding.Basic
import Zcash.Security.Common.Birthday
import Zcash.Snark.Soundness.FiatShamir.Adversary.OracleComp

/-!
# Key binding in the whole-table random-oracle model

The deterministic key-binding layer ends at a computed event: `CollisionUpToSign.ofBreak` turns
any key-binding `Break` into a ±-collision of the shifted combined final oracle at two distinct
queries, and `collision_mem_shifted_pm` places its output pair in the set `Birthday.lean` counts.
This module adds the probabilistic model that turns those counting facts into a probability
bound. The bound's denominator is the cardinality of the abstract randomness type `RIVK`.
Nothing here pins `|RIVK|`: at the intended Pallas instantiation `RIVK` is the scalar field,
so `|RIVK| = r_ℙ`, and an undersized instantiation would make the bounds vacuous.

The model samples the combined final `rivk`-derivation oracle `H^*` as one uniform table
`O : FinalQuery AK NK RIVK QK SK → RIVK`. A uniform table is the same as independent uniform outputs at
every query — the product structure of the uniform measure. (In Markov-category terms `PMF` is a
commutative monad, so samples reorder freely; see Fritz [eprint arXiv:1908.07021] and
`Mathlib.CategoryTheory.MarkovCategory` for the abstract setting.) The three constituent oracles
are the table's restrictions along the `FinalQuery` constructors (`FinalQuery.eval_restrict`).

The remaining data (the extract maps, the bases, `hfn`, `Hask`, `Hnk`) are fixed parameters. The shift
`shiftOf` reads only the query and these parameters, never the sampled table — so a shifted read
of the table at distinct queries is still a uniform pair. (The shift is a deterministic, a.k.a.
copy-preserving, map in the Markov-category sense.) The pair and union lemmas below are stated
for an arbitrary finite query domain and arbitrary shift function, for reuse by the Spendability
`H^rcm` collision.

Results (static model — the query set is fixed before the table is sampled):

* `pair_shifted_collision_measure_le` — a shifted ±-collision at one distinct query pair has
  probability at most `2/|F|`.
* `finset_shifted_collision_measure_le` — union bound over the `C(q,2)` unordered pairs of a
  query set of size at most `q`: probability at most `q·(q−1)/|F|`.
* `break_measure_le` — the key-binding capstone: an adversary whose witnesses' derivation
  queries land in the static set produces a `Break` with probability at most `q·(q−1)/|RIVK|`.
  This is ZIP 2005's `ε_kb` as sharpened in zcash/zips#1338. At the intended instantiation,
  `|RIVK|` is the Pallas group order `r_ℙ`.

Results (adaptive — a bounded-query machine choosing queries after seeing earlier answers, as
an `OracleComp` from the Fiat–Shamir layer):

* `CollidesDuring` / `collidesDuring_measure_le` — the history-carrying collision event, and
  the sum-over-steps bound `(2·m·Q + Q·(Q−1))/|F|` for a cache-avoiding `Q`-query machine with
  `m` recorded answers: the triangle sum `Σ 2·(j−1)` recovers the non-adaptive constant
  exactly.
* `queries_pair_collision_measure_le` — a `Q`-query machine's trace contains a shifted
  ±-colliding pair with probability at most `Q·(Q−1)/|F|`.
* `break_measure_le_adaptive` — the adaptive capstone, for a machine that queries its output
  witnesses' derivation inputs: `Q·(Q−1)/|RIVK|` (ZIP 2005's accounting).
* `break_measure_le_of_queryBound` — hypothesis-free: any `Q`-query machine, via
  `OracleComp.completing` appending the four derivation queries: `(Q+4)·(Q+3)/|RIVK|`.
* `uniform_triple_eval` — the triple↔table transport: the three derivation oracles drawn
  independently and uniformly assemble (`FinalQuery.eval`) into exactly the uniform whole
  table.
* `break_measure_le_mixture` / `break_measure_le_product` — the bound over the full
  probability space: adversary private randomness (any distribution) and the five oracle
  tables drawn independently, the tables uniformly; same `(Q+4)·(Q+3)/|RIVK|` bound.
-/

namespace Zcash.Security.KeyBinding

open Finset Zcash.Security.RandomOracle Zcash.Security.Birthday Zcash.Snark
open scoped ENNReal

variable {G F IVK AK NK RIVK ASK QK SK : Type*}

/-! ## Finiteness of the query space -/

/-- `FinalQuery` as the sum of its constructors' data. -/
def finalQueryEquiv : FinalQuery AK NK RIVK QK SK ≃ (QK × AK × NK) ⊕ SK ⊕ (RIVK × AK × NK) where
  toFun
    | .ext qk ak nk => .inl (qk, ak, nk)
    | .legacy sk => .inr (.inl sk)
    | .int rivk_ext ak nk => .inr (.inr (rivk_ext, ak, nk))
  invFun
    | .inl (qk, ak, nk) => .ext qk ak nk
    | .inr (.inl sk) => .legacy sk
    | .inr (.inr (rivk_ext, ak, nk)) => .int rivk_ext ak nk
  left_inv q := by cases q <;> rfl
  right_inv x := by rcases x with ⟨qk, ak, nk⟩ | sk | ⟨rivk_ext, ak, nk⟩ <;> rfl

instance [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype QK] [Fintype SK] :
    Fintype (FinalQuery AK NK RIVK QK SK) :=
  Fintype.ofEquiv _ finalQueryEquiv.symm

/-- Assembling the combined final oracle from a table's constructor restrictions gives back the
table. -/
theorem eval_restrict (O : FinalQuery AK NK RIVK QK SK → RIVK) :
    FinalQuery.eval (fun sk => O (.legacy sk)) (fun qk ak nk => O (.ext qk ak nk))
      (fun rivk_ext ak nk => O (.int rivk_ext ak nk)) = O := by
  funext q; cases q <;> rfl

/-! ## The per-pair and union bounds, over an arbitrary finite query domain -/

section Generic

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [Field F] [Fintype F] [DecidableEq F]

omit [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F] in
/-- `=±` is symmetric. -/
theorem eqUpToSign_symm {x y : F} (h : x =± y) : y =± x :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg]))

/-- **Non-adaptive per-pair bound.** For distinct queries `a ≠ b` and any shift `s` fixed
independently of the table, a uniform table's shifted outputs at `a` and `b` ±-collide with
probability at most `2/|F|`: the pair read is uniform on `F × F`
(`uniformOfFintype_map_precomp_injective`), and the shifted collision set has at most
`2·|F|` elements (`card_shifted_pm_collision_le`). -/
theorem pair_shifted_collision_measure_le (s : Q → F) {a b : Q} (hne : a ≠ b) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | s a + O a =± s b + O b}
      ≤ 2 / Fintype.card F := by
  have hφ : Function.Injective (![a, b] : Fin 2 → Q) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hpre : {O : Q → F | s a + O a =± s b + O b}
      = (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b])) ⁻¹'
          {p : F × F | s a + p.1 =± s b + p.2} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply]
  have hmap : (PMF.uniformOfFintype (Q → F)).map
        (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b]))
      = PMF.uniformOfFintype (F × F) := by
    rw [show (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b]))
          = ⇑(piFinTwoEquiv fun _ => F) ∘ (fun O : Q → F => O ∘ ![a, b]) from rfl,
      ← PMF.map_comp, uniformOfFintype_map_precomp_injective _ hφ,
      map_uniformOfFintype_equiv]
  rw [hmap, uniformOfFintype_toOuterMeasure_set]
  have hcard : Nat.card {p : F × F | s a + p.1 =± s b + p.2} ≤ 2 * Fintype.card F := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    exact card_shifted_pm_collision_le (s a) (s b)
  calc (Nat.card {p : F × F | s a + p.1 =± s b + p.2} : ℝ≥0∞) / Fintype.card (F × F)
      ≤ (2 * Fintype.card F : ℕ) / Fintype.card (F × F) := by
        gcongr
    _ = 2 / Fintype.card F := by
        rw [Fintype.card_prod]
        push_cast
        rw [ENNReal.mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_pos.ne')
          (ENNReal.natCast_ne_top _)]

/-- **Non-adaptive union bound.** A query set of size at most `q`, fixed before the table is
sampled, contains a shifted ±-colliding pair with probability at most `q·(q−1)/|F|`: sum the
per-pair bound over the `C(q,2)` unordered pairs (`Finset.powersetCard 2`). -/
theorem finset_shifted_collision_measure_le (s : Q → F) (Qs : Finset Q) {q : ℕ}
    (hq : Qs.card ≤ q) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ≤ (q * (q - 1) : ℕ) / Fintype.card F := by
  have hcover : {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ⊆ ⋃ t : ↥(Qs.powersetCard 2),
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b} := by
    rintro O ⟨a, ha, b, hb, hab, hpm⟩
    refine Set.mem_iUnion.2 ⟨⟨{a, b}, Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hab⟩⟩,
      ⟨a, ?_, b, ?_, hab, hpm⟩⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb)
    · simp
    · simp
  have hpair : ∀ t : ↥(Qs.powersetCard 2),
      (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b}
        ≤ 2 / Fintype.card F := by
    rintro ⟨t, ht⟩
    obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.1 ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    refine le_trans (MeasureTheory.measure_mono ?_) (pair_shifted_collision_measure_le s hab)
    rintro O ⟨x, hx, y, hy, hxy, hpm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hpm
    · exact eqUpToSign_symm hpm
    · exact absurd rfl hxy
  have hdvd : 2 ∣ q * (q - 1) := by
    rcases q with _ | m
    · simp
    · simpa [Nat.succ_sub_one, mul_comm] using (Nat.even_mul_succ_self m).two_dvd
  have h2 : q * (q - 1) = q.choose 2 * 2 := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel hdvd]
  calc (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ≤ (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          (⋃ t : ↥(Qs.powersetCard 2),
            {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b}) :=
        MeasureTheory.measure_mono hcover
    _ ≤ ∑' t : ↥(Qs.powersetCard 2), (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b} :=
        MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' _t : ↥(Qs.powersetCard 2), (2 / Fintype.card F : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum hpair
    _ = ((Qs.powersetCard 2).card : ℝ≥0∞) * (2 / Fintype.card F) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (q.choose 2 : ℝ≥0∞) * (2 / Fintype.card F) := by
        gcongr
        rw [Finset.card_powersetCard]
        exact_mod_cast Nat.choose_le_choose 2 hq
    _ = (q * (q - 1) : ℕ) / Fintype.card F := by
        rw [h2]
        push_cast
        rw [mul_div_assoc]

/-! ### The adaptive model

The adversary is now a bounded-query machine (`OracleComp`, shared with the Fiat–Shamir layer)
choosing each query after seeing earlier answers, run against the whole table. The event
carries the query history: at each step the fresh answer must avoid the at most `2·m` values
that ±-collide with one of the `m` recorded earlier answers, and summing the per-step budgets
over a `Q`-query run recovers the non-adaptive constant exactly — the triangle sum `Σ 2·(j−1)`
counts each unordered pair once. The measure induction mirrors `escapesDuringC_measure_le`
(fresh-answer conditioning via `uniformOfFintype_cond_point`); recording answers as history
*data* is what keeps each step's bad set independent of the sampled table.

This is the standard bad-event analysis of adaptive random-oracle queries. A close
textbook instance is the Davies–Meyer collision bound — Boneh and Shoup, *A Graduate Course
in Applied Cryptography*, v0.6, https://toc.cryptobook.us/, §8.5.3, Theorem 8.4. Their event `Z`
(some distinct query pair with colliding derived values) is this module's trace collision,
and their "reasonable adversary" normalization (`q' := q + 2` there, `n + 4` here) is the
`OracleComp.completing` transformation. The rendering differs in one respect: lazy sampling's
"each fresh answer is uniform" becomes conditioning at an unread coordinate of the eager
whole table. -/

/-- The answers at `t` that would ±-collide with a recorded `(query, answer)` pair: two
candidate values per pair, one per sign. A list representing the step's *bad set* (only
membership matters, but the list length `2·|σ|` is a convenient bound on the set's
cardinality; coinciding candidates merely leave the inequality slack, they do not
invalidate it). -/
def badList (s : Q → F) (σ : List (Q × F)) (t : Q) : List F :=
  σ.map (fun p => s p.1 + p.2 - s t) ++ σ.map (fun p => -(s p.1 + p.2) - s t)

omit [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F] in
theorem mem_badList {s : Q → F} {σ : List (Q × F)} {t : Q} {y : F} :
    y ∈ badList s σ t ↔ ∃ p ∈ σ, s t + y =± s p.1 + p.2 := by
  simp only [badList, List.mem_append, List.mem_map, EqUpToSign]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, hp, Or.inl (by ring)⟩
    · exact ⟨p, hp, Or.inr (by ring)⟩
  · rintro ⟨p, hp, h | h⟩
    · exact Or.inl ⟨p, hp, by linear_combination -h⟩
    · exact Or.inr ⟨p, hp, by linear_combination -h⟩

omit [Fintype Q] [DecidableEq Q] in
/-- One step's bad set has probability at most `2·m/|F|` for a history of length `m`. -/
theorem badList_measure_le (s : Q → F) (σ : List (Q × F)) (t : Q) :
    (PMF.uniformOfFintype F).toOuterMeasure {y : F | y ∈ badList s σ t}
      ≤ (2 * σ.length : ℕ) / Fintype.card F := by
  rw [uniformOfFintype_toOuterMeasure_set]
  have hcard : Nat.card {y : F | y ∈ badList s σ t} ≤ 2 * σ.length := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    calc (univ.filter fun y : F => y ∈ badList s σ t).card
        ≤ (badList s σ t).toFinset.card := by
          apply card_le_card
          intro y hy
          rw [mem_filter] at hy
          simpa [List.mem_toFinset] using hy.2
      _ ≤ (badList s σ t).length := (badList s σ t).toFinset_card_le
      _ ≤ 2 * σ.length := le_of_eq (by simp [badList, two_mul])
  gcongr

/-- Some query's answer lands in the escape set determined by the accumulated history: the
history-indexed generalization of `escapesDuringC` (which is the constant-budget case). The
history `σ` accumulates `(query, answer)` pairs as the run proceeds; recording answers as
history *data* keeps each step's escape set independent of the sampled table. -/
def escapesWithHistory {α : Type*} (esc : List (Q × F) → Q → Set F) :
    List (Q × F) → OracleComp Q F α → (Q → F) → Prop
  | _, .pure _, _ => False
  | σ, .query t k, O => O t ∈ esc σ t ∨ escapesWithHistory esc ((t, O t) :: σ) (k (O t)) O

omit [DecidableEq F] in
/-- **History-indexed escape bound.** If the escape set at history length `m` has probability
at most `f m`, a cache-avoiding `n`-query machine starting from history `σ` escapes with
probability at most `Σ_{i<n} f (|σ| + i)`: condition on each fresh answer in turn, mirroring
`escapesDuringC_measure_le`. -/
theorem escapesWithHistory_measure_le {α : Type*} (esc : List (Q × F) → Q → Set F)
    {f : ℕ → ℝ≥0∞} (hesc : ∀ (σ : List (Q × F)) (t : Q),
      (PMF.uniformOfFintype F).toOuterMeasure (esc σ t) ≤ f σ.length)
    {A : OracleComp Q F α} {n : ℕ} (hQ : A.QueryBound n)
    {σ : List (Q × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
      {O : Q → F | escapesWithHistory esc σ A (applyUpdates σ O)}
      ≤ ∑ i ∈ Finset.range n, f (σ.length + i) := by
  induction hQ generalizing σ with
  | pure a n =>
      have hempty : {O : Q → F |
          escapesWithHistory esc σ (OracleComp.pure a) (applyUpdates σ O)} = ∅ := by
        ext O; simp [escapesWithHistory]
      rw [hempty]; simp
  | @query t k n h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : Q → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsub : {O : Q → F |
            escapesWithHistory esc σ (OracleComp.query t k) (applyUpdates σ O)}
          ⊆ {O : Q → F | O t ∈ esc σ t}
            ∪ ⋃ u : F, {O : Q → F | O t = u ∧
                O ∈ {O' : Q → F | escapesWithHistory esc ((t, u) :: σ) (k u)
                  (applyUpdates ((t, u) :: σ) O')}} := by
        intro O hO
        simp only [escapesWithHistory, Set.mem_setOf_eq, happ O] at hO
        rcases hO with h1 | h2
        · exact Or.inl h1
        · refine Or.inr (Set.mem_iUnion.mpr ⟨O t, rfl, ?_⟩)
          have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
            rw [applyUpdates_cons, Function.update_eq_self]
          simp only [Set.mem_setOf_eq, hcons]
          exact h2
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (MeasureTheory.measure_union_le _ _) ?_
      have hfirst : (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          {O : Q → F | O t ∈ esc σ t} ≤ f σ.length :=
        uniformOfFintype_point_mem_blind_le t (fun _ => esc σ t)
          (fun _ _ => rfl) (fun _ => hesc σ t)
      have hsecond : (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          (⋃ u : F, {O : Q → F | O t = u ∧
            O ∈ {O' : Q → F | escapesWithHistory esc ((t, u) :: σ) (k u)
              (applyUpdates ((t, u) :: σ) O')}})
          ≤ ∑ i ∈ Finset.range n, f (σ.length + (i + 1)) := by
        refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
        rw [tsum_fintype]
        have hper : ∀ u : F, (PMF.uniformOfFintype (Q → F)).toOuterMeasure
            {O : Q → F | O t = u ∧
              O ∈ {O' : Q → F | escapesWithHistory esc ((t, u) :: σ) (k u)
                (applyUpdates ((t, u) :: σ) O')}}
            ≤ (∑ i ∈ Finset.range n, f (σ.length + (i + 1))) / Fintype.card F := by
          intro u
          have hblindE : ∀ (O : Q → F) (v : F),
              Function.update O t v ∈ {O' : Q → F | escapesWithHistory esc ((t, u) :: σ)
                (k u) (applyUpdates ((t, u) :: σ) O')}
              ↔ O ∈ {O' : Q → F | escapesWithHistory esc ((t, u) :: σ) (k u)
                (applyUpdates ((t, u) :: σ) O')} := by
            intro O v
            have hcons : applyUpdates ((t, u) :: σ) (Function.update O t v)
                = applyUpdates ((t, u) :: σ) O := by
              rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
            simp only [Set.mem_setOf_eq, hcons]
          rw [uniformOfFintype_cond_point t u _ hblindE]
          refine ENNReal.div_le_div_right ?_ _
          have hlen := ih u (hk u)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
        refine le_trans (Finset.sum_le_sum fun u _ => hper u) ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
          ENNReal.div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      calc (PMF.uniformOfFintype (Q → F)).toOuterMeasure {O : Q → F | O t ∈ esc σ t}
          + (PMF.uniformOfFintype (Q → F)).toOuterMeasure (⋃ u : F, _)
          ≤ f σ.length + ∑ i ∈ Finset.range n, f (σ.length + (i + 1)) :=
            add_le_add hfirst hsecond
        _ = ∑ i ∈ Finset.range (n + 1), f (σ.length + i) := by
            rw [Finset.sum_range_succ', add_comm]
            simp

/-- The run ±-collides during execution: the history-escape event at the `badList` sets. -/
def CollidesDuring {α : Type*} (s : Q → F) :
    List (Q × F) → OracleComp Q F α → (Q → F) → Prop :=
  escapesWithHistory (fun σ t => {y : F | y ∈ badList s σ t})

omit [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F] in
/-- A ±-colliding pair of distinct points, each either queried on the run or recorded in a
table-consistent history (but not both recorded), forces a collision during the run. -/
theorem CollidesDuring.of_pair {α : Type*} {s : Q → F} {O : Q → F} {A : OracleComp Q F α}
    {σ : List (Q × F)} (hσ : ∀ p ∈ σ, O p.1 = p.2) {a b : Q} (hab : a ≠ b)
    (ha : a ∈ A.queries O ∨ a ∈ σ.map Prod.fst)
    (hb : b ∈ A.queries O ∨ b ∈ σ.map Prod.fst)
    (hnot : a ∉ σ.map Prod.fst ∨ b ∉ σ.map Prod.fst)
    (hpm : s a + O a =± s b + O b) :
    CollidesDuring s σ A O := by
  induction A generalizing σ with
  | pure c =>
      simp only [OracleComp.queries, List.not_mem_nil, false_or] at ha hb
      rcases hnot with h | h
      · exact absurd ha h
      · exact absurd hb h
  | query t k ih =>
      have hconsist : ∀ p ∈ (t, O t) :: σ, O p.1 = p.2 := by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · rfl
        · exact hσ p hp
      simp only [OracleComp.queries, List.mem_cons] at ha hb
      show (O t ∈ {y : F | y ∈ badList s σ t}) ∨
        CollidesDuring s ((t, O t) :: σ) (k (O t)) O
      by_cases hat : a = t
      · subst hat
        by_cases hbh : b ∈ σ.map Prod.fst
        · obtain ⟨p, hp, hpfst⟩ := List.mem_map.1 hbh
          refine Or.inl (mem_badList.2 ⟨p, hp, ?_⟩)
          rw [← hσ p hp, hpfst]
          exact hpm
        · have hbtail : b ∈ (k (O a)).queries O := by
            rcases hb with hb | hb
            · rcases hb with rfl | hb
              · exact absurd rfl hab
              · exact hb
            · exact absurd hb hbh
          refine Or.inr (ih (O a) hconsist ?_ ?_ ?_)
          · exact Or.inr (by simp)
          · exact Or.inl hbtail
          · refine Or.inr ?_
            simp only [List.map_cons, List.mem_cons, not_or]
            exact ⟨Ne.symm hab, hbh⟩
      · by_cases hbt : b = t
        · subst hbt
          by_cases hah : a ∈ σ.map Prod.fst
          · obtain ⟨p, hp, hpfst⟩ := List.mem_map.1 hah
            refine Or.inl (mem_badList.2 ⟨p, hp, ?_⟩)
            rw [← hσ p hp, hpfst]
            exact eqUpToSign_symm hpm
          · have hatail : a ∈ (k (O b)).queries O := by
              rcases ha with ha | ha
              · rcases ha with rfl | ha
                · exact absurd rfl hat
                · exact ha
              · exact absurd ha hah
            refine Or.inr (ih (O b) hconsist ?_ ?_ ?_)
            · exact Or.inl hatail
            · exact Or.inr (by simp)
            · refine Or.inl ?_
              simp only [List.map_cons, List.mem_cons, not_or]
              exact ⟨hat, hah⟩
        · have ha' : a ∈ (k (O t)).queries O ∨ a ∈ ((t, O t) :: σ).map Prod.fst := by
            rcases ha with ha | ha
            · rcases ha with rfl | ha
              · exact absurd rfl hat
              · exact Or.inl ha
            · exact Or.inr (by simp [ha])
          have hb' : b ∈ (k (O t)).queries O ∨ b ∈ ((t, O t) :: σ).map Prod.fst := by
            rcases hb with hb | hb
            · rcases hb with rfl | hb
              · exact absurd rfl hbt
              · exact Or.inl hb
            · exact Or.inr (by simp [hb])
          have hnot' : a ∉ ((t, O t) :: σ).map Prod.fst
              ∨ b ∉ ((t, O t) :: σ).map Prod.fst := by
            rcases hnot with h | h
            · refine Or.inl ?_
              simp only [List.map_cons, List.mem_cons, not_or]
              exact ⟨hat, h⟩
            · refine Or.inr ?_
              simp only [List.map_cons, List.mem_cons, not_or]
              exact ⟨hbt, h⟩
          exact Or.inr (ih (O t) hconsist ha' hb' hnot')

omit [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F] in
/-- Gauss closed form for the collision budgets: `Σ_{i<n} 2·(m+i) = 2·m·n + n·(n−1)`. -/
theorem sum_two_mul_add (m n : ℕ) :
    ∑ i ∈ Finset.range n, 2 * (m + i) = 2 * m * n + n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.succ_sub_one]
      cases n with
      | zero => ring
      | succ k => rw [Nat.succ_sub_one]; ring

/-- **Adaptive sum-over-steps bound.** A cache-avoiding `n`-query machine with `m` recorded
answers collides during its run with probability at most `(2·m·n + n·(n−1))/|F|`: instantiate
the history-escape bound at the `badList` sets and close the Gauss sum. -/
theorem collidesDuring_measure_le {α : Type*} (s : Q → F)
    {A : OracleComp Q F α} {n : ℕ} (hQ : A.QueryBound n)
    {σ : List (Q × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
      {O : Q → F | CollidesDuring s σ A (applyUpdates σ O)}
      ≤ (2 * σ.length * n + n * (n - 1) : ℕ) / Fintype.card F := by
  refine le_trans (escapesWithHistory_measure_le _
    (f := fun m => (2 * m : ℕ) / Fintype.card F)
    (fun σ' t => badList_measure_le s σ' t) hQ hσ) (le_of_eq ?_)
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, sum_two_mul_add]

/-- **Adaptive trace bound.** An `n`-query machine's trace contains a shifted ±-colliding
distinct pair with probability at most `n·(n−1)/|F|` — the non-adaptive constant, adaptively. -/
theorem queries_pair_collision_measure_le {α : Type*} (s : Q → F)
    {A : OracleComp Q F α} {n : ℕ} (hQ : A.QueryBound n) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
      {O : Q → F | ∃ a ∈ A.queries O, ∃ b ∈ A.queries O, a ≠ b ∧ s a + O a =± s b + O b}
      ≤ (n * (n - 1) : ℕ) / Fintype.card F := by
  have hsub : {O : Q → F | ∃ a ∈ A.queries O, ∃ b ∈ A.queries O,
        a ≠ b ∧ s a + O a =± s b + O b}
      ⊆ {O : Q → F | CollidesDuring s [] (OracleComp.dedup [] A) O} := by
    rintro O ⟨a, ha, b, hb, hab, hpm⟩
    have ha' : a ∈ (OracleComp.dedup [] A).queries O :=
      mem_queries_dedup (by simp) (by simp) ha
    have hb' : b ∈ (OracleComp.dedup [] A).queries O :=
      mem_queries_dedup (by simp) (by simp) hb
    exact CollidesDuring.of_pair (by simp) hab (Or.inl ha') (Or.inl hb')
      (Or.inl (by simp)) hpm
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have hmain := collidesDuring_measure_le s (OracleComp.dedup_queryBound hQ [])
    (OracleComp.dedup_avoidsCache [] A)
  simpa using hmain

end Generic

/-! ## Averaging a pointwise bound -/

/-- A measure bound that holds for every conditioned slice survives averaging: if each
component `f a` gives the event measure at most `ε`, so does the mixture `p.bind f`. -/
theorem toOuterMeasure_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β) (s : Set β)
    {ε : ℝ≥0∞} (h : ∀ a, (f a).toOuterMeasure s ≤ ε) :
    (p.bind f).toOuterMeasure s ≤ ε := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s
      ≤ ∑' a, p a * ε := ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


/-! ## The derivation oracles as independent draws -/

section Transport

variable [Field RIVK] [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype QK] [Fintype SK]
variable [DecidableEq AK] [DecidableEq NK] [DecidableEq RIVK] [DecidableEq QK] [DecidableEq SK]

/-- Drawing the coordinates independently and uniformly is the uniform draw on the product. -/
theorem uniformOfFintype_prod {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β)
      = (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).map (Prod.mk a) := by
  refine PMF.ext fun x => ?_
  rw [PMF.bind_apply, tsum_eq_single x.1 fun a ha => ?_]
  · rw [PMF.map_apply, tsum_eq_single x.2 fun b hb => ?_]
    · simp only [Prod.mk.eta, if_pos, PMF.uniformOfFintype_apply, Fintype.card_prod,
        Nat.cast_mul]
      rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
    · exact if_neg fun h => hb (congrArg Prod.snd h).symm
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr fun b => if_neg fun h =>
      ha (congrArg Prod.fst h).symm, mul_zero]

/-- The three final `rivk`-derivation oracles assemble bijectively into whole tables
(`FinalQuery.eval`); the inverse is restriction along the constructors. -/
def evalEquiv :
    ((SK → RIVK) × (QK → AK → NK → RIVK) × (RIVK → AK → NK → RIVK))
      ≃ (FinalQuery AK NK RIVK QK SK → RIVK) where
  toFun H := FinalQuery.eval H.1 H.2.1 H.2.2
  invFun O := (fun sk => O (.legacy sk), fun qk ak nk => O (.ext qk ak nk),
    fun rivk_ext ak nk => O (.int rivk_ext ak nk))
  left_inv _H := rfl
  right_inv O := eval_restrict O

/-- **Triple↔table uniformity transport**, as a stated PMF equality: drawing the three final
`rivk`-derivation oracles independently and uniformly and combining them with
`FinalQuery.eval` is the uniform whole-table draw. -/
theorem uniform_triple_eval :
    ((PMF.uniformOfFintype (SK → RIVK)).bind fun Hleg =>
        (PMF.uniformOfFintype (QK → AK → NK → RIVK)).bind fun Hext =>
          (PMF.uniformOfFintype (RIVK → AK → NK → RIVK)).map fun Hint =>
            FinalQuery.eval Hleg Hext Hint)
      = PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK) := by
  rw [← map_uniformOfFintype_equiv (evalEquiv (QK := QK) (SK := SK) (AK := AK) (NK := NK)
    (RIVK := RIVK))]
  simp only [uniformOfFintype_prod, PMF.map_bind, PMF.map_comp]
  rfl

end Transport

/-! ## The key-binding capstone -/

section Capstone

variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [NoZeroSMulDivisors RIVK G]
variable [SMul ASK G]
variable [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype QK] [Fintype SK]
variable [DecidableEq AK] [DecidableEq NK] [DecidableEq RIVK] [DecidableEq QK] [DecidableEq SK]

omit [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype QK] [Fintype SK] in
/-- The queries at which `CollisionUpToSign.ofBreak` exhibits its collision are the witnesses'
derivation queries: the `rivk_ext`-derivation pair in the residual case, the final-query pair
otherwise. Stated over any `c` equal to the computed collision (`hc`), so that a consumer's
`set c := CollisionUpToSign.ofBreak ... with hc` supplies `hc` directly. -/
theorem ofBreak_queries {Extract : Extractor G IVK AK} {S : G} {hfn : AK → NK → RIVK}
    {Ggen : G} {hS : S ≠ 0}
    {H : Oracles AK NK RIVK ASK QK SK}
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    {hbrk : Break Extract S hfn Ggen H w₁ w₂}
    {c : RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn H
        (QK := QK) (SK := SK))}
    (hc : c = CollisionUpToSign.ofBreak Extract S hfn Ggen hS H hbrk) :
    (c.q₁ = extQueryOf Extract w₁ ∧ c.q₂ = extQueryOf Extract w₂) ∨
      (c.q₁ = finalQueryOf Extract w₁ ∧ c.q₂ = finalQueryOf Extract w₂) := by
  subst hc
  unfold CollisionUpToSign.ofBreak
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **Non-adaptive key-binding birthday bound.** Sample the combined final oracle as a uniform
table. An adversary —here, any pair of witness choices depending on the whole table— whose
witnesses' derivation queries lie in a set `Qs` of at most `q` queries *fixed in advance*,
produces a key-binding `Break` with probability at most `q·(q−1)/|RIVK|`. This is ZIP 2005's
`ε_kb` as sharpened in zcash/zips#1338. At the intended instantiation, `|RIVK|` is the
Pallas group order `r_ℙ`. -/
theorem break_measure_le (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (Ggen : G) (hS : S ≠ 0)
    (Hask : SK → ASK) (Hnk : SK → NK)
    (w₁ w₂ : (FinalQuery AK NK RIVK QK SK → RIVK) → Witness G IVK AK NK RIVK QK SK)
    (Qs : Finset (FinalQuery AK NK RIVK QK SK)) {q : ℕ} (hq : Qs.card ≤ q)
    (hqueries : ∀ O, finalQueryOf Extract (w₁ O) ∈ Qs ∧ finalQueryOf Extract (w₂ O) ∈ Qs ∧
      extQueryOf Extract (w₁ O) ∈ Qs ∧ extQueryOf Extract (w₂ O) ∈ Qs) :
    (PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK)).toOuterMeasure
        {O : FinalQuery AK NK RIVK QK SK → RIVK |
          Break Extract S hfn Ggen
            ⟨Hask, Hnk, fun sk => O (.legacy sk), fun qk ak nk => O (.ext qk ak nk),
              fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩ (w₁ O) (w₂ O)}
      ≤ (q * (q - 1) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (finset_shifted_collision_measure_le (shiftOf Extract Ggen hfn Hask Hnk) Qs hq)
  intro O hO
  obtain ⟨hf₁, hf₂, he₁, he₂⟩ := hqueries O
  set c := CollisionUpToSign.ofBreak Extract S hfn Ggen hS _ hO with hc
  have hq12 := ofBreak_queries hc
  have hpm : shiftOf Extract Ggen hfn Hask Hnk c.q₁ + O c.q₁
      =± shiftOf Extract Ggen hfn Hask Hnk c.q₂ + O c.q₂ := by
    have hp := c.pm
    simpa only [shiftedFinalOracle, eval_restrict] using hp
  refine ⟨c.q₁, ?_, c.q₂, ?_, c.ne, hpm⟩
  · rcases hq12 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
  · rcases hq12 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> assumption

/-! ### Adaptive capstones -/

/-- The derivation queries of an output witness pair: the final and `rivk_ext`-derivation
queries of both witnesses — the four points at which `CollisionUpToSign.ofBreak` can exhibit
its collision. -/
def derivQueries (Extract : Extractor G IVK AK)
    (w : Witness G IVK AK NK RIVK QK SK × Witness G IVK AK NK RIVK QK SK) : Fin 4 → FinalQuery AK NK RIVK QK SK :=
  ![finalQueryOf Extract w.1, finalQueryOf Extract w.2,
    extQueryOf Extract w.1, extQueryOf Extract w.2]

/-- **Adaptive key-binding bound (ZIP 2005 accounting).** An `n`-query machine that queries its
output witnesses' derivation inputs produces a key-binding `Break` with probability at most
`n·(n−1)/|RIVK|`, with the adversary's queries chosen adaptively. This is ZIP 2005's
`ε_kb` as sharpened in zcash/zips#1338. At the intended instantiation, `|RIVK|` is the
Pallas group order `r_ℙ`. -/
theorem break_measure_le_adaptive (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (Ggen : G) (hS : S ≠ 0)
    (Hask : SK → ASK) (Hnk : SK → NK)
    {A : OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
      (Witness G IVK AK NK RIVK QK SK × Witness G IVK AK NK RIVK QK SK)}
    {n : ℕ} (hQ : A.QueryBound n)
    (hqueries : ∀ (O : FinalQuery AK NK RIVK QK SK → RIVK) (i : Fin 4),
      derivQueries Extract (A.run O) i ∈ A.queries O) :
    (PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK)).toOuterMeasure
        {O : FinalQuery AK NK RIVK QK SK → RIVK |
          Break Extract S hfn Ggen
            ⟨Hask, Hnk, fun sk => O (.legacy sk), fun qk ak nk => O (.ext qk ak nk),
              fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩ (A.run O).1 (A.run O).2}
      ≤ (n * (n - 1) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (queries_pair_collision_measure_le (shiftOf Extract Ggen hfn Hask Hnk) hQ)
  intro O hO
  set c := CollisionUpToSign.ofBreak Extract S hfn Ggen hS _ hO with hc
  have hq12 := ofBreak_queries hc
  have hpm : shiftOf Extract Ggen hfn Hask Hnk c.q₁ + O c.q₁
      =± shiftOf Extract Ggen hfn Hask Hnk c.q₂ + O c.q₂ := by
    have hp := c.pm
    simpa only [shiftedFinalOracle, eval_restrict] using hp
  refine ⟨c.q₁, ?_, c.q₂, ?_, c.ne, hpm⟩
  · rcases hq12 with ⟨h1, -⟩ | ⟨h1, -⟩
    · simpa [derivQueries, h1] using hqueries O 2
    · simpa [derivQueries, h1] using hqueries O 0
  · rcases hq12 with ⟨-, h2⟩ | ⟨-, h2⟩
    · simpa [derivQueries, h2] using hqueries O 3
    · simpa [derivQueries, h2] using hqueries O 1

/-- **Adaptive key-binding bound, hypothesis-free.** Any `n`-query machine produces a
key-binding `Break` with probability at most `(n+4)·(n+3)/|F|`: complete the machine with its
output witnesses' four derivation queries (`OracleComp.completing`) and apply the adaptive
bound at budget `n + 4`. -/
theorem break_measure_le_of_queryBound (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (Ggen : G) (hS : S ≠ 0)
    (Hask : SK → ASK) (Hnk : SK → NK)
    {A : OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
      (Witness G IVK AK NK RIVK QK SK × Witness G IVK AK NK RIVK QK SK)}
    {n : ℕ} (hQ : A.QueryBound n) :
    (PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK)).toOuterMeasure
        {O : FinalQuery AK NK RIVK QK SK → RIVK |
          Break Extract S hfn Ggen
            ⟨Hask, Hnk, fun sk => O (.legacy sk), fun qk ak nk => O (.ext qk ak nk),
              fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩ (A.run O).1 (A.run O).2}
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  have hqueries : ∀ (O : FinalQuery AK NK RIVK QK SK → RIVK) (i : Fin 4),
      derivQueries Extract ((A.completing (derivQueries Extract)).run O) i
        ∈ (A.completing (derivQueries Extract)).queries O := by
    intro O i
    rw [OracleComp.run_completing, OracleComp.completing, OracleComp.queries_bind,
      OracleComp.queries_queryList]
    exact List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨i, rfl⟩))
  have hbound := break_measure_le_adaptive Extract S hfn Ggen hS Hask Hnk
    (OracleComp.queryBound_completing (derivQueries Extract) hQ) hqueries
  have h43 : n + 4 - 1 = n + 3 := by omega
  simpa [OracleComp.run_completing, h43] using hbound


/-- **Adaptive key-binding bound over adversary randomness and the outer oracles.** The
pointwise capstone conditions on the adversary's private randomness and the `H^ask`/`H^nk`
tables; this lifts it to the mixture. The index `ι` bundles everything the pointwise bound
fixes — private coins and both outer tables, under any joint distribution `p` — and the
bound is uniform in the slice, so averaging preserves it. -/
theorem break_measure_le_mixture {ι : Type*} (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι) (Hask : ι → SK → ASK) (Hnk : ι → SK → NK)
    {A : ι → OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
      (Witness G IVK AK NK RIVK QK SK × Witness G IVK AK NK RIVK QK SK)}
    {n : ℕ} (hQ : ∀ i, (A i).QueryBound n) :
    ((p.bind fun i => (PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK)).map
        (Prod.mk i))).toOuterMeasure
        {x : ι × (FinalQuery AK NK RIVK QK SK → RIVK) |
          Break Extract S hfn Ggen
            ⟨(Hask x.1), (Hnk x.1), fun sk => x.2 (.legacy sk), fun qk ak nk => x.2 (.ext qk ak nk),
              fun rivk_ext ak nk => x.2 (.int rivk_ext ak nk)⟩
            ((A x.1).run x.2).1 ((A x.1).run x.2).2}
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine toOuterMeasure_bind_le _ _ _ fun i => ?_
  rw [PMF.toOuterMeasure_map_apply]
  exact break_measure_le_of_queryBound Extract S hfn Ggen hS (Hask i) (Hnk i) (hQ i)


/-- **Adaptive key-binding bound over five independent oracle tables** — ZIP 2005's
probability space in full: the adversary's private randomness (any distribution `p`) and
the five oracle tables — `H^ask`, `H^nk`, and the three final `rivk`-derivation oracles —
drawn independently, the tables uniformly. The machine receives the sampled `H^ask`/`H^nk`
tables — dominating any query strategy against those oracles, with the query budget counting
only rivk-oracle queries — and runs on the combined table; the bound is the hypothesis-free
`(n+4)·(n+3)/|RIVK|`. -/
theorem break_measure_le_product {ι : Type*} [Fintype ASK] [Nonempty NK] [Nonempty ASK]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι)
    {A : ι → (SK → ASK) → (SK → NK) → OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
      (Witness G IVK AK NK RIVK QK SK × Witness G IVK AK NK RIVK QK SK)}
    {n : ℕ} (hQ : ∀ i Hask Hnk, (A i Hask Hnk).QueryBound n) :
    ((p.bind fun i => (PMF.uniformOfFintype (SK → ASK)).bind fun Hask =>
        (PMF.uniformOfFintype (SK → NK)).bind fun Hnk =>
          (PMF.uniformOfFintype (SK → RIVK)).bind fun Hleg =>
            (PMF.uniformOfFintype (QK → AK → NK → RIVK)).bind fun Hext =>
              (PMF.uniformOfFintype (RIVK → AK → NK → RIVK)).map fun Hint =>
                (i, Hask, Hnk, FinalQuery.eval Hleg Hext Hint))).toOuterMeasure
        (setOf fun (i, Hask, Hnk, O) =>
          Break Extract S hfn Ggen
            ⟨Hask, Hnk, fun sk => O (.legacy sk), fun qk ak nk => O (.ext qk ak nk),
              fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩
            ((A i Hask Hnk).run O).1 ((A i Hask Hnk).run O).2)
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine toOuterMeasure_bind_le _ _ _ fun i => ?_
  refine toOuterMeasure_bind_le _ _ _ fun Hask => ?_
  refine toOuterMeasure_bind_le _ _ _ fun Hnk => ?_
  have htr : ((PMF.uniformOfFintype (SK → RIVK)).bind fun Hleg =>
        (PMF.uniformOfFintype (QK → AK → NK → RIVK)).bind fun Hext =>
          (PMF.uniformOfFintype (RIVK → AK → NK → RIVK)).map fun Hint =>
            (i, Hask, Hnk, FinalQuery.eval Hleg Hext Hint))
      = (PMF.uniformOfFintype (FinalQuery AK NK RIVK QK SK → RIVK)).map fun O =>
          (i, Hask, Hnk, O) := by
    rw [← uniform_triple_eval]
    simp only [PMF.map_bind, PMF.map_comp]
    rfl
  rw [htr, PMF.toOuterMeasure_map_apply]
  exact break_measure_le_of_queryBound Extract S hfn Ggen hS Hask Hnk (hQ i Hask Hnk)

end Capstone

end Zcash.Security.KeyBinding
