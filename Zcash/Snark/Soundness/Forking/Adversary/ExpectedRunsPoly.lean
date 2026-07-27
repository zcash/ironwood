import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRuns

/-!
# AFK expected-run accounting

Node-level gated and low-rank accounting for the unconditional AFK expected-run bound.
-/

namespace Zcash.Snark

section GatedNode

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))

/-- At the incumbent challenge the reprogrammed candidate *is* the first branch: reprogramming the
table to its own value changes nothing and the trunk is trivially stable. -/
theorem scanCandidate_self [Fintype F] {d m : ℕ} (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC
        (O (prefixes (A.run O) ⟨m, by omega⟩))
      = recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          (m + 1) (by omega) O (A.run O)
          (childC (O (prefixes (A.run O) ⟨m, by omega⟩))) := by
  simp only [scanCandidate, Function.update_eq_self]
  rw [if_pos trivial]

/-- A *nonzero* incumbent challenge is good exactly when the first branch extracts. -/
theorem self_mem_goodChallenges_iff [Fintype F] {d m : ℕ} (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d)
    (h0 : O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0) :
    O (prefixes (A.run O) ⟨m, by omega⟩) ∈
        goodChallenges basis k A prefixes rounds final win decideWin m hmk O childC
      ↔ (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
          (by omega) O (A.run O)
          (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome := by
  rw [goodChallenges, Finset.mem_filter,
    scanCandidate_self basis k A prefixes rounds final win decideWin hmk O childC]
  simp [h0]

omit [Field F] in
/-- A candidate's low-rank test only counts *other* challenges sampled before it: its own
membership in the good set is invisible to its rank. -/
theorem scanRank_insert_erase {n : ℕ} (e : Fin n ≃ F) (M : Finset F) (u : F) :
    scanRank e (insert u M) u = scanRank e (insert u (M.erase u)) u := by
  unfold scanRank
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨ha, hlt⟩
    refine ⟨?_, hlt⟩
    rcases ha with rfl | ha
    · exact Or.inl rfl
    · by_cases hau : a = u
      · exact Or.inl hau
      · exact Or.inr ⟨hau, ha⟩
  · rintro ⟨ha, hlt⟩
    refine ⟨?_, hlt⟩
    rcases ha with rfl | ⟨_, ha⟩
    · exact Or.inl rfl
    · exact Or.inr ha

/-- Pointwise node accounting in which scan costs are paid only under the gate
`u₁ ≠ 0 ∧ first extracts` — the event whose probability the pairing argument prices. -/
theorem recursiveAlgebraicForkFrom_node_runs_le_gated [Fintype F] {d m : ℕ}
    (hmk : m + (d + 1) = k) (O : T → F) (p : P) (order : Fin (Fintype.card F) ≃ F)
    (childC : F → RecursiveForkCoins F d) :
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin m hmk O p
        (.node (List.ofFn (⇑order)) childC)).runs
      ≤ 1
        + (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
            (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).runs
        + (if O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0 ∧
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
              (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome
          then
            2 * ∑ u ∈ Finset.univ.filter (fun u : F =>
                scanRank order (insert u ((goodChallenges basis k A prefixes rounds final win
                  decideWin m hmk O childC).erase (O (prefixes (A.run O) ⟨m, by omega⟩)))) u < 2),
              (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u).runs
          else 0) := by
  by_cases hgate : O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0 ∧
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome
  · rw [if_pos hgate]
    exact recursiveAlgebraicForkFrom_node_runs_le basis k A prefixes rounds final win decideWin
      hmk O p order childC
  · rw [if_neg hgate]
    rw [not_and_or, not_ne_iff] at hgate
    simp only [recursiveAlgebraicForkFrom]
    split
    · simp
    · rename_i hu₁
      split
      · simp
      · rename_i c₁ hfirst
        rcases hgate with hz | hns
        · exact absurd hz hu₁
        · exact absurd (by rw [hfirst]; rfl) hns

/-- A scan candidate with an explicit reprogramming anchor, blind at that anchor. -/
def scanCandidateAt (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) (u : F) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := F) basis d) :=
  let O' := Function.update O t₀ u
  let p' := A.run O'
  if prefixes p' ⟨m, by omega⟩ = t₀ then
    recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O' p' (childC u)
  else { output := none, runs := 1 }

/-- Anchored at the run's actual fork prefix, the explicit-anchor candidate is the scan
candidate. -/
theorem scanCandidateAt_fork {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    scanCandidateAt basis k A prefixes rounds final win decideWin
        (prefixes (A.run O) ⟨m, by omega⟩) m hmk O childC
      = scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC :=
  rfl

/-- The explicit-anchor candidate is blind at its anchor. -/
theorem scanCandidateAt_update (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (x : F) (childC : F → RecursiveForkCoins F d) (u : F) :
    scanCandidateAt basis k A prefixes rounds final win decideWin t₀ m hmk
        (Function.update O t₀ x) childC u
      = scanCandidateAt basis k A prefixes rounds final win decideWin t₀ m hmk O childC u := by
  simp only [scanCandidateAt, Function.update_idem]

/-- The good set with the reprogramming anchor explicit: blind at the anchor and independent of
the anchor's table value. -/
noncomputable def goodChallengesAt (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k)
    [Fintype F] (O : T → F) (childC : F → RecursiveForkCoins F d) : Finset F :=
  Finset.univ.filter (fun u : F => u ≠ 0 ∧
    (scanCandidateAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O childC u).output.isSome)

theorem goodChallengesAt_fork [Fintype F] {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    goodChallengesAt basis k A prefixes rounds final win decideWin
        (prefixes (A.run O) ⟨m, by omega⟩) m hmk O childC
      = goodChallenges basis k A prefixes rounds final win decideWin m hmk O childC := by
  ext u
  simp [goodChallengesAt, goodChallenges,
    scanCandidateAt_fork basis k A prefixes rounds final win decideWin m hmk O childC]

theorem goodChallengesAt_update [Fintype F] (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k)
    (O : T → F) (x : F) (childC : F → RecursiveForkCoins F d) :
    goodChallengesAt basis k A prefixes rounds final win decideWin t₀ m hmk
        (Function.update O t₀ x) childC
      = goodChallengesAt basis k A prefixes rounds final win decideWin t₀ m hmk O childC := by
  simp only [goodChallengesAt,
    scanCandidateAt_update basis k A prefixes rounds final win decideWin t₀ m hmk O x childC]

end GatedNode

section RankDoubleCount

variable {F : Type*} [DecidableEq F]

/-- A candidate never precedes itself: its rank against an inserted set only counts the set. -/
theorem scanRank_insert_eq_filter {n : ℕ} (e : Fin n ≃ F) (S : Finset F) (u : F) :
    scanRank e (insert u S) u = (S.filter (fun a => e.symm a < e.symm u)).card := by
  unfold scanRank
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

/-- A fixed candidate is low-rank against the punctured good set at most four orders' worth of
times, summed over punctures and sampling orders. -/
theorem sum_card_scanRank_erase_lt_le [Fintype F] (G : Finset F) (u : F) :
    ∑ x ∈ G, (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
        scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) := by
  -- swap to per-order counting
  have hswap : ∑ x ∈ G, (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
      scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
      = ∑ order : Fin (Fintype.card F) ≃ F,
          (G.filter (fun x => scanRank order (insert u ((G.erase x).erase u)) u < 2)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  -- per-order: at most 2, plus the good set's size when u is low-rank against the full good set
  have hper : ∀ order : Fin (Fintype.card F) ≃ F,
      (G.filter (fun x => scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
        ≤ 2 + (if scanRank order (insert u (G.erase u)) u < 2 then G.card else 0) := by
    intro order
    have hrank : ∀ x, scanRank order (insert u ((G.erase x).erase u)) u
        = (((G.filter (fun a => order.symm a < order.symm u)).erase u).erase x).card := by
      intro x
      rw [scanRank_insert_eq_filter, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_right_comm]
    have hrank' : scanRank order (insert u (G.erase u)) u
        = ((G.filter (fun a => order.symm a < order.symm u)).erase u).card := by
      rw [scanRank_insert_eq_filter, Finset.filter_erase]
    by_cases hb : scanRank order (insert u (G.erase u)) u < 2
    · rw [if_pos hb]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.le_add_left _ _)
    · rw [if_neg hb, Nat.add_zero]
      rw [hrank', not_lt] at hb
      by_cases hb3 : 3 ≤ ((G.filter (fun a => order.symm a < order.symm u)).erase u).card
      · -- at least three preceding goods: no puncture rescues u
        have hempty : G.filter (fun x =>
            scanRank order (insert u ((G.erase x).erase u)) u < 2) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _
          rw [hrank x, not_lt]
          have := Finset.pred_card_le_card_erase
            (s := (G.filter (fun a => order.symm a < order.symm u)).erase u) (a := x)
          omega
        rw [hempty]
        simp
      · -- exactly two preceding goods: the puncture must be one of them
        have hsub : G.filter (fun x =>
            scanRank order (insert u ((G.erase x).erase u)) u < 2)
            ⊆ (G.filter (fun a => order.symm a < order.symm u)).erase u := by
          intro x hx
          rw [Finset.mem_filter] at hx
          by_contra hxB
          rw [hrank x, Finset.erase_eq_self.mpr hxB] at hx
          omega
        refine le_trans (Finset.card_le_card hsub) ?_
        omega
  refine le_trans (Finset.sum_le_sum fun order _ => hper order) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have htwo : ∑ order : Fin (Fintype.card F) ≃ F,
      (if scanRank order (insert u (G.erase u)) u < 2 then G.card else 0)
      ≤ 2 * Fintype.card (Fin (Fintype.card F) ≃ F) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul]
    have hmem : u ∈ insert u (G.erase u) := Finset.mem_insert_self u _
    have hcount := card_scanRank_lt_mul_le (n := Fintype.card F) (insert u (G.erase u)) hmem 2
    have hcard : G.card ≤ (insert u (G.erase u)).card := by
      rw [Finset.card_insert_of_notMem (Finset.notMem_erase u G)]
      have := Finset.pred_card_le_card_erase (s := G) (a := u)
      omega
    calc (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
            scanRank order (insert u (G.erase u)) u < 2)).card * G.card
        ≤ (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
            scanRank order (insert u (G.erase u)) u < 2)).card
            * (insert u (G.erase u)).card := Nat.mul_le_mul_left _ hcard
      _ = (insert u (G.erase u)).card
            * (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
              scanRank order (insert u (G.erase u)) u < 2)).card := Nat.mul_comm _ _
      _ ≤ 2 * Fintype.card (Fin (Fintype.card F) ≃ F) := hcount
  omega

namespace OracleComp

/-- Reprogramming a point that the original execution does not query cannot change its result. -/
theorem run_update_eq_of_not_mem_queries {T F α : Type*} [DecidableEq T]
    (A : OracleComp T F α) (O : T → F) (t : T) (u : F)
    (h : t ∉ A.queries O) : A.run (Function.update O t u) = A.run O := by
  induction A with
  | pure a => rfl
  | query q next ih =>
      simp only [queries, List.mem_cons, not_or] at h
      simp only [run]
      have hq : Function.update O t u q = O q := by
        rw [Function.update_apply, if_neg (Ne.symm h.1)]
      rw [hq]
      exact ih (O q) h.2

/-- If one-point reprogramming changes the result, the original execution queried that point. -/
theorem mem_queries_of_run_update_ne {T F α : Type*} [DecidableEq T]
    (A : OracleComp T F α) (O : T → F) (t : T) (u : F)
    (h : A.run (Function.update O t u) ≠ A.run O) : t ∈ A.queries O := by
  by_contra hn
  exact h (run_update_eq_of_not_mem_queries A O t u hn)

/-- At most the structural query budget's many distinct points occur in a completed run. -/
theorem card_filter_mem_queries_le {T F α : Type*} [Fintype T] [DecidableEq T]
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) (O : T → F) :
    (Finset.univ.filter (fun t : T ↦ t ∈ A.queries O)).card ≤ Q := by
  have hsub : Finset.univ.filter (fun t : T ↦ t ∈ A.queries O) ⊆ (A.queries O).toFinset := by
    intro t ht
    simpa using (Finset.mem_filter.mp ht).2
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (List.toFinset_card_le (A.queries O)) (A.queries_length_le hQ O))

end OracleComp

section SteeredBlind

/-- Fiber a coordinate-blind charge selected at an output-dependent table coordinate.  After
clearing `|F|`, the selected charge is the sum over every possible anchor and replacement value
whose reprogrammed table selects that anchor.  This is the finite-table form of AFK's array
reindexing step. -/
theorem sum_steered_blind_mul_card {T F : Type*} [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] (idx : (T → F) → T)
    (H : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F),
      H t (Function.update O t y) x = H t O x) :
    (∑ O : T → F, H (idx O) O (O (idx O))) * Fintype.card F
      = ∑ t : T, ∑ O : T → F, ∑ x : F,
          if idx (Function.update O t x) = t then H t O x else 0 := by
  let g : T → F → (T → F) → ℕ := fun t x O ↦
    if idx (Function.update O t x) = t then H t O x else 0
  have hgblind : ∀ (t : T) (x : F) (O : T → F) (y : F),
      g t x (Function.update O t y) = g t x O := by
    intro t x O y
    simp only [g, Function.update_idem, hblind]
  have hpartition :
      ∑ O : T → F, H (idx O) O (O (idx O))
        = ∑ t : T, ∑ O : T → F, if idx O = t then H t O (O t) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro O _
    simp
  rw [hpartition, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_table_fiberwise t (fun O ↦ if idx O = t then H t O (O t) else 0),
    Finset.sum_mul]
  calc
    ∑ x : F, (∑ O ∈ Finset.univ.filter (fun O : T → F ↦ O t = x),
        if idx O = t then H t O (O t) else 0) * Fintype.card F
      = ∑ x : F, (∑ O ∈ Finset.univ.filter (fun O : T → F ↦ O t = x),
          g t x O) * Fintype.card F := by
            apply Finset.sum_congr rfl
            intro x _
            congr 1
            apply Finset.sum_congr rfl
            intro O hO
            have hx : O t = x := (Finset.mem_filter.mp hO).2
            simp only [g]
            rw [← hx, Function.update_eq_self]
    _ = ∑ x : F, ∑ O : T → F, g t x O := by
          apply Finset.sum_congr rfl
          intro x _
          exact sum_table_fiber_mul_card t (g t x) (hgblind t x) x
    _ = ∑ O : T → F, ∑ x : F,
          if idx (Function.update O t x) = t then H t O x else 0 := by
            rw [Finset.sum_comm]

end SteeredBlind

section WeightedStableRank

/-- The expensive, trunk-stable part of a low-rank scan costs at most four recursive calls on
average over sampling orders.  Unlike a coarse query-charge bound, this does not multiply the
recursive cost by `Q`: reprogrammed tables whose selected index remains `t` are reindexed back to
ordinary tables before the low-rank double count is applied. -/
theorem sum_steered_rank_stable_le {T F : Type*} [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (idx : (T → F) → T) (good : T → (T → F) → Finset F)
    (hgoodBlind : ∀ (t : T) (O : T → F) (y : F),
      good t (Function.update O t y) = good t O)
    (hgoodStable : ∀ (t : T) (O : T → F) (x : F),
      x ∈ good t O → idx (Function.update O t x) = t)
    (Γ : (T → F) → ℕ) :
    (∑ O : T → F,
        let t := idx O
        let x := O t
        if x ∈ good t O then
          ∑ u : F,
            (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
              scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
              (if idx (Function.update O t u) = t then Γ (Function.update O t u) else 0)
        else 0)
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ O : T → F, Γ O := by
  let stableCost : T → (T → F) → F → ℕ := fun t O u ↦
    if idx (Function.update O t u) = t then Γ (Function.update O t u) else 0
  let H : T → (T → F) → F → ℕ := fun t O x ↦
    if x ∈ good t O then
      ∑ u : F,
        (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
          scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
          stableCost t O u
    else 0
  have hstableBlind : ∀ (t : T) (O : T → F) (u y : F),
      stableCost t (Function.update O t y) u = stableCost t O u := by
    intro t O u y
    simp only [stableCost, Function.update_idem]
  have hHblind : ∀ (t : T) (O : T → F) (x y : F),
      H t (Function.update O t y) x = H t O x := by
    intro t O x y
    simp only [H, hgoodBlind t O y, hstableBlind]
  have hsteer := sum_steered_blind_mul_card idx H hHblind
  have hpoint : ∀ (t : T) (O : T → F),
      (∑ x : F, if idx (Function.update O t x) = t then H t O x else 0)
        ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F, stableCost t O u := by
    intro t O
    simp only [H]
    calc
      (∑ x : F, if idx (Function.update O t x) = t then
          (if x ∈ good t O then
            ∑ u : F,
              (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
                stableCost t O u
           else 0)
        else 0)
        = ∑ x ∈ good t O, ∑ u : F,
            (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
              scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
              stableCost t O u := by
                calc
                  _ = ∑ x : F, if x ∈ good t O then
                      ∑ u : F,
                        (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                          scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
                          stableCost t O u
                      else 0 := by
                        apply Finset.sum_congr rfl
                        intro x _
                        by_cases hx : x ∈ good t O
                        · simp [hx, hgoodStable t O x hx]
                        · rw [if_neg hx]
                          split <;> rfl
                  _ = _ := by rw [← Finset.sum_filter, Finset.filter_univ_mem]
      _ = ∑ u : F, (∑ x ∈ good t O,
            (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
              scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card) *
              stableCost t O u := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro u _
                rw [Finset.sum_mul]
      _ ≤ ∑ u : F, (4 * Fintype.card (Fin (Fintype.card F) ≃ F)) *
            stableCost t O u := by
              apply Finset.sum_le_sum
              intro u _
              exact Nat.mul_le_mul_right (stableCost t O u)
                (sum_card_scanRank_erase_lt_le (good t O) u)
      _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
            ∑ u : F, stableCost t O u := by rw [Finset.mul_sum]
  have hstableSum :
      ∑ t : T, ∑ O : T → F, ∑ u : F, stableCost t O u
        = Fintype.card F * ∑ O : T → F, Γ O := by
    have hper : ∀ t : T,
        ∑ O : T → F, ∑ u : F, stableCost t O u
          = Fintype.card F * ∑ O : T → F, if idx O = t then Γ O else 0 := by
      intro t
      rw [Finset.sum_comm]
      calc
        ∑ u : F, ∑ O : T → F, stableCost t O u
          = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F ↦ O t = u),
              if idx O = t then Γ O else 0) * Fintype.card F := by
                apply Finset.sum_congr rfl
                intro u _
                let f : (T → F) → ℕ := fun O ↦ stableCost t O u
                have hfblind : ∀ (O : T → F) (y : F),
                    f (Function.update O t y) = f O := by
                  intro O y
                  exact hstableBlind t O u y
                rw [← sum_table_fiber_mul_card t f hfblind u]
                congr 1
                apply Finset.sum_congr rfl
                intro O hO
                have hu : O t = u := (Finset.mem_filter.mp hO).2
                simp only [f, stableCost]
                rw [← hu, Function.update_eq_self]
        _ = Fintype.card F * ∑ O : T → F, if idx O = t then Γ O else 0 := by
              rw [← Finset.sum_mul, ← sum_table_fiberwise t]
              ring
    rw [Finset.sum_congr rfl (fun t _ ↦ hper t), ← Finset.mul_sum, Finset.sum_comm]
    apply congrArg (fun n : ℕ ↦ Fintype.card F * n)
    apply Finset.sum_congr rfl
    intro O _
    simp
  refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
  rw [hsteer]
  calc
    (∑ t : T, ∑ O : T → F, ∑ x : F,
        if idx (Function.update O t x) = t then H t O x else 0)
      ≤ ∑ t : T, ∑ O : T → F,
          4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
            ∑ u : F, stableCost t O u := by
              apply Finset.sum_le_sum
              intro t _
              apply Finset.sum_le_sum
              intro O _
              exact hpoint t O
    _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
          (∑ t : T, ∑ O : T → F, ∑ u : F, stableCost t O u) := by
            simp only [Finset.mul_sum]
    _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
          (Fintype.card F * ∑ O : T → F, Γ O) := by rw [hstableSum]
    _ = (4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
          ∑ O : T → F, Γ O) * Fintype.card F := by ring

end WeightedStableRank

section WeightedAbortRank

/-- The cheap, changed-trunk part of a low-rank scan is charged only to queried coordinates.
Each such candidate costs one adversary call; after table reindexing, the number of possible
anchors is bounded by `Q`. -/
theorem sum_steered_rank_abort_le {T F α : Type*} [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (A : OracleComp T F α) {Q : ℕ} (hQ : A.QueryBound Q)
    (idx : (T → F) → T) (good : T → (T → F) → Finset F)
    (hgoodBlind : ∀ (t : T) (O : T → F) (y : F),
      good t (Function.update O t y) = good t O)
    (hgoodStable : ∀ (t : T) (O : T → F) (x : F),
      x ∈ good t O → idx (Function.update O t x) = t)
    (hchangedQuery : ∀ (t : T) (O : T → F),
      (good t O).Nonempty → idx O ≠ t → t ∈ A.queries O) :
    (∑ O : T → F,
        let t := idx O
        let x := O t
        if x ∈ good t O then
          ∑ u : F,
            (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
              scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
              (if idx (Function.update O t u) = t then 0 else 1)
        else 0)
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) * Q * Fintype.card (T → F) := by
  let abortCost : T → (T → F) → F → ℕ := fun t O u ↦
    if idx (Function.update O t u) = t then 0 else 1
  let H : T → (T → F) → F → ℕ := fun t O x ↦
    if x ∈ good t O then
      ∑ u : F,
        (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
          scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
          abortCost t O u
    else 0
  have habortBlind : ∀ (t : T) (O : T → F) (u y : F),
      abortCost t (Function.update O t y) u = abortCost t O u := by
    intro t O u y
    simp only [abortCost, Function.update_idem]
  have hHblind : ∀ (t : T) (O : T → F) (x y : F),
      H t (Function.update O t y) x = H t O x := by
    intro t O x y
    simp only [H, hgoodBlind t O y, habortBlind]
  have hsteer := sum_steered_blind_mul_card idx H hHblind
  have hpoint : ∀ (t : T) (O : T → F),
      (∑ x : F, if idx (Function.update O t x) = t then H t O x else 0)
        ≤ if (good t O).Nonempty then
            4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F, abortCost t O u
          else 0 := by
    intro t O
    by_cases hne : (good t O).Nonempty
    · rw [if_pos hne]
      simp only [H]
      calc
        (∑ x : F, if idx (Function.update O t x) = t then
            (if x ∈ good t O then
              ∑ u : F,
                (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                  scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
                  abortCost t O u
             else 0)
          else 0)
          = ∑ x ∈ good t O, ∑ u : F,
              (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
                abortCost t O u := by
                  calc
                    _ = ∑ x : F, if x ∈ good t O then
                        ∑ u : F,
                          (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                            scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card *
                            abortCost t O u
                        else 0 := by
                          apply Finset.sum_congr rfl
                          intro x _
                          by_cases hx : x ∈ good t O
                          · simp [hx, hgoodStable t O x hx]
                          · rw [if_neg hx]
                            split <;> rfl
                    _ = _ := by rw [← Finset.sum_filter, Finset.filter_univ_mem]
        _ = ∑ u : F, (∑ x ∈ good t O,
              (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                scanRank order (insert u (((good t O).erase x).erase u)) u < 2)).card) *
                abortCost t O u := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro u _
                  rw [Finset.sum_mul]
        _ ≤ ∑ u : F, (4 * Fintype.card (Fin (Fintype.card F) ≃ F)) *
              abortCost t O u := by
                apply Finset.sum_le_sum
                intro u _
                exact Nat.mul_le_mul_right (abortCost t O u)
                  (sum_card_scanRank_erase_lt_le (good t O) u)
        _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
              ∑ u : F, abortCost t O u := by rw [Finset.mul_sum]
    · have hempty : good t O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [if_neg hne]
      simp [H, hempty]
  have habortSum :
      ∑ t : T, ∑ O : T → F,
          (if (good t O).Nonempty then ∑ u : F, abortCost t O u else 0)
        ≤ Fintype.card F * (Q * Fintype.card (T → F)) := by
    have hper : ∀ t : T,
        ∑ O : T → F, (if (good t O).Nonempty then ∑ u : F, abortCost t O u else 0)
          = Fintype.card F * ∑ O : T → F,
              if (good t O).Nonempty ∧ idx O ≠ t then 1 else 0 := by
      intro t
      calc
        ∑ O : T → F, (if (good t O).Nonempty then ∑ u : F, abortCost t O u else 0)
          = ∑ O : T → F, ∑ u : F,
              (if (good t O).Nonempty then abortCost t O u else 0) := by
                apply Finset.sum_congr rfl
                intro O _
                by_cases hg : (good t O).Nonempty <;> simp [hg]
        _ = ∑ u : F, ∑ O : T → F,
              (if (good t O).Nonempty then abortCost t O u else 0) := Finset.sum_comm
        _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F ↦ O t = u),
              if (good t O).Nonempty ∧ idx O ≠ t then 1 else 0) * Fintype.card F := by
                apply Finset.sum_congr rfl
                intro u _
                let f : (T → F) → ℕ := fun O ↦
                  if (good t O).Nonempty then abortCost t O u else 0
                have hfblind : ∀ (O : T → F) (y : F),
                    f (Function.update O t y) = f O := by
                  intro O y
                  simp only [f, hgoodBlind t O y, habortBlind]
                rw [← sum_table_fiber_mul_card t f hfblind u]
                congr 1
                apply Finset.sum_congr rfl
                intro O hO
                have hu : O t = u := (Finset.mem_filter.mp hO).2
                simp only [f, abortCost]
                rw [← hu, Function.update_eq_self]
                by_cases hg : (good t O).Nonempty <;> by_cases hi : idx O = t <;>
                  simp [hg, hi]
        _ = Fintype.card F * ∑ O : T → F,
              if (good t O).Nonempty ∧ idx O ≠ t then 1 else 0 := by
                rw [← Finset.sum_mul, ← sum_table_fiberwise t]
                ring
    rw [Finset.sum_congr rfl (fun t _ ↦ hper t), ← Finset.mul_sum, Finset.sum_comm]
    apply Nat.mul_le_mul_left
    calc
      (∑ O : T → F, ∑ t : T,
          if (good t O).Nonempty ∧ idx O ≠ t then 1 else 0)
        ≤ ∑ O : T → F, Q := by
              apply Finset.sum_le_sum
              intro O _
              calc
                (∑ t : T, if (good t O).Nonempty ∧ idx O ≠ t then 1 else 0)
                  = (Finset.univ.filter (fun t : T ↦
                      (good t O).Nonempty ∧ idx O ≠ t)).card := by
                        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
                _ ≤ (Finset.univ.filter (fun t : T ↦ t ∈ A.queries O)).card := by
                      apply Finset.card_le_card
                      intro t ht
                      rw [Finset.mem_filter] at ht ⊢
                      exact ⟨Finset.mem_univ _, hchangedQuery t O ht.2.1 ht.2.2⟩
                _ ≤ Q := OracleComp.card_filter_mem_queries_le hQ O
      _ = Q * Fintype.card (T → F) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
  refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
  rw [hsteer]
  calc
    (∑ t : T, ∑ O : T → F, ∑ x : F,
        if idx (Function.update O t x) = t then H t O x else 0)
      ≤ ∑ t : T, ∑ O : T → F,
          (if (good t O).Nonempty then
            4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F, abortCost t O u
           else 0) := by
              apply Finset.sum_le_sum
              intro t _
              apply Finset.sum_le_sum
              intro O _
              exact hpoint t O
    _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
          ∑ t : T, ∑ O : T → F,
            (if (good t O).Nonempty then ∑ u : F, abortCost t O u else 0) := by
              simp only [Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
          (Fintype.card F * (Q * Fintype.card (T → F))) :=
            Nat.mul_le_mul_left _ habortSum
    _ = (4 * Fintype.card (Fin (Fintype.card F) ≃ F) * Q *
          Fintype.card (T → F)) * Fintype.card F := by ring

end WeightedAbortRank

section WeightedScanCharge

variable {T F G P ι : Type*} [Fintype T] [DecidableEq T] [Field F] [Fintype F]
  [DecidableEq F] [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))

omit [Fintype T] [Fintype F] in
/-- A scan candidate is either a stable recursive call or a unit-cost changed-trunk abort. -/
theorem scanCandidateAt_runs_split (t₀ : T) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) (childC : F → RecursiveForkCoins F d) (u : F) :
    (scanCandidateAt basis k A prefixes rounds final win decideWin
        t₀ m hmk O childC u).runs
      = (if prefixes (A.run (Function.update O t₀ u)) ⟨m, by omega⟩ = t₀ then
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) (by omega) (Function.update O t₀ u)
            (A.run (Function.update O t₀ u)) (childC u)).runs
        else 0)
        + (if prefixes (A.run (Function.update O t₀ u)) ⟨m, by omega⟩ = t₀ then 0 else 1) := by
  simp only [scanCandidateAt]
  split <;> simp

omit [Fintype T] in
/-- Membership in the explicit-anchor good set certifies that reprogramming selects that
anchor. -/
theorem goodChallengesAt_stable (t₀ : T) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) (childC : F → RecursiveForkCoins F d) {x : F}
    (hx : x ∈ goodChallengesAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O childC) :
    prefixes (A.run (Function.update O t₀ x)) ⟨m, by omega⟩ = t₀ := by
  rw [goodChallengesAt, Finset.mem_filter] at hx
  simp only [scanCandidateAt] at hx
  split at hx
  · assumption
  · simp at hx

omit [Fintype T] in
/-- If an anchor has a good replacement but is not the current output prefix, then changing that
coordinate changes the adversary output, so the original execution queried it. -/
theorem goodChallengesAt_nonempty_changed_query (t₀ : T) {d m : ℕ}
    (hmk : m + (d + 1) = k) (O : T → F) (childC : F → RecursiveForkCoins F d)
    (hne : (goodChallengesAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O childC).Nonempty)
    (hidx : prefixes (A.run O) ⟨m, by omega⟩ ≠ t₀) : t₀ ∈ A.queries O := by
  obtain ⟨x, hx⟩ := hne
  have hstable := goodChallengesAt_stable basis k A prefixes rounds final win decideWin
    t₀ hmk O childC hx
  apply OracleComp.mem_queries_of_run_update_ne A O t₀ x
  intro heq
  apply hidx
  calc
    prefixes (A.run O) ⟨m, by omega⟩
        = prefixes (A.run (Function.update O t₀ x)) ⟨m, by omega⟩ := by rw [heq]
    _ = t₀ := hstable

/-- The scan cost charged to a proposed incumbent challenge `x`, after averaging over all child
tapes but before averaging over sampling orders.  The explicit anchor makes this charge blind to
the oracle value at that anchor, which is the condition needed by the weighted-query lemmas.

The punctures by `x` and `u` match `sum_card_scanRank_erase_lt_le`: `x` is the incumbent branch
and `u` is the candidate whose rank is being tested. -/
noncomputable def afkScanCharge (t₀ : T) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) (x : F) : ℕ :=
  ∑ childT : F → RecursiveForkTape F d,
    let childC := fun u ↦ (childT u).toCoins
    let good := goodChallengesAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O childC
    if x ∈ good then
      ∑ u : F,
        (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
          scanRank order (insert u ((good.erase x).erase u)) u < 2)).card *
          (scanCandidateAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O childC u).runs
    else 0

omit [Fintype T] in
/-- `afkScanCharge` is coordinate-blind at its explicit reprogramming anchor. -/
theorem afkScanCharge_update (t₀ : T) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) (x y : F) :
    afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk
        (Function.update O t₀ y) x
      = afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk O x := by
  unfold afkScanCharge
  apply Finset.sum_congr rfl
  intro childT _
  simp only
  rw [goodChallengesAt_update basis k A prefixes rounds final win decideWin
    t₀ m hmk O y (fun u ↦ (childT u).toCoins)]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [scanCandidateAt_update basis k A prefixes rounds final win decideWin
    t₀ m hmk O y (fun w ↦ (childT w).toCoins) u]

omit [Fintype T] in
/-- The total incumbent charge is bounded by four order-spaces' worth of candidate costs.  This
is the weighted double-counting step: it removes all dependence on the size of the good set and
is the local combinatorial heart of the unconditional AFK bound. -/
theorem sum_afkScanCharge_le (t₀ : T) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) :
    ∑ x : F, afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk O x
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
        ∑ childT : F → RecursiveForkTape F d, ∑ u : F,
          (scanCandidateAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O (fun w ↦ (childT w).toCoins) u).runs := by
  unfold afkScanCharge
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ childT : F → RecursiveForkTape F d,
          4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F,
            (scanCandidateAt basis k A prefixes rounds final win decideWin
              t₀ m hmk O (fun w ↦ (childT w).toCoins) u).runs := by
        apply Finset.sum_le_sum
        intro childT _
        let childC := fun u ↦ (childT u).toCoins
        let good := goodChallengesAt basis k A prefixes rounds final win decideWin
          t₀ m hmk O childC
        let cost := fun u ↦
          (scanCandidateAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O childC u).runs
        change (∑ x : F, if x ∈ good then
            ∑ u : F,
              (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                scanRank order (insert u ((good.erase x).erase u)) u < 2)).card * cost u
            else 0)
          ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F, cost u
        rw [← Finset.sum_filter, Finset.filter_univ_mem]
        calc
          _ = ∑ u : F, (∑ x ∈ good,
                (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                  scanRank order (insert u ((good.erase x).erase u)) u < 2)).card) * cost u := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro u _
                rw [Finset.sum_mul]
          _ ≤ ∑ u : F,
              (4 * Fintype.card (Fin (Fintype.card F) ≃ F)) * cost u := by
                apply Finset.sum_le_sum
                intro u _
                exact Nat.mul_le_mul_right (cost u) (sum_card_scanRank_erase_lt_le good u)
          _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) * ∑ u : F, cost u := by
                rw [Finset.mul_sum]
    _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
        ∑ childT : F → RecursiveForkTape F d, ∑ u : F,
          (scanCandidateAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O (fun w ↦ (childT w).toCoins) u).runs := by
      rw [Finset.mul_sum]

/-- The full output-steered scan charge has the AFK weighted form: a constant-times recursive
cost plus a constant-times `Q` unit-abort cost.  In particular, `Q` does not multiply the
recursive term. -/
theorem sum_afkScanCharge_steered_le {Q : ℕ} (hQ : A.QueryBound Q)
    {d m : ℕ} (hmk : m + (d + 1) = k) :
    (∑ O : T → F,
        let t₀ := prefixes (A.run O) ⟨m, by omega⟩
        afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk O (O t₀))
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
        (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
            ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) (by omega) O (A.run O) tape.toCoins).runs
          + Q * Fintype.card (T → F) *
              Fintype.card (RecursiveForkTape F d) ^ Fintype.card F) := by
  let idx : (T → F) → T := fun O ↦ prefixes (A.run O) ⟨m, by omega⟩
  let CP := Fintype.card (Fin (Fintype.card F) ≃ F)
  let CT := Fintype.card (RecursiveForkTape F d)
  have hper : ∀ childT : F → RecursiveForkTape F d,
      (∑ O : T → F,
          let t₀ := idx O
          let x := O t₀
          let childC := fun u ↦ (childT u).toCoins
          let good := goodChallengesAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O childC
          if x ∈ good then
            ∑ u : F,
              (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                scanRank order (insert u ((good.erase x).erase u)) u < 2)).card *
                (scanCandidateAt basis k A prefixes rounds final win decideWin
                  t₀ m hmk O childC u).runs
          else 0)
        ≤ 4 * CP *
            (∑ O : T → F,
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) (by omega) O (A.run O) (childT (O (idx O))).toCoins).runs)
          + 4 * CP * Q * Fintype.card (T → F) := by
    intro childT
    let childC := fun u ↦ (childT u).toCoins
    let good : T → (T → F) → Finset F := fun t₀ O ↦
      goodChallengesAt basis k A prefixes rounds final win decideWin t₀ m hmk O childC
    let Γ : (T → F) → ℕ := fun O ↦
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        (m + 1) (by omega) O (A.run O) (childT (O (idx O))).toCoins).runs
    have hgoodBlind : ∀ (t₀ : T) (O : T → F) (y : F),
        good t₀ (Function.update O t₀ y) = good t₀ O := by
      intro t₀ O y
      exact goodChallengesAt_update basis k A prefixes rounds final win decideWin
        t₀ m hmk O y childC
    have hgoodStable : ∀ (t₀ : T) (O : T → F) (x : F),
        x ∈ good t₀ O → idx (Function.update O t₀ x) = t₀ := by
      intro t₀ O x hx
      exact goodChallengesAt_stable basis k A prefixes rounds final win decideWin
        t₀ hmk O childC hx
    have hchangedQuery : ∀ (t₀ : T) (O : T → F),
        (good t₀ O).Nonempty → idx O ≠ t₀ → t₀ ∈ A.queries O := by
      intro t₀ O hne hidx
      exact goodChallengesAt_nonempty_changed_query basis k A prefixes rounds final win decideWin
        t₀ hmk O childC hne hidx
    have hstable := sum_steered_rank_stable_le idx good hgoodBlind hgoodStable Γ
    have habort := sum_steered_rank_abort_le A hQ idx good hgoodBlind hgoodStable hchangedQuery
    let stableCost : T → (T → F) → F → ℕ := fun t₀ O u ↦
      if idx (Function.update O t₀ u) = t₀ then Γ (Function.update O t₀ u) else 0
    let abortCost : T → (T → F) → F → ℕ := fun t₀ O u ↦
      if idx (Function.update O t₀ u) = t₀ then 0 else 1
    have hcost : ∀ (t₀ : T) (O : T → F) (u : F),
        (scanCandidateAt basis k A prefixes rounds final win decideWin
            t₀ m hmk O childC u).runs
          = stableCost t₀ O u + abortCost t₀ O u := by
      intro t₀ O u
      rw [scanCandidateAt_runs_split basis k A prefixes rounds final win decideWin
        t₀ hmk O childC u]
      by_cases hs : prefixes (A.run (Function.update O t₀ u)) ⟨m, by omega⟩ = t₀
      · simp only [stableCost, abortCost, Γ, idx, if_pos hs, add_zero]
        rw [hs, Function.update_self]
      · simp [stableCost, abortCost, Γ, idx, hs]
    have hsplit :
        (∑ O : T → F,
            let t₀ := idx O
            let x := O t₀
            if x ∈ good t₀ O then
              ∑ u : F,
                (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                  scanRank order (insert u (((good t₀ O).erase x).erase u)) u < 2)).card *
                  (scanCandidateAt basis k A prefixes rounds final win decideWin
                    t₀ m hmk O childC u).runs
            else 0)
          = (∑ O : T → F,
              let t₀ := idx O
              let x := O t₀
              if x ∈ good t₀ O then
                ∑ u : F,
                  (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                    scanRank order (insert u (((good t₀ O).erase x).erase u)) u < 2)).card *
                    stableCost t₀ O u
              else 0)
            + (∑ O : T → F,
              let t₀ := idx O
              let x := O t₀
              if x ∈ good t₀ O then
                ∑ u : F,
                  (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F ↦
                    scanRank order (insert u (((good t₀ O).erase x).erase u)) u < 2)).card *
                    abortCost t₀ O u
              else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro O _
      dsimp only
      split
      · rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rw [hcost]
        ring
      · simp
    rw [hsplit]
    exact Nat.add_le_add hstable habort
  unfold afkScanCharge
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ childT : F → RecursiveForkTape F d,
          (4 * CP *
              (∑ O : T → F,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) (childT (O (idx O))).toCoins).runs)
            + 4 * CP * Q * Fintype.card (T → F)) := by
              apply Finset.sum_le_sum
              intro childT _
              simpa [idx] using hper childT
    _ = 4 * CP *
          (CT ^ (Fintype.card F - 1) *
              ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) tape.toCoins).runs
            + Q * Fintype.card (T → F) * CT ^ Fintype.card F) := by
      rw [Finset.sum_add_distrib]
      have hrecursive :
          ∑ childT : F → RecursiveForkTape F d,
              4 * CP * ∑ O : T → F,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) (childT (O (idx O))).toCoins).runs
            = 4 * CP * (CT ^ (Fintype.card F - 1) *
                ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
                  (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                    (m + 1) (by omega) O (A.run O) tape.toCoins).runs) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        calc
          ∑ O : T → F, ∑ childT : F → RecursiveForkTape F d,
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) (by omega) O (A.run O) (childT (O (idx O))).toCoins).runs
            = ∑ O : T → F, CT ^ (Fintype.card F - 1) *
                ∑ tape : RecursiveForkTape F d,
                  (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                    (m + 1) (by omega) O (A.run O) tape.toCoins).runs := by
                      apply Finset.sum_congr rfl
                      intro O _
                      exact sum_eval_pi (O (idx O)) (fun tape : RecursiveForkTape F d ↦
                        (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                          (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
          _ = CT ^ (Fintype.card F - 1) *
                ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
                  (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                    (m + 1) (by omega) O (A.run O) tape.toCoins).runs := by
                      rw [Finset.mul_sum]
      rw [hrecursive, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Fintype.card_fun]
      ring
    _ = 4 * Fintype.card (Fin (Fintype.card F) ≃ F) *
        (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
            ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) (by omega) O (A.run O) tape.toCoins).runs
          + Q * Fintype.card (T → F) *
              Fintype.card (RecursiveForkTape F d) ^ Fintype.card F) := by
                rfl

end WeightedScanCharge

section PolynomialRunBound

variable {T F G P ι : Type*} [Fintype T] [DecidableEq T] [Field F] [Fintype F]
  [DecidableEq F] [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))

/-- After summing a node over sampling orders and child tapes, its scan term is exactly the
explicit AFK charge.  This is the bridge between the pointwise gated accounting and the
output-steered oracle-table argument. -/
theorem recursiveAlgebraicForkFrom_tape_sum_runs_le_afk {d m : ℕ}
    (hmk : m + (d + 1) = k) (O : T → F) :
    ∑ tape : RecursiveForkTape F (d + 1),
        (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          m hmk O (A.run O) tape.toCoins).runs
      ≤ Fintype.card (Fin (Fintype.card F) ≃ F) *
            Fintype.card (RecursiveForkTape F d) ^ Fintype.card F
        + Fintype.card (Fin (Fintype.card F) ≃ F) *
            (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
              ∑ tape : RecursiveForkTape F d,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
        + 2 * afkScanCharge basis k A prefixes rounds final win decideWin
            (prefixes (A.run O) ⟨m, by omega⟩) hmk O
            (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
  let N := Fintype.card F
  let CP := Fintype.card (Fin N ≃ F)
  let CT := Fintype.card (RecursiveForkTape F d)
  let t₀ := prefixes (A.run O) ⟨m, by omega⟩
  let x := O t₀
  let childRuns : RecursiveForkTape F d → ℕ := fun tape ↦
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O (A.run O) tape.toCoins).runs
  let good : (F → RecursiveForkTape F d) → Finset F := fun childT ↦
    goodChallengesAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O (fun u ↦ (childT u).toCoins)
  let candidateRuns : F → (F → RecursiveForkTape F d) → ℕ := fun u childT ↦
    (scanCandidateAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O (fun w ↦ (childT w).toCoins) u).runs
  have htrans : ∑ tape : RecursiveForkTape F (d + 1),
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O (A.run O) tape.toCoins).runs
      = ∑ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            m hmk O (A.run O) (RecursiveForkTape.node pr.1 pr.2).toCoins).runs := by
    rw [← Equiv.sum_comp (RecursiveForkTape.equivSucc (F := F) d).symm
      (fun tape ↦ (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O (A.run O) tape.toCoins).runs)]
    apply Finset.sum_congr rfl
    intro pr _
    rfl
  have hpoint : ∀ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O (A.run O) (RecursiveForkTape.node pr.1 pr.2).toCoins).runs
      ≤ 1 + childRuns (pr.2 x)
        + (if x ∈ good pr.2 then
            2 * ∑ u ∈ Finset.univ.filter (fun u : F ↦
              scanRank pr.1 (insert u (((good pr.2).erase x).erase u)) u < 2),
                candidateRuns u pr.2
          else 0) := by
    intro pr
    have hbase := recursiveAlgebraicForkFrom_node_runs_le_gated basis k A prefixes rounds final
      win decideWin hmk O (A.run O) pr.1 (fun w ↦ (pr.2 w).toCoins)
    have hgood : good pr.2 = goodChallenges basis k A prefixes rounds final win decideWin
        m hmk O (fun w ↦ (pr.2 w).toCoins) := by
      exact goodChallengesAt_fork basis k A prefixes rounds final win decideWin
        m hmk O (fun w ↦ (pr.2 w).toCoins)
    have hgate : (x ≠ 0 ∧
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) (by omega) O (A.run O) (pr.2 x).toCoins).output.isSome)
        ↔ x ∈ good pr.2 := by
      rw [hgood, goodChallenges, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      rw [scanCandidate_self basis k A prefixes rounds final win decideWin
        hmk O (fun w ↦ (pr.2 w).toCoins)]
    by_cases hx : x ∈ good pr.2
    · rw [if_pos hx]
      rw [if_pos (hgate.mpr hx)] at hbase
      simpa only [childRuns, candidateRuns, t₀, x, hgood,
        scanCandidateAt_fork,
        scanRank_insert_erase pr.1
          ((goodChallenges basis k A prefixes rounds final win decideWin
            m hmk O (fun w ↦ (pr.2 w).toCoins)).erase
              (O (prefixes (A.run O) ⟨m, by omega⟩)))] using hbase
    · rw [if_neg hx]
      rw [if_neg (mt hgate.mp hx)] at hbase
      simpa only [childRuns, t₀, x] using hbase
  rw [htrans]
  calc
    _ ≤ ∑ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
          (1 + childRuns (pr.2 x)
            + (if x ∈ good pr.2 then
                2 * ∑ u ∈ Finset.univ.filter (fun u : F ↦
                  scanRank pr.1 (insert u (((good pr.2).erase x).erase u)) u < 2),
                    candidateRuns u pr.2
              else 0)) := Finset.sum_le_sum (fun pr _ ↦ hpoint pr)
    _ = CP * CT ^ N
        + CP * (CT ^ (N - 1) * ∑ tape : RecursiveForkTape F d, childRuns tape)
        + 2 * afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk O x := by
      calc
        ∑ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
            (1 + childRuns (pr.2 x)
              + (if x ∈ good pr.2 then
                  2 * ∑ u ∈ Finset.univ.filter (fun u : F ↦
                    scanRank pr.1 (insert u (((good pr.2).erase x).erase u)) u < 2),
                      candidateRuns u pr.2
                else 0))
            = (∑ _pr : (Fin N ≃ F) × (F → RecursiveForkTape F d), 1)
              + (∑ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
                  childRuns (pr.2 x))
              + (∑ pr : (Fin N ≃ F) × (F → RecursiveForkTape F d),
                  if x ∈ good pr.2 then
                    2 * ∑ u ∈ Finset.univ.filter (fun u : F ↦
                      scanRank pr.1 (insert u (((good pr.2).erase x).erase u)) u < 2),
                        candidateRuns u pr.2
                  else 0) := by
                    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        _ = CP * CT ^ N
            + CP * (CT ^ (N - 1) * ∑ tape : RecursiveForkTape F d, childRuns tape)
            + 2 * afkScanCharge basis k A prefixes rounds final win decideWin t₀ hmk O x := by
          congr 1
          · congr 1
            · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
                Fintype.card_prod, Fintype.card_fun]
            · rw [Fintype.sum_prod_type]
              calc
                ∑ _order : Fin N ≃ F, ∑ childT : F → RecursiveForkTape F d,
                    childRuns (childT x)
                    = ∑ _order : Fin N ≃ F,
                        CT ^ (N - 1) * ∑ tape : RecursiveForkTape F d, childRuns tape := by
                          apply Finset.sum_congr rfl
                          intro order _
                          exact sum_eval_pi x childRuns
                _ = CP * (CT ^ (N - 1) *
                      ∑ tape : RecursiveForkTape F d, childRuns tape) := by
                        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          · rw [Fintype.sum_prod_type_right]
            unfold afkScanCharge
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro childT _
            change (∑ order : Fin N ≃ F,
                if x ∈ good childT then
                  2 * ∑ u ∈ Finset.univ.filter (fun u : F ↦
                    scanRank order (insert u (((good childT).erase x).erase u)) u < 2),
                      candidateRuns u childT
                else 0)
              = 2 * (if x ∈ good childT then
                  ∑ u : F,
                    (Finset.univ.filter (fun order : Fin N ≃ F ↦
                      scanRank order (insert u (((good childT).erase x).erase u)) u < 2)).card *
                        candidateRuns u childT
                else 0)
            by_cases hx : x ∈ good childT
            · simp only [if_pos hx, ← Finset.mul_sum]
              congr 1
              calc
                ∑ order : Fin N ≃ F, ∑ u ∈ Finset.univ.filter (fun u : F ↦
                    scanRank order (insert u (((good childT).erase x).erase u)) u < 2),
                      candidateRuns u childT
                    = ∑ order : Fin N ≃ F, ∑ u : F,
                        (if scanRank order (insert u (((good childT).erase x).erase u)) u < 2
                          then candidateRuns u childT else 0) := by
                            apply Finset.sum_congr rfl
                            intro order _
                            rw [Finset.sum_filter]
                _ = ∑ u : F, ∑ order : Fin N ≃ F,
                      (if scanRank order (insert u (((good childT).erase x).erase u)) u < 2
                        then candidateRuns u childT else 0) := Finset.sum_comm
                _ = ∑ u : F,
                      (Finset.univ.filter (fun order : Fin N ≃ F ↦
                        scanRank order (insert u (((good childT).erase x).erase u)) u < 2)).card *
                          candidateRuns u childT := by
                            apply Finset.sum_congr rfl
                            intro u _
                            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
            · simp [hx]
    _ = Fintype.card (Fin (Fintype.card F) ≃ F) *
          Fintype.card (RecursiveForkTape F d) ^ Fintype.card F
        + Fintype.card (Fin (Fintype.card F) ≃ F) *
            (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
              ∑ tape : RecursiveForkTape F d,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
        + 2 * afkScanCharge basis k A prefixes rounds final win decideWin
            (prefixes (A.run O) ⟨m, by omega⟩) hmk O
            (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
              rfl

/-- One unconditional AFK recurrence step.  Stable recursive branches contribute the factor
`9`; changed-trunk aborts contribute only the additive query-bounded term `8·Q+1`. -/
theorem recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_step {Q d m : ℕ}
    (hQ : A.QueryBound Q) (hmk : m + (d + 1) = k) :
    (∑ O : T → F, ∑ tape : RecursiveForkTape F (d + 1),
        (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          m hmk O (A.run O) tape.toCoins).runs)
      ≤ 9 * Fintype.card (Fin (Fintype.card F) ≃ F) *
            (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
              ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
        + (8 * Q + 1) * Fintype.card (T → F) *
            Fintype.card (Fin (Fintype.card F) ≃ F) *
            Fintype.card (RecursiveForkTape F d) ^ Fintype.card F := by
  let CP := Fintype.card (Fin (Fintype.card F) ≃ F)
  let CT := Fintype.card (RecursiveForkTape F d)
  let CO := Fintype.card (T → F)
  let childSum := ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O (A.run O) tape.toCoins).runs
  have hnode : (∑ O : T → F, ∑ tape : RecursiveForkTape F (d + 1),
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O (A.run O) tape.toCoins).runs)
      ≤ ∑ O : T → F,
          (CP * CT ^ Fintype.card F
            + CP * (CT ^ (Fintype.card F - 1) *
                ∑ tape : RecursiveForkTape F d,
                  (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                    (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
            + 2 * afkScanCharge basis k A prefixes rounds final win decideWin
                (prefixes (A.run O) ⟨m, by omega⟩) hmk O
                (O (prefixes (A.run O) ⟨m, by omega⟩))) := by
    apply Finset.sum_le_sum
    intro O _
    exact recursiveAlgebraicForkFrom_tape_sum_runs_le_afk basis k A prefixes rounds final
      win decideWin hmk O
  have hscan := sum_afkScanCharge_steered_le basis k A prefixes rounds final win decideWin hQ hmk
  calc
    _ ≤ ∑ O : T → F,
          (CP * CT ^ Fintype.card F
            + CP * (CT ^ (Fintype.card F - 1) *
                ∑ tape : RecursiveForkTape F d,
                  (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                    (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
            + 2 * afkScanCharge basis k A prefixes rounds final win decideWin
                (prefixes (A.run O) ⟨m, by omega⟩) hmk O
                (O (prefixes (A.run O) ⟨m, by omega⟩))) := hnode
    _ = CO * (CP * CT ^ Fintype.card F)
        + CP * (CT ^ (Fintype.card F - 1) * childSum)
        + 2 * ∑ O : T → F,
            afkScanCharge basis k A prefixes rounds final win decideWin
              (prefixes (A.run O) ⟨m, by omega⟩) hmk O
              (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
          calc
            ∑ O : T → F,
                (CP * CT ^ Fintype.card F
                  + CP * (CT ^ (Fintype.card F - 1) *
                      ∑ tape : RecursiveForkTape F d,
                        (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                          (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
                  + 2 * afkScanCharge basis k A prefixes rounds final win decideWin
                      (prefixes (A.run O) ⟨m, by omega⟩) hmk O
                      (O (prefixes (A.run O) ⟨m, by omega⟩)))
                = (∑ _O : T → F, CP * CT ^ Fintype.card F)
                  + (∑ O : T → F,
                      CP * (CT ^ (Fintype.card F - 1) *
                        ∑ tape : RecursiveForkTape F d,
                          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                            (m + 1) (by omega) O (A.run O) tape.toCoins).runs))
                  + (∑ O : T → F,
                      2 * afkScanCharge basis k A prefixes rounds final win decideWin
                        (prefixes (A.run O) ⟨m, by omega⟩) hmk O
                        (O (prefixes (A.run O) ⟨m, by omega⟩))) := by
                          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            _ = CO * (CP * CT ^ Fintype.card F)
                + CP * (CT ^ (Fintype.card F - 1) * childSum)
                + 2 * ∑ O : T → F,
                    afkScanCharge basis k A prefixes rounds final win decideWin
                      (prefixes (A.run O) ⟨m, by omega⟩) hmk O
                      (O (prefixes (A.run O) ⟨m, by omega⟩)) := by
                  congr 1
                  · congr 1
                    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
                    · rw [← Finset.mul_sum, ← Finset.mul_sum]
                      rfl
                  · rw [← Finset.mul_sum]
    _ ≤ CO * (CP * CT ^ Fintype.card F)
        + CP * (CT ^ (Fintype.card F - 1) * childSum)
        + 2 * (4 * CP *
            (CT ^ (Fintype.card F - 1) * childSum
              + Q * CO * CT ^ Fintype.card F)) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hscan) _
    _ = 9 * Fintype.card (Fin (Fintype.card F) ≃ F) *
            (Fintype.card (RecursiveForkTape F d) ^ (Fintype.card F - 1) *
              ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
                (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                  (m + 1) (by omega) O (A.run O) tape.toCoins).runs)
        + (8 * Q + 1) * Fintype.card (T → F) *
            Fintype.card (Fin (Fintype.card F) ≃ F) *
            Fintype.card (RecursiveForkTape F d) ^ Fintype.card F := by
              dsimp only [CP, CT, CO, childSum]
              ring

/-- A simple closed form for the AFK recurrence. -/
def afkRunBound (Q d : ℕ) : ℕ := (8 * Q + 1) * 10 ^ d

/-- The recursive extractor has an unconditional field-independent polynomial expected call
bound when summed over the oracle table and extractor tape. -/
theorem recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_poly {Q : ℕ}
    (hQ : A.QueryBound Q) :
    ∀ (d m : ℕ) (hmk : m + d = k),
      (∑ O : T → F, ∑ tape : RecursiveForkTape F d,
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            m hmk O (A.run O) tape.toCoins).runs)
        ≤ afkRunBound Q d * Fintype.card (T → F) *
            Fintype.card (RecursiveForkTape F d) := by
  intro d
  induction d with
  | zero =>
      intro m hmk
      have hone : ∀ (O : T → F) (tape : RecursiveForkTape F 0),
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            m hmk O (A.run O) tape.toCoins).runs = 1 := by
        intro O tape
        cases tape
        simp [RecursiveForkTape.toCoins, recursiveAlgebraicForkFrom]
      rw [Finset.sum_congr rfl (fun O _ ↦
        Finset.sum_congr rfl (fun tape _ ↦ hone O tape))]
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      simp only [afkRunBound, pow_zero, mul_one]
      have hfactor : 1 ≤ 8 * Q + 1 := by omega
      simpa only [one_mul, mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (RecursiveForkTape F 0))
          (Nat.mul_le_mul_right (Fintype.card (T → F)) hfactor)
  | succ d ih =>
      intro m hmk
      let N := Fintype.card F
      let CP := Fintype.card (Fin N ≃ F)
      let CT := Fintype.card (RecursiveForkTape F d)
      let CO := Fintype.card (T → F)
      let childSum := ∑ O : T → F, ∑ tape : RecursiveForkTape F d,
        (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          (m + 1) (by omega) O (A.run O) tape.toCoins).runs
      have hstep := recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_step
        basis k A prefixes rounds final win decideWin hQ hmk
      have hih : childSum ≤ afkRunBound Q d * CO * CT := by
        exact ih (m + 1) (by omega)
      have hcard : Fintype.card (RecursiveForkTape F (d + 1)) = CP * CT ^ N := by
        have h := Fintype.card_congr (RecursiveForkTape.equivSucc (F := F) d)
        rwa [Fintype.card_prod, Fintype.card_fun] at h
      have hNpos : 0 < N := Fintype.card_pos
      have hCTpow : CT ^ (N - 1) * CT = CT ^ N := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      have hcoeff : 9 * afkRunBound Q d + (8 * Q + 1) ≤ afkRunBound Q (d + 1) := by
        have hpow : 1 ≤ 10 ^ d := one_le_pow₀ (by omega)
        simp only [afkRunBound]
        calc
          9 * ((8 * Q + 1) * 10 ^ d) + (8 * Q + 1)
              ≤ 9 * ((8 * Q + 1) * 10 ^ d) + (8 * Q + 1) * 10 ^ d := by
                simpa using
                  Nat.add_le_add_left (Nat.mul_le_mul_left (8 * Q + 1) hpow)
                    (9 * ((8 * Q + 1) * 10 ^ d))
          _ = (8 * Q + 1) * 10 ^ (d + 1) := by
                rw [Nat.pow_succ]
                ring
      calc
        _ ≤ 9 * CP * (CT ^ (N - 1) * childSum)
            + (8 * Q + 1) * CO * CP * CT ^ N := by
              simpa only [N, CP, CT, CO, childSum, Nat.succ_eq_add_one] using hstep
        _ ≤ 9 * CP * (CT ^ (N - 1) * (afkRunBound Q d * CO * CT))
            + (8 * Q + 1) * CO * CP * CT ^ N := by
              refine Nat.add_le_add_right ?_ _
              simpa only [mul_assoc] using
                Nat.mul_le_mul_left (9 * CP * CT ^ (N - 1)) hih
        _ = (9 * afkRunBound Q d + (8 * Q + 1)) * CO * (CP * CT ^ N) := by
              rw [← hCTpow]
              ring
        _ ≤ afkRunBound Q (d + 1) * CO * (CP * CT ^ N) := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoeff)
        _ = afkRunBound Q (d + 1) * Fintype.card (T → F) *
              Fintype.card (RecursiveForkTape F (d + 1)) := by
                rw [hcard]
                rfl

/-- Root-level form of the unconditional polynomial AFK call bound. -/
theorem recursiveAlgebraicFork_oracle_tape_sum_runs_le_poly {Q : ℕ}
    (hQ : A.QueryBound Q) :
    ∑ coins : (T → F) × RecursiveForkTape F k,
        (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin
          coins.1 coins.2.toCoins).runs
      ≤ afkRunBound Q k * Fintype.card ((T → F) × RecursiveForkTape F k) := by
  rw [Fintype.sum_prod_type]
  have h := recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_poly
    basis k A prefixes rounds final win decideWin hQ k 0 (by omega)
  simpa only [recursiveAlgebraicFork, Fintype.card_prod, mul_assoc] using h

end PolynomialRunBound
