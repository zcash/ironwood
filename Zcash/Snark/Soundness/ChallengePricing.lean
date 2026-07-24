import Mathlib
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly

/-!
# Pricing the new challenge surfaces

The permutation and lookup chain conditions on more challenges than the quotient check's `x`: the
fold split conditions on `y`, the multiset bridge on `β` and `γ`, the tuple decompression on `θ`,
and every telescoped result carries a vanishing-factor escape branch. Each is a root-set event, and
this module prices them all the same way `hgood` is priced — a uniform-challenge measure bound per
event, from `uniformChallenge_badSet` and a root count.

* `uniformChallenge_szBadSet_iUnion_le` — the shared union bound: finitely many root sets, each of
  degree at most `d`, cost at most `N·d / p` together.
* `goodY_failure_measure_le` — the fold split's `y` surface.
* `perm_gamma/beta_failure_measure_le` — the permutation bridge's two surfaces.
* `escape_measure_le` — a vanishing-factor branch, as the root set of the product of its factors.
* `theta_failure_measure_le` — the decompression's pairwise `θ` surface.

Sequential conditioning across the squeezes is the same coupling hook `hgood` carries — the data
each root set is built from is pinned in the transcript before its challenge is squeezed (θ after
the advice commitments, β and γ after θ, y after the lookup commitments, x last) — documented with
the `hfold`/`hgood` surfaces in `Soundness.VestaBudget` and not re-derived here.
-/

-- TODO: compose these per-surface prices into the terminal knowledge-error bound. Each is bounded
-- here; folding them together needs the sequential-coupling hook above, the same one `hgood`
-- awaits, supplied with the computed-path re-instantiation.

namespace Zcash.Snark

open Polynomial Finset
open scoped ENNReal

/-- **The shared union bound.** Finitely many root-set events, each of degree at most `d`, together
have measure at most `N·d / p`. -/
theorem uniformChallenge_szBadSet_iUnion_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial Fp)
    (d : ℕ) (hdeg : ∀ i ∈ s, (f i).natDegree ≤ d) :
    uniformChallenge.toOuterMeasure {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)}
      ≤ (s.card * d : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  have hsub : {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)} ⊆ ↑(s.biUnion fun i => szBadSet (f i)) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩)
  calc uniformChallenge.toOuterMeasure {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)}
      ≤ uniformChallenge.toOuterMeasure ↑(s.biUnion fun i => szBadSet (f i)) :=
        uniformChallenge.toOuterMeasure.mono hsub
    _ = ((s.biUnion fun i => szBadSet (f i)).card : ℝ≥0∞) / Fintype.card Fp :=
        uniformChallenge_badSet _
    _ ≤ (s.card * d : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
        gcongr
        calc (s.biUnion fun i => szBadSet (f i)).card
            ≤ ∑ i ∈ s, (szBadSet (f i)).card := Finset.card_biUnion_le
          _ ≤ ∑ _i ∈ s, d := Finset.sum_le_sum fun i hi =>
              le_trans (szBadSet_card_le _) (hdeg i hi)
          _ = s.card * d := by rw [Finset.sum_const, smul_eq_mul]

/-- Out-of-range fold-split witnesses vanish: the residues have degree below `n`, so coefficient
`j ≥ n` folds a list of zeros. -/
theorem foldSplitWitness_eq_zero_of_le {cs : List (Polynomial Fp)} {n j : ℕ} (hn : n ≠ 0)
    (hj : n ≤ j) : foldSplitWitness cs n j = 0 := by
  rw [foldSplitWitness]
  refine (foldPoly_eq_zero_iff _).mpr fun v hv => ?_
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ hj)
  rcases eq_or_ne (c %ₘ (X ^ n - 1)) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact Nat.pos_of_ne_zero hn
  · have hdeg := Polynomial.degree_modByMonic_lt c (monic_X_pow_sub_one hn)
    rw [(Polynomial.natDegree_lt_iff_degree_lt h0)]
    have hXn : ((X : Polynomial Fp) ^ n - 1).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree (monic_X_pow_sub_one hn).ne_zero]
      have h2 : ((X : Polynomial Fp) ^ n - 1).natDegree = n := by
        have h1 : ((X : Polynomial Fp) ^ n - 1) = X ^ n - C 1 := by rw [map_one]
        rw [h1, Polynomial.natDegree_X_pow_sub_C]
      exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) h2
    rw [← hXn]
    exact hdeg

/-- **The `y` surface priced.** The fold split's bad event — some coefficient witness roots `y` —
costs at most `n·length / p`. -/
theorem goodY_failure_measure_le (cs : List (Polynomial Fp)) {n : ℕ} (hn : n ≠ 0) :
    uniformChallenge.toOuterMeasure
        {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness cs n j)}
      ≤ (n * cs.length : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  have hset : {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness cs n j)}
      = {y : Fp | ∃ j ∈ range n, y ∈ szBadSet (foldSplitWitness cs n j)} := by
    ext y
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j n with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [foldSplitWitness_eq_zero_of_le hn hge] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range n) _ cs.length fun j _ => ?_) ?_
  · rcases eq_or_ne cs [] with rfl | hne
    · simp [foldSplitWitness, foldPoly]
    · have hne' : cs.map (fun c => (c %ₘ (X ^ n - 1)).coeff j) ≠ [] := by simpa using hne
      have hlt := natDegree_foldPoly_lt hne'
      rw [foldSplitWitness]
      simpa using le_of_lt hlt
  · rw [Finset.card_range]

/-- **The permutation `γ` surface priced.** The linear-product difference has degree at most the
cell count, so the bridge's `γ` condition costs at most `|cells| / p`. -/
theorem perm_gamma_failure_measure_le (sp tp : Multiset (Fp × Fp)) (beta : Fp) :
    uniformChallenge.toOuterMeasure
        ↑(szBadSet (linProdDiff (sp.map (fun q => q.1 + q.2 * beta))
          (tp.map (fun q => q.1 + q.2 * beta))))
      ≤ ((max (Multiset.card sp) (Multiset.card tp) : ℕ) : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge_badSet]
  gcongr
  refine Nat.cast_le.mpr (le_trans (szBadSet_linProdDiff_card_le _ _) ?_)
  simp only [Multiset.card_map]
  exact le_refl _

/-- Each coefficient of the pair-product difference has degree at most the cell count: the factors
`X + C (encPair q)` carry `β`-degree at most one each. -/
theorem natDegree_coeff_pairProdDiff_le (sp tp : Multiset (Fp × Fp)) (j : ℕ) :
    ((pairProdDiff sp tp).coeff j).natDegree ≤ max (Multiset.card sp) (Multiset.card tp) := by
  have key : ∀ (m : Multiset (Fp × Fp)) (j : ℕ),
      (((m.map (fun q => X + C (encPair q))).prod).coeff j).natDegree ≤ Multiset.card m := by
    intro m
    induction m using Multiset.induction with
    | empty =>
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · simp
        · simp [Polynomial.coeff_one, hj]
    | cons q m ih =>
        intro j
        rw [Multiset.map_cons, Multiset.prod_cons, add_mul, Polynomial.coeff_add]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · rcases j with _ | j'
          · simp [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
          · rw [Polynomial.coeff_X_mul]
            exact le_trans (ih j') (by simp)
        · rw [Polynomial.coeff_C_mul]
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          have hencp : (encPair q).natDegree ≤ 1 := by
            refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
            exact le_trans Polynomial.natDegree_mul_le (by simp)
          calc (encPair q).natDegree + (((m.map (fun q => X + C (encPair q))).prod).coeff j).natDegree
              ≤ 1 + Multiset.card m := Nat.add_le_add hencp (ih j)
            _ = Multiset.card (q ::ₘ m) := by rw [Multiset.card_cons]; omega
  rw [pairProdDiff, Polynomial.coeff_sub]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (key sp j) (le_max_left _ _)
  · exact le_trans (key tp j) (le_max_right _ _)

/-- Out-of-range coefficients of the pair-product difference vanish. -/
theorem pairProdDiff_coeff_eq_zero_of_le (sp tp : Multiset (Fp × Fp)) {j : ℕ}
    (hj : max (Multiset.card sp) (Multiset.card tp) < j) : (pairProdDiff sp tp).coeff j = 0 := by
  have key : ∀ (m : Multiset (Fp × Fp)), Multiset.card m < j →
      ((m.map (fun q => X + C (encPair q))).prod).coeff j = 0 := by
    intro m hm
    refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hm)
    have hmap : ∀ m : Multiset (Fp × Fp),
        m.map (fun q => X + C (encPair q)) = (m.map encPair).map (fun u => X + C u) := by
      intro m; simp [Multiset.map_map]
    rw [hmap, natDegree_prod_X_add_u]
    simp
  rw [pairProdDiff, Polynomial.coeff_sub,
    key sp (lt_of_le_of_lt (le_max_left _ _) hj), key tp (lt_of_le_of_lt (le_max_right _ _) hj),
    sub_self]

/-- **The permutation `β` surface priced.** Some coefficient of the pair-product difference roots
`β` — at most `(|cells| + 1) · |cells| / p`. -/
theorem perm_beta_failure_measure_le (sp tp : Multiset (Fp × Fp)) :
    uniformChallenge.toOuterMeasure
        {b : Fp | ∃ j, b ∈ szBadSet ((pairProdDiff sp tp).coeff j)}
      ≤ ((max (Multiset.card sp) (Multiset.card tp) + 1)
          * max (Multiset.card sp) (Multiset.card tp) : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  set d := max (Multiset.card sp) (Multiset.card tp) with hd
  have hset : {b : Fp | ∃ j, b ∈ szBadSet ((pairProdDiff sp tp).coeff j)}
      = {b : Fp | ∃ j ∈ range (d + 1), b ∈ szBadSet ((pairProdDiff sp tp).coeff j)} := by
    ext b
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j (d + 1) with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [pairProdDiff_coeff_eq_zero_of_le sp tp (by omega)] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range (d + 1)) _ d
    fun j _ => natDegree_coeff_pairProdDiff_le sp tp j) ?_
  simp

/-- **A vanishing-factor escape priced.** The event that some listed factor `v + challenge` vanishes
is the root set of the product `∏ (X + v)`, so it costs at most the factor count over `p`. -/
theorem escape_measure_le (vs : Multiset Fp) :
    uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ (Multiset.card vs : ℝ≥0∞) / Fintype.card Fp := by
  have hsub : {x : Fp | ∃ v ∈ vs, v + x = 0}
      ⊆ ↑(szBadSet ((vs.map (fun v => X + C v)).prod)) := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [Finset.mem_coe, mem_szBadSet]
    constructor
    · exact (monic_multiset_prod_of_monic _ _ fun u _ => monic_X_add_C u).ne_zero
    · rw [eval_prod_X_add_u]
      refine Multiset.prod_eq_zero ?_
      refine Multiset.mem_map.mpr ⟨v, hv, ?_⟩
      linear_combination hvx
  calc uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ uniformChallenge.toOuterMeasure ↑(szBadSet ((vs.map (fun v => X + C v)).prod)) :=
        uniformChallenge.toOuterMeasure.mono hsub
    _ ≤ _ := by
        rw [uniformChallenge_badSet]
        gcongr
        calc (szBadSet ((vs.map (fun v => X + C v)).prod)).card
            ≤ ((vs.map (fun v => X + C v)).prod).natDegree := szBadSet_card_le _
          _ ≤ Multiset.card vs := by rw [natDegree_prod_X_add_u]

/-- **The `θ` surface priced.** The pairwise decompression condition over `N` rows of arity at most
`r` costs at most `N²·r / p`. -/
theorem theta_failure_measure_le {N r : ℕ} (inputT tableT : ℕ → List Fp)
    (hlen : ∀ i < N, (inputT i).length ≤ r ∧ (tableT i).length ≤ r) :
    uniformChallenge.toOuterMeasure
        {θ : Fp | ∃ q ∈ range N ×ˢ range N,
          θ ∈ szBadSet (foldPoly (inputT q.1) - foldPoly (tableT q.2))}
      ≤ (N * N * r : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range N ×ˢ range N)
    (fun q => foldPoly (inputT q.1) - foldPoly (tableT q.2)) r fun q hq => ?_) ?_
  · obtain ⟨h1, h2⟩ := mem_product.mp hq
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rcases eq_or_ne (inputT q.1) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.1 (mem_range.mp h1)).1)
    · rcases eq_or_ne (tableT q.2) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.2 (mem_range.mp h2)).2)
  · simp [mul_assoc]

end Zcash.Snark
