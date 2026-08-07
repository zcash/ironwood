import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Argument.GrandProductBridge
import Zcash.Snark.Soundness.Argument.LookupAssembly
import Zcash.Snark.Soundness.Canonical.LookupSemantics
import Zcash.Snark.Soundness.Canonical.PermutationSemantics
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Common.RelationWitness

/-!
# Pricing the new challenge surfaces

The permutation and lookup chains condition on more challenges than the quotient check's `x`: the
fold split on `y`, the multiset bridge on `β` and `γ`, the tuple decompression on `θ`, and every
telescoped result carries a vanishing-factor escape. Each is a root-set event, priced the way
`hgood` is — a uniform-challenge measure bound from `uniformChallenge_badSet` and a root count.

* `uniformChallenge_szBadSet_iUnion_le` — the shared union bound: `N` root sets of degree at most
  `d` cost `N·d / p` together.
* `goodY_failure_measure_le`, `perm_gamma/beta_failure_measure_le`,
  `lookup_gamma/beta_failure_measure_le`, `theta_failure_measure_le` — the individual surfaces.
* `escape_measure_le` — a vanishing-factor branch, as the root set of its factors' product.

Sequential conditioning across the squeezes is the coupling `hgood` already carries: each root
set's data is pinned in the transcript before its challenge is squeezed (`θ` after the advice
commitments, `β` and `γ` after `θ`, `y` after the lookup commitments, `x` last). It is documented
with the deployed constraint decoder's surfaces, not re-derived here.

The final section adds the bundle-wide resolver permutation prices, so one module carries the
whole challenge-pricing story.
-/

-- The semantic terminal API consumes four explicit bad-event bounds, one for each surface below.
-- A concrete instantiation must obtain those bounds through the sequential-coupling hook above;
-- the compressed-identity capstone deliberately cannot be presented as semantic soundness
-- without them.

namespace Zcash.Snark

open Halo2 Polynomial Finset CompPoly
open CompPoly.CPolynomial (natDegree_toPoly toPoly_eq_zero_iff)
open scoped ENNReal

/-- **The shared union bound.** Finitely many root-set events, each of degree at most `d`, together
have measure at most `N·d / p`. -/
theorem uniformChallenge_szBadSet_iUnion_le {ι : Type*} (s : Finset ι) (f : ι → CPoly)
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
theorem foldSplitWitness_zero_of_le {cs : List (CPoly)} {n j : ℕ} (hn : n ≠ 0)
    (hj : n ≤ j) : foldSplitWitness cs n j = 0 := by
  rw [foldSplitWitness]
  refine (foldPoly_eq_zero_iff _).mpr fun v hv => ?_
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
  refine CPolynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ hj)
  have hmonic : ((CPolynomial.X : CPoly) ^ n - 1).monic := monic_X_pow_sub_one hn
  have hmonicP : (((CPolynomial.X : CPoly) ^ n - 1).toPoly).Monic := (CPolynomial.monic_toPoly_iff _).mp hmonic
  have hXn : (((CPolynomial.X : CPoly) ^ n - 1).toPoly).natDegree = n := by
    simp only [CPolynomial.toPoly_sub, CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.toPoly_one]
    simpa using Polynomial.natDegree_X_pow_sub_C (n := n) (r := (1 : Fp))
  rw [CPolynomial.natDegree_toPoly, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hmonic]
  have hlt := Polynomial.degree_modByMonic_lt c.toPoly hmonicP
  rw [Polynomial.degree_eq_natDegree hmonicP.ne_zero, hXn] at hlt
  rcases eq_or_ne (c.toPoly %ₘ ((CPolynomial.X : CPoly) ^ n - 1).toPoly) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact Nat.pos_of_ne_zero hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt

/-- **The `y` surface priced.** The fold split's bad event — some coefficient witness roots `y` —
costs at most `n·length / p`. -/
theorem goodY_failure_measure_le (cs : List (CPoly)) {n : ℕ} (hn : n ≠ 0) :
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
      · rw [foldSplitWitness_zero_of_le hn hge] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range n) _ cs.length fun j _ => ?_) ?_
  · rcases eq_or_ne cs [] with rfl | hne
    · simp [foldSplitWitness, foldPoly]
    · have hne' : cs.map (fun c => (vanishingRemainder c n).coeff j) ≠ [] := by simpa using hne
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
    (CPolynomial.coeff (pairProdDiff sp tp) j).natDegree
      ≤ max (Multiset.card sp) (Multiset.card tp) := by
  have hencp : ∀ (m : Multiset (Fp × Fp)) (p : CPoly), p ∈ m.map encPair → p.natDegree ≤ 1 := by
    rintro m _ hp
    obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
    rw [encPair]
    refine le_trans (CompPoly.CPolynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [CompPoly.CPolynomial.natDegree_C]
      exact Nat.zero_le 1
    · refine le_trans CompPoly.CPolynomial.natDegree_mul_le ?_
      rw [CompPoly.CPolynomial.natDegree_C]
      exact le_trans (Nat.add_le_add_left CompPoly.CPolynomial.natDegree_X_le 0) (by omega)
  -- Each `γ` coefficient is an elementary symmetric function of the `β`-linear encodings, so its
  -- degree is at most one per factor taken.
  have key : ∀ m : Multiset (Fp × Fp),
      CompPoly.CPolynomial.natDegree
          (CPolynomial.coeff ((m.map (fun p =>
            (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (encPair p) : CBiPoly))).prod) j)
        ≤ Multiset.card m := by
    intro m
    have hmap : m.map (fun p =>
        (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (encPair p) : CBiPoly))
        = (m.map encPair).map (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    rcases le_or_gt j (Multiset.card (m.map encPair)) with hj | hj
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C _ hj]
      refine le_trans (CompPoly.CPolynomial.natDegree_esymm_le (hencp m) _) ?_
      rw [Multiset.card_map] at hj ⊢
      omega
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C_eq_zero _ hj]
      exact le_trans (le_of_eq CompPoly.CPolynomial.natDegree_zero) (Nat.zero_le _)
  rw [pairProdDiff, CompPoly.CPolynomial.coeff_sub]
  refine le_trans (CompPoly.CPolynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (key sp) (le_max_left _ _)
  · exact le_trans (key tp) (le_max_right _ _)

/-- Out-of-range coefficients of the pair-product difference vanish. -/
theorem pairProdDiff_coeff_eq_zero_of_le (sp tp : Multiset (Fp × Fp)) {j : ℕ}
    (hj : max (Multiset.card sp) (Multiset.card tp) < j) :
    CPolynomial.coeff (pairProdDiff sp tp) j = 0 := by
  have key : ∀ m : Multiset (Fp × Fp), Multiset.card m < j →
      CPolynomial.coeff ((m.map (fun p =>
        (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (encPair p) : CBiPoly))).prod) j = 0 := by
    intro m hm
    have hmap : m.map (fun p =>
        (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (encPair p) : CBiPoly))
        = (m.map encPair).map (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    exact CompPoly.CPolynomial.coeff_prod_X_add_C_eq_zero _ (by simpa using hm)
  rw [pairProdDiff, CompPoly.CPolynomial.coeff_sub,
    key sp (lt_of_le_of_lt (le_max_left _ _) hj), key tp (lt_of_le_of_lt (le_max_right _ _) hj),
    sub_self]

/-- **The permutation `β` surface priced.** Some coefficient of the pair-product difference roots
`β` — at most `(|cells| + 1) · |cells| / p`. -/
theorem perm_beta_failure_measure_le (sp tp : Multiset (Fp × Fp)) :
    uniformChallenge.toOuterMeasure
        {b : Fp | ∃ j, b ∈ szBadSet (pairProdDiffCoeff sp tp j)}
      ≤ ((max (Multiset.card sp) (Multiset.card tp) + 1)
          * max (Multiset.card sp) (Multiset.card tp) : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  set d := max (Multiset.card sp) (Multiset.card tp) with hd
  have hset : {b : Fp | ∃ j, b ∈ szBadSet (pairProdDiffCoeff sp tp j)}
      = {b : Fp | ∃ j ∈ range (d + 1), b ∈ szBadSet (pairProdDiffCoeff sp tp j)} := by
    ext b
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j (d + 1) with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [show pairProdDiffCoeff sp tp j = 0 from by
              rw [toPoly_pairProdDiffCoeff]
              exact pairProdDiff_coeff_eq_zero_of_le sp tp (by omega)] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range (d + 1)) _ d
    fun j _ => by
      rw [toPoly_pairProdDiffCoeff]
      exact natDegree_coeff_pairProdDiff_le sp tp j) ?_
  simp

/-- The lookup product difference has `γ`-degree bounded by the larger table column. The two input
columns occur only in its coefficients. -/
theorem natDegree_lookupProdDiff_le (a s inp tbl : Multiset Fp) :
    (lookupProdDiff a s inp tbl).natDegree ≤
      max (Multiset.card s) (Multiset.card tbl) := by
  have key : ∀ m : Multiset Fp,
      CompPoly.CPolynomial.natDegree ((m.map (fun u =>
        (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (CompPoly.CPolynomial.C u)
          : CBiPoly))).prod) = Multiset.card m := by
    intro m
    have hmap : m.map (fun u => (CompPoly.CPolynomial.X
        + CompPoly.CPolynomial.C (CompPoly.CPolynomial.C u) : CBiPoly))
        = (m.map CompPoly.CPolynomial.C).map
            (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap, CompPoly.CPolynomial.natDegree_prod_X_add_C, Multiset.card_map]
  rw [lookupProdDiff]
  refine le_trans (CompPoly.CPolynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (CompPoly.CPolynomial.natDegree_C_mul_le _ _)
      (le_trans (le_of_eq (key s)) (le_max_left _ _))
  · exact le_trans (CompPoly.CPolynomial.natDegree_C_mul_le _ _)
      (le_trans (le_of_eq (key tbl)) (le_max_right _ _))

/-- Out-of-range `γ` coefficients of the lookup product difference vanish. -/
theorem lookupProdDiff_coeff_eq_zero_of_le (a s inp tbl : Multiset Fp) {j : ℕ}
    (hj : max (Multiset.card s) (Multiset.card tbl) < j) :
    CPolynomial.coeff (lookupProdDiff a s inp tbl) j = 0 := by
  exact CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_lookupProdDiff_le a s inp tbl) hj)

/-- Every `γ` coefficient of the lookup product difference has `β`-degree bounded by the larger
input column. The table factors have coefficients that are constant in `β`. -/
theorem natDegree_coeff_lookupProdDiff_le
    (a s inp tbl : Multiset Fp) (j : ℕ) :
    (CPolynomial.coeff (lookupProdDiff a s inp tbl) j).natDegree ≤
      max (Multiset.card a) (Multiset.card inp) := by
  -- The table factors are constant in `β`, so every one of their `γ` coefficients is too.
  have tableCoeff : ∀ m : Multiset Fp,
      CompPoly.CPolynomial.natDegree (CPolynomial.coeff ((m.map (fun u =>
        (CompPoly.CPolynomial.X + CompPoly.CPolynomial.C (CompPoly.CPolynomial.C u)
          : CBiPoly))).prod) j) ≤ 0 := by
    intro m
    have hmap : m.map (fun u => (CompPoly.CPolynomial.X
        + CompPoly.CPolynomial.C (CompPoly.CPolynomial.C u) : CBiPoly))
        = (m.map CompPoly.CPolynomial.C).map
            (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    rcases le_or_gt j (Multiset.card (m.map (CompPoly.CPolynomial.C : Fp → CPoly))) with hj | hj
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C _ hj]
      refine le_trans (CompPoly.CPolynomial.natDegree_esymm_le (d := 0) ?_ _) (by omega)
      rintro _ hp
      obtain ⟨u, _, rfl⟩ := Multiset.mem_map.mp hp
      exact le_of_eq (CompPoly.CPolynomial.natDegree_C u)
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C_eq_zero _ hj]
      exact le_of_eq CompPoly.CPolynomial.natDegree_zero
  have hlin : ∀ m : Multiset Fp,
      CompPoly.CPolynomial.natDegree ((m.map (fun u =>
        CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u)).prod) = Multiset.card m :=
    fun m => CompPoly.CPolynomial.natDegree_prod_X_add_C m
  rw [lookupProdDiff, CompPoly.CPolynomial.coeff_sub, CompPoly.CPolynomial.coeff_C_mul,
    CompPoly.CPolynomial.coeff_C_mul]
  refine le_trans (CompPoly.CPolynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans CompPoly.CPolynomial.natDegree_mul_le ?_
    exact le_trans (Nat.add_le_add (le_of_eq (hlin a)) (tableCoeff s))
      (by simp)
  · refine le_trans CompPoly.CPolynomial.natDegree_mul_le ?_
    exact le_trans (Nat.add_le_add (le_of_eq (hlin inp)) (tableCoeff tbl))
      (by simp)

/-- **The lookup `γ` surface priced.** Once `β` is fixed, the lookup product difference has one
root per table row at most. -/
theorem lookup_gamma_failure_measure_le
    (a s inp tbl : Multiset Fp) (beta : Fp) :
    uniformChallenge.toOuterMeasure
        ↑(szBadSet (lookupProdDiffGamma a s inp tbl beta))
      ≤ (max (Multiset.card s) (Multiset.card tbl) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  refine le_trans (szBadSet_card_le _) ?_
  rw [lookupProdDiffGamma_eq_map]
  exact le_trans (CompPoly.CPolynomial.natDegree_map_le _ _)
    (natDegree_lookupProdDiff_le a s inp tbl)

/-- **The lookup `β` surface priced.** There is one root set for each potentially nonzero
`γ` coefficient, and each such coefficient has degree at most the larger input-column size. -/
theorem lookup_beta_failure_measure_le (a s inp tbl : Multiset Fp) :
    uniformChallenge.toOuterMeasure
        {b : Fp | ∃ j, b ∈ szBadSet (lookupProdDiffCoeff a s inp tbl j)}
      ≤ ((max (Multiset.card s) (Multiset.card tbl) + 1)
          * max (Multiset.card a) (Multiset.card inp) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  set ds := max (Multiset.card s) (Multiset.card tbl) with hds
  set da := max (Multiset.card a) (Multiset.card inp) with hda
  have hset : {b : Fp | ∃ j, b ∈ szBadSet (lookupProdDiffCoeff a s inp tbl j)}
      = {b : Fp | ∃ j ∈ range (ds + 1),
          b ∈ szBadSet (lookupProdDiffCoeff a s inp tbl j)} := by
    ext b
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j (ds + 1) with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [show lookupProdDiffCoeff a s inp tbl j = 0 from by
              rw [toPoly_lookupProdDiffCoeff]
              exact lookupProdDiff_coeff_eq_zero_of_le a s inp tbl (by omega)] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range (ds + 1)) _ da
    fun j _ => ?_) ?_
  · rw [toPoly_lookupProdDiffCoeff]
    simpa [hda] using natDegree_coeff_lookupProdDiff_le a s inp tbl j
  · simp [hds, hda]

/-! ## Resolver-backed lookup challenge families -/

/-- The complete `γ` exclusion for one deployed lookup: the product-difference roots together
with the table-column zero factors used to eliminate the residual running-product branch. -/
def resolverLookupGammaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) : Finset Fp :=
  szBadSet (resolverLookupProductDifferenceGamma vk ch poly p l u) ∪
  lookupColumnZeroBadSet vk.omega
    (lookupTablePolyOfResolver vk ch poly p l) (u + 1)

/-- The complete `β` exclusion for one deployed lookup: every potentially nonzero coefficient of
the product difference together with the input-column zero factors. There are at most `u + 2`
coefficients because the `γ` degree is at most `u + 1`. -/
def resolverLookupBetaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) : Finset Fp :=
  ((Finset.range (u + 2)).biUnion fun j =>
    szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)) ∪
  lookupColumnZeroBadSet vk.omega
    (lookupInputPolyOfResolver vk ch poly p l) (u + 1)

/-- Avoiding the two finite bad sets supplies exactly the four challenge facts consumed by one
resolver-backed lookup endpoint. -/
theorem ResolverLookupGoodChallenges.ofBadSets
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (hgamma : ch.gamma ∉ resolverLookupGammaBadSet vk ch poly p l u)
    (hbeta : ch.beta ∉ resolverLookupBetaBadSet vk ch poly p l u) :
    ResolverLookupGoodChallenges vk ch poly p l u where
  gamma hmem := hgamma (Finset.mem_union_left _ hmem)
  beta j := by
    by_cases hj : j < u + 2
    · intro hmem
      apply hbeta
      rw [resolverLookupBetaBadSet]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hmem⟩)
    · have hzero : resolverLookupProductDifferenceCoeff vk ch poly p l u j = 0 := by
        rw [toPoly_resolverLookupProductDifferenceCoeff]
        apply lookupProdDiff_coeff_eq_zero_of_le
        simpa [resolverLookupProductDifference] using (show u + 1 < j by omega)
      simp [hzero, szBadSet]
  inputNonzero hmem := hbeta (by
    rw [resolverLookupBetaBadSet]
    exact Finset.mem_union_right _ hmem)
  tableNonzero hmem := hgamma (by
    rw [resolverLookupGammaBadSet]
    exact Finset.mem_union_right _ hmem)

/-- One deployed lookup's full `γ` exclusion costs at most two values per participating row: one
for multiset recovery and one for the table-column zero factor. -/
theorem resolverLookupGammaBadSet_card_le
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    (resolverLookupGammaBadSet vk ch poly p l u).card ≤ 2 * (u + 1) := by
  have hroot :
      (szBadSet (resolverLookupProductDifferenceGamma vk ch poly p l u)).card ≤ u + 1 := by
    refine le_trans (szBadSet_card_le _) ?_
    rw [toPoly_resolverLookupProductDifferenceGamma]
    refine le_trans (CompPoly.CPolynomial.natDegree_map_le _ _) ?_
    rw [resolverLookupProductDifference]
    simpa using
      natDegree_lookupProdDiff_le
        (Finset.univ.val.map
          (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
        (Finset.univ.val.map
          (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
        (Finset.univ.val.map
          (lookupColumnRows vk.omega
            (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
        (Finset.univ.val.map
          (lookupColumnRows vk.omega
            (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))
  have hzero :
      (lookupColumnZeroBadSet vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card ≤ u + 1 := by
    rw [lookupColumnZeroBadSet]
    simpa using additiveZeroBadSet_card_le
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1))
  rw [resolverLookupGammaBadSet]
  calc
    (szBadSet (resolverLookupProductDifferenceGamma vk ch poly p l u) ∪
        lookupColumnZeroBadSet vk.omega
          (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card
      ≤ (szBadSet (resolverLookupProductDifferenceGamma vk ch poly p l u)).card +
          (lookupColumnZeroBadSet vk.omega
            (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card := by
        exact Finset.card_union_le _ _
    _ ≤ (u + 1) + (u + 1) := Nat.add_le_add hroot hzero
    _ = 2 * (u + 1) := by omega

/-- Uniform `γ` hits one deployed lookup's complete bad set with probability at most two values
per participating row over the scalar-field size. -/
theorem uniformChallenge_resolverLookupGammaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverLookupGammaBadSet vk ch poly p l u)
      ≤ (2 * (u + 1) : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast resolverLookupGammaBadSet_card_le vk ch poly p l u

/-- One deployed lookup's full `β` exclusion costs at most
`(u + 2)·(u + 1) + (u + 1) = (u + 3)·(u + 1)` challenge values. -/
theorem resolverLookupBetaBadSet_card_le
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    (resolverLookupBetaBadSet vk ch poly p l u).card ≤
      (u + 2) * (u + 1) + (u + 1) := by
  have hcoeff : ∀ j,
      (szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)).card
        ≤ u + 1 := by
    intro j
    refine le_trans (szBadSet_card_le _) ?_
    rw [toPoly_resolverLookupProductDifferenceCoeff]
    exact (by
      simpa [resolverLookupProductDifference] using
        natDegree_coeff_lookupProdDiff_le
          (Finset.univ.val.map
            (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega
              (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega
              (lookupTablePolyOfResolver vk ch poly p l) (u + 1))) j)
  have hzero :
      (lookupColumnZeroBadSet vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card ≤ u + 1 := by
    rw [lookupColumnZeroBadSet]
    simpa using additiveZeroBadSet_card_le
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1))
  rw [resolverLookupBetaBadSet]
  calc
    (((Finset.range (u + 2)).biUnion fun j =>
          szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)) ∪
        lookupColumnZeroBadSet vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card
      ≤ ((Finset.range (u + 2)).biUnion fun j =>
          szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)).card +
        (lookupColumnZeroBadSet vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card := by
        exact Finset.card_union_le _ _
    _ ≤ (∑ j ∈ Finset.range (u + 2),
          (szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)).card) +
        (u + 1) := Nat.add_le_add Finset.card_biUnion_le hzero
    _ ≤ (∑ _j ∈ Finset.range (u + 2), (u + 1)) + (u + 1) := by
      exact Nat.add_le_add (Finset.sum_le_sum fun j _ => hcoeff j) (le_refl _)
    _ = (u + 2) * (u + 1) + (u + 1) := by simp

/-- Uniform `β` hits one deployed lookup's complete coefficient/zero-factor bad set with the
corresponding root-count probability. -/
theorem uniformChallenge_resolverLookupBetaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverLookupBetaBadSet vk ch poly p l u)
      ≤ ((u + 2) * (u + 1) + (u + 1) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast resolverLookupBetaBadSet_card_le vk ch poly p l u

/-- The union of all lookup `γ` exclusions in one proof bundle. The challenge is shared by every
proof and lookup argument, so this is the event the transcript squeeze must avoid. -/
def allResolverLookupGammaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)).biUnion fun q =>
    resolverLookupGammaBadSet vk ch poly q.1 q.2 u

/-- The union of all lookup `β` exclusions in one proof bundle. -/
def allResolverLookupBetaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)).biUnion fun q =>
    resolverLookupBetaBadSet vk ch poly q.1 q.2 u

/-- Avoiding the bundle-wide lookup bad sets supplies the good-challenge record for every proof
and every deployed lookup argument. -/
theorem resolverLookupGoodChallenges_of_not_mem
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ)
    (hgamma : ch.gamma ∉ allResolverLookupGammaBadSet numProofs vk ch poly u)
    (hbeta : ch.beta ∉ allResolverLookupBetaBadSet numProofs vk ch poly u) :
    ∀ (p : Fin numProofs) (l : Fin shape.numLookups),
      ResolverLookupGoodChallenges vk ch poly p l u := by
  intro p l
  apply ResolverLookupGoodChallenges.ofBadSets
  · intro hmem
    apply hgamma
    exact Finset.mem_biUnion.mpr ⟨(p, l), Finset.mem_univ _, hmem⟩
  · intro hmem
    apply hbeta
    exact Finset.mem_biUnion.mpr ⟨(p, l), Finset.mem_univ _, hmem⟩

/-- Compute one lookup good-challenge package from finite point tests.  As with the permutation
adapter, the specification-level root sets appear only in erased proofs. -/
def resolverLookupGoodChallenges?
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    Option (PLift (ResolverLookupGoodChallenges vk ch poly p l u)) := by
  let gammaDifference := resolverLookupProductDifferenceGamma vk ch poly p l u
  let input := lookupInputPolyOfResolver vk ch poly p l
  let table := lookupTablePolyOfResolver vk ch poly p l
  match szBadSetAvoidance? gammaDifference ch.gamma with
  | none => exact none
  | some hgammaProof =>
      match finForallOption (fun j : Fin (u + 2) =>
          szBadSetAvoidance?
            (resolverLookupProductDifferenceCoeff vk ch poly p l u j.1) ch.beta) with
      | none => exact none
      | some hbetaProof =>
          if hinput : ∀ i : Fin (u + 1),
              input.eval (vk.omega ^ (i : Nat)) + ch.beta ≠ 0 then
            if htable : ∀ i : Fin (u + 1),
                table.eval (vk.omega ^ (i : Nat)) + ch.gamma ≠ 0 then
              exact some ⟨{
                gamma := hgammaProof.down
                beta := fun j => by
                  by_cases hj : j < u + 2
                  · exact (hbetaProof ⟨j, hj⟩).down
                  · have hzero :
                        resolverLookupProductDifferenceCoeff vk ch poly p l u j = 0 := by
                      rw [toPoly_resolverLookupProductDifferenceCoeff]
                      apply lookupProdDiff_coeff_eq_zero_of_le
                      simpa [resolverLookupProductDifference] using
                        (show u + 1 < j by omega)
                    exact not_mem_szBadSet.mpr fun hne => False.elim (hne hzero)
                inputNonzero := by
                  intro hmem
                  obtain ⟨i, hi⟩ :=
                    (mem_lookupColumnZeroBadSet_iff vk.omega input (u + 1) ch.beta).mp hmem
                  exact hinput i hi
                tableNonzero := by
                  intro hmem
                  obtain ⟨i, hi⟩ :=
                    (mem_lookupColumnZeroBadSet_iff vk.omega table (u + 1) ch.gamma).mp hmem
                  exact htable i hi }⟩
            else exact none
          else exact none

/-- Executable bundle-wide lookup `β`/`γ` exclusions. -/
def resolverLookupBundleExclusions?
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) :
    Option (PLift ((ch.gamma ∉ allResolverLookupGammaBadSet numProofs vk ch poly u) ∧
      ch.beta ∉ allResolverLookupBetaBadSet numProofs vk ch poly u)) :=
  match finForallOption (fun p : Fin numProofs =>
      finForallOption (fun l : Fin shape.numLookups =>
        resolverLookupGoodChallenges? vk ch poly p l u)) with
  | none => none
  | some good => some ⟨
      ⟨by
        intro hmem
        obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hmem
        exact (Finset.mem_union.mp hq).elim
          (good q.1 q.2).down.gamma (good q.1 q.2).down.tableNonzero,
       by
        intro hmem
        obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hmem
        rcases Finset.mem_union.mp hq with hroots | hzero
        · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hroots
          exact (good q.1 q.2).down.beta j hj
        · exact (good q.1 q.2).down.inputNonzero hzero⟩⟩

theorem resolverLookupGoodChallenges?_isSome_of
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (hgood : ResolverLookupGoodChallenges vk ch poly p l u) :
    (resolverLookupGoodChallenges? vk ch poly p l u).isSome := by
  let gammaDifference := resolverLookupProductDifferenceGamma vk ch poly p l u
  let input := lookupInputPolyOfResolver vk ch poly p l
  let table := lookupTablePolyOfResolver vk ch poly p l
  have hgammaGood : ch.gamma ∉ szBadSet gammaDifference := by
    dsimp only [gammaDifference]
    exact hgood.gamma
  dsimp only [gammaDifference] at hgammaGood
  obtain ⟨gammaProof, hgammaEq⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hgammaGood)
  have hbetaFinite : ∀ j : Fin (u + 2),
      (szBadSetAvoidance?
        (resolverLookupProductDifferenceCoeff vk ch poly p l u j.1) ch.beta).isSome :=
    fun j => (szBadSetAvoidance?_isSome_iff _ _).2 (hgood.beta j.1)
  have hinput : ∀ i : Fin (u + 1),
      input.eval (vk.omega ^ (i : Nat)) + ch.beta ≠ 0 := by
    intro i hzero
    exact hgood.inputNonzero
      ((mem_lookupColumnZeroBadSet_iff vk.omega input (u + 1) ch.beta).2 ⟨i, hzero⟩)
  have htable : ∀ i : Fin (u + 1),
      table.eval (vk.omega ^ (i : Nat)) + ch.gamma ≠ 0 := by
    intro i hzero
    exact hgood.tableNonzero
      ((mem_lookupColumnZeroBadSet_iff vk.omega table (u + 1) ch.gamma).2 ⟨i, hzero⟩)
  obtain ⟨betaProof, hbetaEq⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hbetaFinite)
  dsimp only [input] at hinput
  dsimp only [table] at htable
  simp only [resolverLookupGoodChallenges?, hgammaEq, hbetaEq]
  rw [dif_pos hinput, dif_pos htable]
  rfl

theorem resolverLookupBundleExclusions?_isSome_of
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ)
    (hgamma : ch.gamma ∉ allResolverLookupGammaBadSet numProofs vk ch poly u)
    (hbeta : ch.beta ∉ allResolverLookupBetaBadSet numProofs vk ch poly u) :
    (resolverLookupBundleExclusions? numProofs vk ch poly u).isSome := by
  have hall : ∀ q : Fin numProofs × Fin shape.numLookups,
      (resolverLookupGoodChallenges? vk ch poly q.1 q.2 u).isSome :=
    fun q => resolverLookupGoodChallenges?_isSome_of vk ch poly q.1 q.2 u
      (resolverLookupGoodChallenges_of_not_mem numProofs vk ch poly u hgamma hbeta q.1 q.2)
  have hinner : ∀ p : Fin numProofs,
      (finForallOption (fun l : Fin shape.numLookups =>
        resolverLookupGoodChallenges? vk ch poly p l u)).isSome :=
    fun p => finForallOption_isSome_of _ (fun l => hall (p, l))
  obtain ⟨good, hgood⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hinner)
  unfold resolverLookupBundleExclusions?
  generalize hresult : finForallOption (fun p : Fin numProofs =>
      finForallOption (fun l : Fin shape.numLookups =>
        resolverLookupGoodChallenges? vk ch poly p l u)) = result at hgood ⊢
  cases result <;> simp_all

/-- The bundle-wide lookup `γ` surface is the number of proof/lookup pairs times the per-argument
two-values-per-row budget. -/
theorem uniformChallenge_allResolverLookupGammaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupGammaBadSet numProofs vk ch poly u)
      ≤ (numProofs * shape.numLookups * (2 * (u + 1)) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverLookupGammaBadSet]
  calc
    ((Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)).biUnion
        fun q => resolverLookupGammaBadSet vk ch poly q.1 q.2 u).card
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)),
          (resolverLookupGammaBadSet vk ch poly q.1 q.2 u).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)),
          2 * (u + 1) := Finset.sum_le_sum fun q _ =>
            resolverLookupGammaBadSet_card_le vk ch poly q.1 q.2 u
    _ = numProofs * shape.numLookups * (2 * (u + 1)) := by simp

/-- The bundle-wide lookup `β` surface is the number of proof/lookup pairs times the
coefficient-and-zero-factor budget for one argument. -/
theorem uniformChallenge_allResolverLookupBetaBadSet
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupBetaBadSet numProofs vk ch poly u)
      ≤ (numProofs * shape.numLookups *
          ((u + 2) * (u + 1) + (u + 1)) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverLookupBetaBadSet]
  calc
    ((Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)).biUnion
        fun q => resolverLookupBetaBadSet vk ch poly q.1 q.2 u).card
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)),
          (resolverLookupBetaBadSet vk ch poly q.1 q.2 u).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin numProofs × Fin shape.numLookups)),
          ((u + 2) * (u + 1) + (u + 1)) := Finset.sum_le_sum fun q _ =>
            resolverLookupBetaBadSet_card_le vk ch poly q.1 q.2 u
    _ = numProofs * shape.numLookups *
        ((u + 2) * (u + 1) + (u + 1)) := by simp

/-- **A vanishing-factor escape priced.** The event that some listed factor `v + challenge` vanishes
is the root set of the product `∏ (X + v)`, so it costs at most the factor count over `p`. -/
theorem escape_measure_le (vs : Multiset Fp) :
    uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ (Multiset.card vs : ℝ≥0∞) / Fintype.card Fp := by
  have hsub : {x : Fp | ∃ v ∈ vs, v + x = 0}
      ⊆ ↑(szBadSet ((vs.map (fun v => CPolynomial.X + CPolynomial.C v)).prod)) := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [Finset.mem_coe, mem_szBadSet]
    constructor
    · rw [Ne, ← CPolynomial.toPoly_eq_zero_iff, CPolynomial.toPoly_multiset_prod,
        Multiset.map_map]
      simpa [Function.comp_def] using
        (monic_multiset_prod_of_monic (R := Fp) vs (fun v => X + C v)
          fun u _ => monic_X_add_C u).ne_zero
    · rw [eval_cprod_X_add_u]
      refine Multiset.prod_eq_zero ?_
      refine Multiset.mem_map.mpr ⟨v, hv, ?_⟩
      linear_combination hvx
  calc uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ uniformChallenge.toOuterMeasure ↑(szBadSet ((vs.map (fun v => CPolynomial.X + CPolynomial.C v)).prod)) :=
        uniformChallenge.toOuterMeasure.mono hsub
    _ ≤ _ := by
        rw [uniformChallenge_badSet]
        gcongr
        calc (szBadSet ((vs.map (fun v => CPolynomial.X + CPolynomial.C v)).prod)).card
            ≤ ((vs.map (fun v => CPolynomial.X + CPolynomial.C v)).prod).natDegree := szBadSet_card_le _
          _ ≤ Multiset.card vs :=
              (CompPoly.CPolynomial.natDegree_prod_X_add_C vs).le

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
    refine le_trans (CPolynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rcases eq_or_ne (inputT q.1) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.1 (mem_range.mp h1)).1)
    · rcases eq_or_ne (tableT q.2) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.2 (mem_range.mp h2)).2)
  · simp [mul_assoc]

/-! The operation-level lookup bridge has one `thetaBadSet` per enabled lookup activation (and per
proof assignment). The following family union is the exact finite event a shared `θ` squeeze must
avoid; unlike `theta_failure_measure_le`, it retains the Clean placement and environment needed by
the eventual bridge constructor. -/

/-- The union of the tuple-compression collision sets for an arbitrary finite family of enabled
lookup activations. -/
def enabledLookupThetaBadSetFamily
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp) : Finset Fp :=
  (Finset.univ : Finset ι).biUnion fun i =>
    (lookup i).thetaBadSet (place i) (env i)

/-- Avoiding the family union supplies the `θ` exclusion for every enabled activation. -/
theorem not_mem_enabledLookupThetaBadSetFamily_iff
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp) (theta : Fp) :
    theta ∉ enabledLookupThetaBadSetFamily place env lookup ↔
      ∀ i, theta ∉ (lookup i).thetaBadSet (place i) (env i) := by
  classical
  simp [enabledLookupThetaBadSetFamily]

/-- The family collision set costs the sum of `usableRows × tupleArity` over its activations. -/
theorem enabledLookupThetaBadSetFamily_card_le
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp)
    (hlength : ∀ i row, row < (env i).usableRows →
      ((lookup i).inputValues (place i) (env i)).length =
        ((lookup i).tableValues (env i) row).length) :
    (enabledLookupThetaBadSetFamily place env lookup).card ≤
      ∑ i : ι, (env i).usableRows *
        ((lookup i).inputValues (place i) (env i)).length := by
  classical
  rw [enabledLookupThetaBadSetFamily]
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun i _ =>
    (lookup i).thetaBadSet_card_le (place i) (env i)
      (fun row hrow => hlength i row hrow)

/-- Uniform `θ` hits some activation in a finite enabled-lookup family with probability at most
the sum of the individual row-by-arity budgets. -/
theorem uniformChallenge_enabledLookupThetaBadSetFamily
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp)
    (hlength : ∀ i row, row < (env i).usableRows →
      ((lookup i).inputValues (place i) (env i)).length =
        ((lookup i).tableValues (env i) row).length) :
    uniformChallenge.toOuterMeasure
        (enabledLookupThetaBadSetFamily place env lookup)
      ≤ (∑ i : ι, (env i).usableRows *
          ((lookup i).inputValues (place i) (env i)).length : ℕ) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast enabledLookupThetaBadSetFamily_card_le place env lookup hlength

/-! ## Bundle-wide resolver permutation challenge pricing

This section collects the finite bad sets needed to obtain `ResolverPermutationGoodChallenges`
simultaneously for every proof in a bundle, and bounds their uniform-challenge cost. -/

section ResolverPermutation

set_option maxHeartbeats 20000

/-- Both multisets used by a resolver permutation argument contain exactly one entry per
active chunk cell. -/
theorem card_chunkedCellPairs_eq_fintypeCard
    (nc m : ℕ) (width : ℕ → ℕ)
    (value name : ℕ → ℕ → ℕ → Fp) :
    Multiset.card (chunkedCellPairs nc m width value name) =
      Fintype.card (ChunkCell nc m width) := by
  simp [chunkedCellPairs]

/-- The finite `β` exclusion for one resolver-backed permutation argument.  There is one
coefficient root set for each potentially nonzero coefficient of `pairProdDiff`. -/
def resolverPermutationBetaBadSet
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) : Finset Fp :=
  (Finset.range (Fintype.card (ResolverPermutationCell vk poly p m) + 1)).biUnion fun j =>
    szBadSet (pairProdDiffCoeff
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)))
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen)) j)

/-- Avoiding the two per-proof bad sets supplies exactly the good-challenge record consumed by
the resolver permutation endpoint. -/
theorem ResolverPermutationGoodChallenges.ofBadSets
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ)
    (hgamma : ch.gamma ∉ resolverPermutationGammaBadSet vk ch poly p m)
    (hbeta : ch.beta ∉ resolverPermutationBetaBadSet vk poly p m) :
    ResolverPermutationGoodChallenges vk ch poly p m where
  gamma := hgamma
  beta j := by
    let source :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
    let target :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen)
    let d := Fintype.card (ResolverPermutationCell vk poly p m)
    change ch.beta ∉ szBadSet (pairProdDiffCoeff source target j)
    by_cases hj : j < d + 1
    · intro hmem
      apply hbeta
      rw [resolverPermutationBetaBadSet]
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hmem⟩
    · have hsource : Multiset.card source = d := by
        simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
      have htarget : Multiset.card target = d := by
        simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowName vk.omega vk.delta vk.chunkLen)
      have hzero : pairProdDiffCoeff source target j = 0 := by
        rw [toPoly_pairProdDiffCoeff]
        apply pairProdDiff_coeff_eq_zero_of_le
        simp only [hsource, htarget, max_self]
        omega
      rw [hzero]
      simp [szBadSet]

/-- The union of all resolver permutation `γ` exclusions in one proof bundle. -/
def allResolverPermutationGammaBadSet
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin numProofs)).biUnion fun p =>
    resolverPermutationGammaBadSet vk ch poly p m

/-- The union of all resolver permutation `β` exclusions in one proof bundle. -/
def allResolverPermutationBetaBadSet
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin numProofs)).biUnion fun p =>
    resolverPermutationBetaBadSet vk poly p m

/-- Bundle-wide permutation challenge exclusions at one active-row boundary.
This is the verifier-native package consumed by circuit integrations. -/
structure ResolverPermutationChallengeExclusions
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ) : Prop where
  gamma :
    ch.gamma ∉ allResolverPermutationGammaBadSet numProofs vk ch poly m
  beta :
    ch.beta ∉ allResolverPermutationBetaBadSet numProofs vk poly m

/-- Avoiding the bundle-wide permutation bad sets supplies the good-challenge record for every
proof. -/
theorem resolverPermutationGoodChallenges_of_not_mem
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ)
    (hgamma : ch.gamma ∉ allResolverPermutationGammaBadSet numProofs vk ch poly m)
    (hbeta : ch.beta ∉ allResolverPermutationBetaBadSet numProofs vk poly m) :
    ∀ p : Fin numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m := by
  intro p
  apply ResolverPermutationGoodChallenges.ofBadSets
  · intro hmem
    apply hgamma
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩
  · intro hmem
    apply hbeta
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩

/-- A bundle exclusion package supplies the per-proof record used by the
permutation semantic endpoint. -/
theorem ResolverPermutationChallengeExclusions.good
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    {vk : VerifyingKey shape Fp G} {ch : Challenges shape.k Fp}
    {poly : CommitmentId → CPoly} {m : ℕ}
    (exclusions :
      ResolverPermutationChallengeExclusions numProofs vk ch poly m) :
    ∀ p : Fin numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m :=
  resolverPermutationGoodChallenges_of_not_mem
    numProofs vk ch poly m exclusions.gamma exclusions.beta

/-- Compute one permutation good-challenge package using point evaluations and finite factor
checks.  Root sets occur only in the erased certificate; no root enumeration is performed. -/
def resolverPermutationGoodChallenges?
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    Option (PLift (ResolverPermutationGoodChallenges vk ch poly p m)) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using
      card_chunkedCellPairs_eq_fintypeCard shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using
      card_chunkedCellPairs_eq_fintypeCard shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen)
  match szBadSetAvoidance?
      (resolverPermutationGammaDifference vk ch poly p m) ch.gamma with
  | none => exact none
  | some hgammaRootProof =>
      if hfactor : ∀ cell : ResolverPermutationCell vk poly p m,
          chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
              cell.1 cell.2.1 cell.2.2 +
            ch.beta * chunkRowName vk.omega vk.delta vk.chunkLen
              cell.1 cell.2.1 cell.2.2 + ch.gamma ≠ 0 then
        match finForallOption (fun j : Fin (d + 1) =>
            szBadSetAvoidance? (pairProdDiffCoeff source target j.1) ch.beta) with
        | none => exact none
        | some hbetaProof =>
            exact some ⟨
              { gamma := by
                  intro hmem
                  rcases Finset.mem_union.mp hmem with hroot | hzero
                  · exact hgammaRootProof.down hroot
                  · obtain ⟨cell, hcell⟩ :=
                      (mem_resolverPermutationZeroFactorBadSet_iff
                        vk ch poly p m).mp hzero
                    exact hfactor cell hcell
                beta := fun j => by
                  by_cases hj : j < d + 1
                  · exact (hbetaProof ⟨j, hj⟩).down
                  ·
                    have hzero : pairProdDiffCoeff source target j = 0 := by
                      rw [toPoly_pairProdDiffCoeff]
                      apply pairProdDiff_coeff_eq_zero_of_le
                      simp only [hsource, htarget, max_self]
                      omega
                    exact not_mem_szBadSet.mpr fun hne => False.elim (hne hzero) }⟩
      else exact none

/-- Bundle-wide executable permutation exclusions, obtained by traversing every proof. -/
def resolverPermutationChallengeExclusions?
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ) :
    Option (PLift (ResolverPermutationChallengeExclusions numProofs vk ch poly m)) :=
  match finForallOption (fun p : Fin numProofs =>
      resolverPermutationGoodChallenges? vk ch poly p m) with
  | none => none
  | some good => some ⟨
      { gamma := by
          intro hmem
          obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hmem
          exact (good p).down.gamma hp
        beta := by
          intro hmem
          obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hmem
          rw [resolverPermutationBetaBadSet] at hp
          obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
          exact (good p).down.beta j hj }⟩

theorem resolverPermutationGoodChallenges?_isSome_of
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ)
    (hgood : ResolverPermutationGoodChallenges vk ch poly p m) :
    (resolverPermutationGoodChallenges? vk ch poly p m).isSome := by
  have hroot : ch.gamma ∉ szBadSet
      (resolverPermutationGammaDifference vk ch poly p m) := by
    intro hmem
    exact hgood.gamma (Finset.mem_union_left _ hmem)
  have hfactor : ∀ cell : ResolverPermutationCell vk poly p m,
      chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
          cell.1 cell.2.1 cell.2.2 +
        ch.beta * chunkRowName vk.omega vk.delta vk.chunkLen
          cell.1 cell.2.1 cell.2.2 + ch.gamma ≠ 0 := by
    intro cell hzero
    apply hgood.gamma
    exact Finset.mem_union_right _
      ((mem_resolverPermutationZeroFactorBadSet_iff vk ch poly p m).2 ⟨cell, hzero⟩)
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hbetaFinite : ∀ j : Fin (d + 1),
      (szBadSetAvoidance? (pairProdDiffCoeff source target j.1) ch.beta).isSome := by
    intro j
    have hsource : Multiset.card source = d := by
      simpa only [source, d] using
        card_chunkedCellPairs_eq_fintypeCard shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
    have htarget : Multiset.card target = d := by
      simpa only [target, d] using
        card_chunkedCellPairs_eq_fintypeCard shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowName vk.omega vk.delta vk.chunkLen)
    rw [szBadSetAvoidance?_isSome_iff]
    exact hgood.beta j.1
  obtain ⟨rootProof, hrootEq⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hroot)
  obtain ⟨betaProof, hbetaEq⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hbetaFinite)
  dsimp only [source, target, d] at hbetaEq
  simp only [resolverPermutationGoodChallenges?, hrootEq, hbetaEq]
  rw [dif_pos hfactor]
  rfl

theorem resolverPermutationChallengeExclusions?_isSome_of
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ)
    (hexclusions : ResolverPermutationChallengeExclusions numProofs vk ch poly m) :
    (resolverPermutationChallengeExclusions? numProofs vk ch poly m).isSome := by
  have hall : ∀ p : Fin numProofs,
      (resolverPermutationGoodChallenges? vk ch poly p m).isSome :=
    fun p => resolverPermutationGoodChallenges?_isSome_of vk ch poly p m
      (hexclusions.good p)
  obtain ⟨good, hgood⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hall)
  unfold resolverPermutationChallengeExclusions?
  generalize hresult : finForallOption (fun p : Fin numProofs =>
      resolverPermutationGoodChallenges? vk ch poly p m) = result at hgood ⊢
  cases result <;> simp_all

/-- One resolver permutation `γ` exclusion costs at most two challenge values per active
permutation cell: one for multiset recovery and one for source-factor nonvanishing. -/
theorem resolverPermutationGammaBadSet_card_le
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    (resolverPermutationGammaBadSet vk ch poly p m).card ≤
      2 * Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hroot :
      (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card ≤ d := by
    apply le_trans (szBadSet_linProdDiff_card_le _ _)
    simp [source, target, hsource, htarget]
  have hzero :
      (resolverPermutationZeroFactorBadSet vk ch poly p m).card ≤ d := by
    exact additiveZeroBadSet_card_le
      (resolverPermutationFactorOffset vk ch poly p m)
  rw [resolverPermutationGammaBadSet]
  calc
    (szBadSet (resolverPermutationGammaDifference vk ch poly p m) ∪
        resolverPermutationZeroFactorBadSet vk ch poly p m).card
      ≤ (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card +
          (resolverPermutationZeroFactorBadSet vk ch poly p m).card :=
        Finset.card_union_le _ _
    _ ≤ d + d := Nat.add_le_add hroot hzero
    _ = 2 * d := by omega

/-- One resolver permutation `β` exclusion costs at most `(d + 1)·d`, where `d` is the number
of active permutation cells. -/
theorem resolverPermutationBetaBadSet_card_le
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    (resolverPermutationBetaBadSet vk poly p m).card ≤
      (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
        Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hcoeff : ∀ j, (szBadSet (pairProdDiffCoeff source target j)).card ≤ d := by
    intro j
    refine le_trans (szBadSet_card_le _) ?_
    rw [toPoly_pairProdDiffCoeff]
    simpa [hsource, htarget] using natDegree_coeff_pairProdDiff_le source target j
  rw [resolverPermutationBetaBadSet]
  calc
    ((Finset.range (d + 1)).biUnion fun j =>
        szBadSet (pairProdDiffCoeff source target j)).card
      ≤ ∑ j ∈ Finset.range (d + 1),
          (szBadSet (pairProdDiffCoeff source target j)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (d + 1), d :=
      Finset.sum_le_sum fun j _ => hcoeff j
    _ = (d + 1) * d := by simp

/-- The bundle-wide permutation `γ` surface is bounded by the sum of the per-proof active-cell
budgets. -/
theorem uniformChallenge_allResolverPermutationGammaBadSet
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationGammaBadSet numProofs vk ch poly m)
      ≤ (∑ p : Fin numProofs,
          (2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationGammaBadSet]
  calc
    ((Finset.univ : Finset (Fin numProofs)).biUnion fun p =>
        resolverPermutationGammaBadSet vk ch poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin numProofs)),
          (resolverPermutationGammaBadSet vk ch poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin numProofs)),
          2 * Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationGammaBadSet_card_le vk ch poly p m
    _ = ∑ p : Fin numProofs,
          2 * Fintype.card (ResolverPermutationCell vk poly p m) := by simp

/-- The bundle-wide permutation `β` surface is bounded by the sum of the per-proof coefficient
budgets. -/
theorem uniformChallenge_allResolverPermutationBetaBadSet
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationBetaBadSet numProofs vk poly m)
      ≤ (∑ p : Fin numProofs,
          ((Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationBetaBadSet]
  calc
    ((Finset.univ : Finset (Fin numProofs)).biUnion fun p =>
        resolverPermutationBetaBadSet vk poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin numProofs)),
          (resolverPermutationBetaBadSet vk poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin numProofs)),
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationBetaBadSet_card_le vk poly p m
    _ = ∑ p : Fin numProofs,
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) := by simp

end ResolverPermutation

end Zcash.Snark
