import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import CompPoly.Bivariate.ToPoly
import Zcash.Snark.Soundness.Argument.GrandProduct
import Zcash.Snark.Soundness.Argument.RunningProduct
import Zcash.Snark.Soundness.Argument.Permutation
import Zcash.Snark.Soundness.Argument.PermutationConstruction
import Zcash.Snark.Soundness.Constraint.Constraints

/-!
# From the verifier's product check to the multiset identity

`GrandProduct` proves that a product of linear factors determines a multiset, but over
polynomials with `β` and `γ` as indeterminates. The verifier checks one field element instead:
that product at the two challenges it sampled. This module bridges the two, at one
Schwartz–Zippel step per challenge.

* `map_eq_of_prod_eval_eq` — a good `γ` turns the field identity into equality of the multisets
  of `value + β·name`.
* `multiset_pair_eq_of_map_eq` — a good `β` turns that into equality of the multisets of
  `(value, name)` pairs, through the nonzero `pairProdDiff` of `prod_pair_inj`.
* `multiset_pair_eq_of_prod_eval_eq` — the composition the permutation argument consumes.

Both bad sets are root sets of nonzero polynomials of degree at most the multiset sizes, so
`szBadSet_card_le` counts them exactly as for the vanishing check.

`pairProdDiff` and `lookupProdDiff` are bivariate, `γ` outer with coefficients in `β`: a `γ`
coefficient is an elementary symmetric function of the `β`-linear encodings (Vieta), zero above
the multiset size. Fixing `β` maps the coefficient ring by evaluation.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

/-- The difference of the two pair-encoded products, a polynomial in `γ` with coefficients in
`Fp[β]`.  The outer indeterminate is `γ`, the inner one `β`. -/
def pairProdDiff (sp tp : Multiset (Fp × Fp)) : CBiPoly :=
  (sp.map (fun p => X + C (encPair p : CPoly))).prod
    - (tp.map (fun p => X + C (encPair p : CPoly))).prod

/-- The `j`-th `γ` coefficient of the pair difference: an elementary symmetric polynomial in the
`β`-linear pair encodings on each side, zero above that side's multiset size. -/
def pairProdDiffCoeff (sp tp : Multiset (Fp × Fp)) (j : ℕ) : CPoly :=
  (if j ≤ Multiset.card sp then (sp.map encPair).esymm (Multiset.card sp - j) else 0)
    - (if j ≤ Multiset.card tp then (tp.map encPair).esymm (Multiset.card tp - j) else 0)

theorem toPoly_pairProdDiffCoeff (sp tp : Multiset (Fp × Fp)) (j : ℕ) :
    pairProdDiffCoeff sp tp j = CPolynomial.coeff (pairProdDiff sp tp) j := by
  have key : ∀ m : Multiset (Fp × Fp),
      CPolynomial.coeff ((m.map (fun p => (X + C (encPair p) : CBiPoly))).prod) j
        = if j ≤ Multiset.card m then (m.map encPair).esymm (Multiset.card m - j) else 0 := by
    intro m
    have hmap : m.map (fun p => (X + C (encPair p) : CBiPoly))
        = (m.map encPair).map (fun u => X + C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    split <;> rename_i hj
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C _ (by simpa using hj), Multiset.card_map]
    · exact CompPoly.CPolynomial.coeff_prod_X_add_C_eq_zero _ (by simpa using not_le.mp hj)
  rw [pairProdDiffCoeff, pairProdDiff, coeff_sub, key sp, key tp]

/-- The difference is nonzero whenever the multisets of pairs differ — this is `prod_pair_inj` read
contrapositively, and it is what makes the `β` bad set below a genuine root set. -/
theorem pairProdDiff_ne_zero {sp tp : Multiset (Fp × Fp)} (h : sp ≠ tp) :
    pairProdDiff sp tp ≠ 0 :=
  fun h0 => h (prod_cpair_inj (sub_eq_zero.mp h0))

/-- The difference of the two `γ`-products once `β` is fixed. -/
def linProdDiff (s t : Multiset Fp) : CPoly :=
  (s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod

/-- **The `γ` step.** A challenge outside the difference's roots turns the verifier's field product
identity into equality of the multisets of `value + β·name`. -/
theorem map_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β) := by
  set s := sp.map (fun p => p.1 + p.2 * β) with hs
  set t := tp.map (fun p => p.1 + p.2 * β) with ht
  by_contra hne
  have hD : linProdDiff s t ≠ 0 := fun h0 =>
    hne (prod_cX_add_u_inj (sub_eq_zero.mp h0))
  refine (not_mem_szBadSet.mp hgoodγ) hD ?_
  have hsv : (s.map (fun x => γ + x)).prod = (t.map (fun x => γ + x)).prod := by
    simpa [hs, ht, Multiset.map_map, Function.comp_def] using h
  rw [linProdDiff, eval_sub, eval_cprod_X_add_u s γ, eval_cprod_X_add_u t γ, hsv, sub_self]

/-- **The `β` step.** A challenge outside the roots of every coefficient of `pairProdDiff` turns
equality of the `value + β·name` multisets into equality of the `(value, name)` pairs. -/
theorem multiset_pair_eq_of_map_eq {sp tp : Multiset (Fp × Fp)} {β : Fp}
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff sp tp j))
    (h : sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β)) :
    sp = tp := by
  by_contra hne
  have hD : pairProdDiff sp tp ≠ 0 := pairProdDiff_ne_zero hne
  obtain ⟨j, hj⟩ : ∃ j, CPolynomial.coeff (pairProdDiff sp tp) j ≠ 0 := by
    by_contra hall
    exact hD (ext_coeff fun j => by simpa using not_exists.mp hall j)
  have hjC : pairProdDiffCoeff sp tp j ≠ 0 := by
    rw [toPoly_pairProdDiffCoeff]
    exact hj
  refine (not_mem_szBadSet.mp (hgoodβ j)) hjC ?_
  -- Fixing `β` is a coefficient map, and it kills the difference: both sides become the same
  -- product of linear factors once the `value + β·name` multisets agree.
  have hmapped : CompPoly.CPolynomial.map (evalRingHom β) (pairProdDiff sp tp) = 0 := by
    have hconv : ∀ m : Multiset (Fp × Fp),
        CompPoly.CPolynomial.map (evalRingHom β)
            ((m.map (fun p => (X + C (encPair p) : CBiPoly))).prod)
          = ((m.map (fun p => p.1 + p.2 * β)).map (fun u => X + C u)).prod := by
      intro m
      rw [CompPoly.CPolynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => ?_)
      rw [Function.comp_apply, Function.comp_apply, CompPoly.CPolynomial.map_add,
        CompPoly.CPolynomial.map_X, CompPoly.CPolynomial.map_C, coe_evalRingHom, encPair,
        eval_add, eval_C, eval_mul, eval_C, eval_X]
    rw [pairProdDiff, CompPoly.CPolynomial.map_sub, hconv sp, hconv tp, h, sub_self]
  have hcoeff : CPolynomial.coeff (CompPoly.CPolynomial.map (evalRingHom β) (pairProdDiff sp tp)) j
      = CPolynomial.coeff (0 : CPoly) j := by rw [hmapped]
  rw [CompPoly.CPolynomial.coeff_map, coe_evalRingHom, coeff_zero] at hcoeff
  rw [toPoly_pairProdDiffCoeff]
  exact hcoeff

/-- **The bridge.** The verifier's product identity at the sampled challenges gives the multiset of
`(value, name)` pairs, provided both challenges avoid their bad sets. This is what the permutation
argument feeds to `perm_copy_constraints`. -/
theorem multiset_pair_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff sp tp j))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp = tp :=
  multiset_pair_eq_of_map_eq hgoodβ (map_eq_of_prod_eval_eq hgoodγ h)

/-- The `γ` bad set is small: at most the larger multiset's size. -/
theorem szBadSet_linProdDiff_card_le (s t : Multiset Fp) :
    (szBadSet (linProdDiff s t)).card ≤ max (Multiset.card s) (Multiset.card t) := by
  refine (szBadSet_card_le _).trans ?_
  rw [linProdDiff]
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_cprod_X_add_u s, natDegree_cprod_X_add_u t]

/-! ## The lookup argument's product

The lookup factors are `(input + β)·(table + γ)` with the two challenges on *separate* columns, not
`value + β·name + γ`. So the product splits into two independent univariate products, and the
kernel applies twice rather than through `encPair`. The `γ`-leading coefficient of the difference is
the difference of the two `β`-products, which is what separates the input columns from the table
columns. -/

/-- The difference of the two lookup products, in `γ` over `Fp[β]`. The input columns enter as
constants in `γ`; the table columns as the linear factors. -/
def lookupProdDiff (a s inp tbl : Multiset Fp) : CBiPoly :=
  C (a.map (fun u => X + C u)).prod * (s.map (fun u => X + C (C u))).prod
    - C (inp.map (fun u => X + C u)).prod * (tbl.map (fun u => X + C (C u))).prod

/-- A `γ` coefficient of the lookup difference, without constructing a nested polynomial. -/
def lookupProdDiffCoeff (a s inp tbl : Multiset Fp) (j : ℕ) : CPoly :=
  (a.map (fun u => X + C u)).prod
      * (if j ≤ Multiset.card s then (s.map C).esymm (Multiset.card s - j) else 0)
    - (inp.map (fun u => X + C u)).prod
      * (if j ≤ Multiset.card tbl then (tbl.map C).esymm (Multiset.card tbl - j) else 0)

theorem toPoly_lookupProdDiffCoeff (a s inp tbl : Multiset Fp) (j : ℕ) :
    lookupProdDiffCoeff a s inp tbl j
      = CPolynomial.coeff (lookupProdDiff a s inp tbl) j := by
  have key : ∀ m : Multiset Fp,
      CPolynomial.coeff ((m.map (fun u => (X + C (C u) : CBiPoly))).prod) j
        = if j ≤ Multiset.card m then (m.map C).esymm (Multiset.card m - j) else 0 := by
    intro m
    have hmap : m.map (fun u => (X + C (C u) : CBiPoly))
        = (m.map C).map (fun u => X + C u) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    split <;> rename_i hj
    · rw [CompPoly.CPolynomial.coeff_prod_X_add_C _ (by simpa using hj), Multiset.card_map]
    · exact CompPoly.CPolynomial.coeff_prod_X_add_C_eq_zero _ (by simpa using not_le.mp hj)
  rw [lookupProdDiffCoeff, lookupProdDiff, coeff_sub, coeff_C_mul, coeff_C_mul, key s, key tbl]

/-- The lookup difference after fixing `β`, as a polynomial in `γ`. -/
def lookupProdDiffGamma (a s inp tbl : Multiset Fp) (beta : Fp) : CPoly :=
  C (eval beta (a.map (fun u => X + C u)).prod) * (s.map (fun u => X + C u)).prod
    - C (eval beta (inp.map (fun u => X + C u)).prod) * (tbl.map (fun u => X + C u)).prod

/-- Fixing `β` is exactly mapping the coefficient ring by evaluation at `β`. -/
theorem lookupProdDiffGamma_eq_map (a s inp tbl : Multiset Fp) (beta : Fp) :
    lookupProdDiffGamma a s inp tbl beta
      = CompPoly.CPolynomial.map (evalRingHom beta) (lookupProdDiff a s inp tbl) := by
  have hprod : ∀ m : Multiset Fp,
      CompPoly.CPolynomial.map (evalRingHom beta) ((m.map (fun u => (X + C (C u) : CBiPoly))).prod)
        = (m.map (fun u => X + C u)).prod := by
    intro m
    rw [CompPoly.CPolynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => ?_)
    rw [Function.comp_apply, CompPoly.CPolynomial.map_add, CompPoly.CPolynomial.map_X,
      CompPoly.CPolynomial.map_C, coe_evalRingHom, eval_C]
  rw [lookupProdDiffGamma, lookupProdDiff, CompPoly.CPolynomial.map_sub,
    CompPoly.CPolynomial.map_mul, CompPoly.CPolynomial.map_mul, CompPoly.CPolynomial.map_C,
    CompPoly.CPolynomial.map_C, hprod s, hprod tbl, coe_evalRingHom]

/-- Evaluating the lookup difference at the sampled challenges is the verifier's own product
comparison. -/
theorem eval_lookupProdDiff (a s inp tbl : Multiset Fp) (β γ : Fp) :
    eval γ (lookupProdDiffGamma a s inp tbl β)
      = (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
        - (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod := by
  rw [lookupProdDiffGamma]
  simp only [eval_sub, eval_mul, eval_C]
  rw [eval_cprod_X_add_u a β, eval_cprod_X_add_u inp β, eval_cprod_X_add_u s γ,
    eval_cprod_X_add_u tbl γ]

/-- **The lookup product's multiset content.** With both challenges outside their bad sets, the
verifier's field product identity forces the input columns and the table columns to match as
multisets, separately. -/
theorem lookup_multisets_of_prod_eval_eq {a s inp tbl : Multiset Fp} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (lookupProdDiffGamma a s inp tbl β))
    (hgoodβ : ∀ j, β ∉ szBadSet (lookupProdDiffCoeff a s inp tbl j))
    (h : (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
       = (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod) :
    lookupProdDiff a s inp tbl = 0 := by
  have hev : eval γ (lookupProdDiffGamma a s inp tbl β) = 0 := by
    rw [eval_lookupProdDiff, h, sub_self]
  have hmap : CompPoly.CPolynomial.map (evalRingHom β) (lookupProdDiff a s inp tbl) = 0 := by
    by_contra hne
    refine (not_mem_szBadSet.mp hgoodγ) ?_ hev
    rwa [Ne, lookupProdDiffGamma_eq_map]
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, CPolynomial.coeff (lookupProdDiff a s inp tbl) j ≠ 0 := by
    by_contra hall
    exact hne (ext_coeff fun j => by simpa using not_exists.mp hall j)
  have hjC : lookupProdDiffCoeff a s inp tbl j ≠ 0 := by
    rw [toPoly_lookupProdDiffCoeff]
    exact hj
  refine (not_mem_szBadSet.mp (hgoodβ j)) hjC ?_
  have hcoeff : CPolynomial.coeff
      (CompPoly.CPolynomial.map (evalRingHom β) (lookupProdDiff a s inp tbl)) j
      = CPolynomial.coeff (0 : CPoly) j := by rw [hmap]
  rw [CompPoly.CPolynomial.coeff_map, coe_evalRingHom, coeff_zero] at hcoeff
  rw [toPoly_lookupProdDiffCoeff]
  exact hcoeff

/-- **The lookup product separates the columns.** The `γ`-leading coefficient of each side is that
side's `β`-product, so the difference vanishing forces the input columns to match and then, after
cancelling, the table columns. -/
theorem lookup_multisets_of_diff_eq_zero {a s inp tbl : Multiset Fp}
    (h : lookupProdDiff a s inp tbl = 0) : a = inp ∧ s = tbl :=
  prod_split_inj (sub_eq_zero.mp (by rwa [lookupProdDiff] at h))

/-! ## The permutation argument, from the row recurrence to the copy constraints

Composing the two halves. `RunningProduct` turns the verifier's per-row recurrence into a product
over every cell; the bridge above turns that product into the multiset of `(value, name)` pairs;
`Soundness.Permutation.perm_copy_constraints` turns the multiset into the copy constraints. One
branch survives all the way: a vanishing factor, meaning the running product ended at zero or a
`value + β·name + γ` collided. It stays in the conclusion rather than being assumed away. -/

/-- The `(value, name)` pair of every cell of an `m × k` table. -/
def cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (Fin m × Fin k)).val.map
    (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))

/-- A cell of a variable-width chunked table: a chunk, a row, and a column valid for that chunk. -/
abbrev ChunkCell (nc m : ℕ) (width : ℕ → ℕ) :=
  Σ c : Fin nc, Fin m × Fin (width c)

/-- The `(value, name)` pair of every cell across a variable-width chunked table. -/
def chunkedCellPairs (nc m : ℕ) (width : ℕ → ℕ)
    (value nm : ℕ → ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (ChunkCell nc m width)).val.map
    (fun c => (value c.1 c.2.1 c.2.2, nm c.1 c.2.1 c.2.2))

open Finset in
/-- A product over the cell pairs is the row-by-row product the telescoping produces. -/
theorem prod_map_cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) (f : Fp × Fp → Fp) :
    ((cellPairs m k value nm).map f).prod
      = ∏ i ∈ range m, ∏ j ∈ range k, f (value i j, nm i j) := by
  rw [cellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fintype.prod_prod_type]
  simp only [Function.comp_apply]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range k, f (value i j, nm i j)) m]
  exact prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range
    (fun j => f (value (i : ℕ) j, nm (i : ℕ) j)) k

open Finset in
/-- A product over variable-width chunked cells is the chunk-by-row product used by stitching. -/
theorem prod_map_chunkedCellPairs (nc m : ℕ) (width : ℕ → ℕ)
    (value nm : ℕ → ℕ → ℕ → Fp) (f : Fp × Fp → Fp) :
    ((chunkedCellPairs nc m width value nm).map f).prod
      = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          f (value c i j, nm c i j) := by
  rw [chunkedCellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fintype.prod_sigma]
  simp only [Function.comp_apply]
  simp_rw [Fintype.prod_prod_type]
  rw [Fin.prod_univ_eq_prod_range
    (fun c => ∏ i : Fin m, ∏ j : Fin (width c),
      f (value c i j, nm c i j)) nc]
  refine prod_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_eq_prod_range
    (fun i => ∏ j : Fin (width c), f (value c i j, nm c i j)) m]
  refine prod_congr rfl fun i _ => ?_
  exact Fin.prod_univ_eq_prod_range
    (fun j => f (value c i j, nm c i j)) (width c)

open Finset in
/-- **The permutation argument's multiset identity.** The verifier's per-row recurrence on the
running product, with the boundary values it also checks, gives equality of the `(value, name)`
multisets — *either* that, *or* one of the identity-side factors vanished. -/
theorem cellPairs_eq_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp)
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j)) :
    cellPairs m k value sigmaName = cellPairs m k value nm
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases grandProduct_eq_or_cell_eq_zero z
      (fun i j => value i j + β * nm i j + γ) (fun i j => value i j + β * sigmaName i j + γ)
      hrec hz0 hzm with hprod | hzero
  · refine Or.inl (multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ ?_)
    rw [prod_map_cellPairs, prod_map_cellPairs]
    rw [← prod_range_prod_range (fun i j => value i j + β * sigmaName i j + γ),
      ← prod_range_prod_range (fun i j => value i j + β * nm i j + γ)] at hprod
    calc ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + sigmaName i j * β))
        = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * sigmaName i j + γ) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * nm i j + γ) := hprod
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + nm i j * β)) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
  · exact Or.inr hzero

open Finset in
/-- **The variable-width permutation multiset identity.** Per-chunk row recurrences and the
inter-chunk running-product chain give equality of the `(value, name)` multisets over the complete
chunked table, or expose an identity-side factor that vanished. -/
theorem chunkedCellPairs_eq_of_running_product {nc m : ℕ} (width : ℕ → ℕ)
    (Z : ℕ → ℕ → Fp) (value nm sigmaName : ℕ → ℕ → ℕ → Fp) (β γ : Fp)
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range (width c),
          (value c i j + β * sigmaName c i j + γ)
        = Z c i * ∏ j ∈ range (width c), (value c i j + β * nm c i j + γ))
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m)
    (hz0 : Z 0 0 = 1) (hzend : Z nc 0 = 0 ∨ Z nc 0 = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((chunkedCellPairs nc m width value sigmaName).map (fun p => p.1 + p.2 * β))
      ((chunkedCellPairs nc m width value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff (chunkedCellPairs nc m width value sigmaName) (chunkedCellPairs nc m width value nm) j)) :
    chunkedCellPairs nc m width value sigmaName = chunkedCellPairs nc m width value nm
      ∨ ∃ c ∈ range nc, ∃ i ∈ range m, ∃ j ∈ range (width c),
          value c i j + β * nm c i j + γ = 0 := by
  rcases chunkedGrandProduct_eq_or_cell_eq_zero Z
      (fun c i j => value c i j + β * nm c i j + γ)
      (fun c i j => value c i j + β * sigmaName c i j + γ)
      width hrec hchain hz0 hzend with hprod | hzero
  · refine Or.inl (multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ ?_)
    rw [prod_map_chunkedCellPairs, prod_map_chunkedCellPairs]
    calc
      ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          (γ + (value c i j + sigmaName c i j * β))
          = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
              (value c i j + β * sigmaName c i j + γ) := by
                exact prod_congr rfl fun c _ => prod_congr rfl fun i _ =>
                  prod_congr rfl fun j _ => by ring
      _ = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
              (value c i j + β * nm c i j + γ) := hprod
      _ = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          (γ + (value c i j + nm c i j * β)) := by
            exact prod_congr rfl fun c _ => prod_congr rfl fun i _ =>
              prod_congr rfl fun j _ => by ring
  · exact Or.inr hzero

open Finset in
/-- **The copy constraints, from the verifier's checks.** Cells in the same cycle of `σ` hold equal
values. `hσ` says the left-hand names are the `σ`-relabelled ones, `hnm` is the name distinctness the
keygen provides, and the surviving branch is a vanishing factor. This is the permutation argument's
soundness statement with the product step supplied rather than assumed. -/
theorem perm_copy_constraints_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp) (σ : Equiv.Perm (Fin m × Fin k))
    (hσ : ∀ c : Fin m × Fin k,
      sigmaName (c.1 : ℕ) (c.2 : ℕ) = nm ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin m × Fin k => nm (c.1 : ℕ) (c.2 : ℕ))
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j))
    {c d : Fin m × Fin k} (hcd : σ.SameCycle c d) :
    value (c.1 : ℕ) (c.2 : ℕ) = value (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases cellPairs_eq_of_running_product z value nm sigmaName β γ hrec hz0 hzm hgoodγ hgoodβ with
    hmulti | hzero
  · have hmulti' : cellPairs m k value nm = cellPairs m k value sigmaName := hmulti.symm
    simp only [cellPairs] at hmulti'
    refine Or.inl (perm_copy_constraints σ hnm (fun c => value (c.1 : ℕ) (c.2 : ℕ)) ?_ hcd)
    calc (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))
        = (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), sigmaName (c.1 : ℕ) (c.2 : ℕ))) := hmulti'
      _ = _ := Multiset.map_congr rfl fun c _ => by rw [hσ c]
  · exact Or.inr hzero

open Finset in
/-- **Global copy constraints across variable-width chunks.** Unlike the single-chunk wrapper, this
uses the verifier's chain between running products and one permutation over all chunked cells, so
cycles may cross chunk boundaries. -/
theorem perm_copy_constraints_of_chunked_running_product {nc m : ℕ} (width : ℕ → ℕ)
    (Z : ℕ → ℕ → Fp) (value nm sigmaName : ℕ → ℕ → ℕ → Fp) (β γ : Fp)
    (σ : Equiv.Perm (ChunkCell nc m width))
    (hσ : ∀ c : ChunkCell nc m width,
      sigmaName c.1 c.2.1 c.2.2 = nm (σ c).1 (σ c).2.1 (σ c).2.2)
    (hnm : Function.Injective fun c : ChunkCell nc m width => nm c.1 c.2.1 c.2.2)
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range (width c),
          (value c i j + β * sigmaName c i j + γ)
        = Z c i * ∏ j ∈ range (width c), (value c i j + β * nm c i j + γ))
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m)
    (hz0 : Z 0 0 = 1) (hzend : Z nc 0 = 0 ∨ Z nc 0 = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((chunkedCellPairs nc m width value sigmaName).map (fun p => p.1 + p.2 * β))
      ((chunkedCellPairs nc m width value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff (chunkedCellPairs nc m width value sigmaName) (chunkedCellPairs nc m width value nm) j))
    {c d : ChunkCell nc m width} (hcd : σ.SameCycle c d) :
    value c.1 c.2.1 c.2.2 = value d.1 d.2.1 d.2.2
      ∨ ∃ c ∈ range nc, ∃ i ∈ range m, ∃ j ∈ range (width c),
          value c i j + β * nm c i j + γ = 0 := by
  rcases chunkedCellPairs_eq_of_running_product width Z value nm sigmaName β γ
      hrec hchain hz0 hzend hgoodγ hgoodβ with hmulti | hzero
  · have hmulti' : chunkedCellPairs nc m width value nm
        = chunkedCellPairs nc m width value sigmaName := hmulti.symm
    simp only [chunkedCellPairs] at hmulti'
    refine Or.inl (perm_copy_constraints σ hnm
      (fun c => value c.1 c.2.1 c.2.2) ?_ hcd)
    calc
      (Finset.univ : Finset (ChunkCell nc m width)).val.map
          (fun c => (value c.1 c.2.1 c.2.2, nm c.1 c.2.1 c.2.2))
        = (Finset.univ : Finset (ChunkCell nc m width)).val.map
          (fun c => (value c.1 c.2.1 c.2.2, sigmaName c.1 c.2.1 c.2.2)) := hmulti'
      _ = _ := Multiset.map_congr rfl fun c _ => by rw [hσ c]
  · exact Or.inr hzero


open Finset in
/-- **The circuit's declared equalities are enforced.** The same chain with the permutation taken to
be the one the keygen builds from the circuit's copy constraints: by `build_correct` its cycles are
exactly the classes those constraints force, so the conclusion is about the circuit's own declared
equalities rather than about an arbitrary permutation. -/
theorem declared_equalities_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp)
    (cs : List ((Fin m × Fin k) × (Fin m × Fin k)))
    (hσ : ∀ c : Fin m × Fin k, sigmaName (c.1 : ℕ) (c.2 : ℕ)
      = nm ((PermConstruction.build cs c).1 : ℕ) ((PermConstruction.build cs c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin m × Fin k => nm (c.1 : ℕ) (c.2 : ℕ))
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j))
    {x y : Fin m × Fin k} (hxy : Relation.EqvGen (fun u v => (u, v) ∈ cs) x y) :
    value (x.1 : ℕ) (x.2 : ℕ) = value (y.1 : ℕ) (y.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 :=
  perm_copy_constraints_of_running_product z value nm sigmaName β γ (PermConstruction.build cs)
    hσ hnm hrec hz0 hzm hgoodγ hgoodβ ((PermConstruction.build_correct cs x y).mpr hxy)

end Zcash.Snark
