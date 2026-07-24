import Mathlib
import Zcash.Snark.Soundness.GrandProduct
import Zcash.Snark.Soundness.RunningProduct
import Zcash.Snark.Soundness.Permutation
import Zcash.Snark.Soundness.PermutationConstruction
import Zcash.Snark.Soundness.Constraints

/-!
# From the verifier's product check to the multiset identity

`GrandProduct` proves that a product of linear factors determines a multiset — but over polynomials,
with `β` and `γ` as indeterminates. The verifier does not check a polynomial identity. It checks one
field element, the product evaluated at the two challenges it actually sampled.

This module is that bridge, and it costs two Schwartz–Zippel steps, one per challenge:

* `map_eq_of_prod_eval_eq` — a good `γ` turns the field product identity into equality of the
  multisets of `value + β·name`. The bad set is the roots of the difference in `γ`.
* `multiset_pair_eq_of_map_eq` — a good `β` turns that into equality of the multisets of
  `(value, name)` *pairs*. The bad set is the roots of one coefficient of `pairProdDiff`, the
  difference `prod_pair_inj` shows is nonzero whenever the pairs differ.
* `multiset_pair_eq_of_prod_eval_eq` — the two composed, which is what the permutation argument
  consumes: a product identity at the sampled challenges gives the multiset of pairs that
  `perm_copy_constraints` turns into the copy constraints.

Both bad sets are root sets of nonzero polynomials of degree at most the multiset sizes, so each is
counted by `szBadSet_card_le` exactly like the vanishing check's.
-/

namespace Zcash.Snark

open Polynomial

/-- The difference of the two pair-encoded products, a polynomial in `γ` with coefficients in
`Fp[β]`. -/
noncomputable def pairProdDiff (sp tp : Multiset (Fp × Fp)) : Polynomial (Polynomial Fp) :=
  (sp.map (fun p => X + C (encPair p))).prod - (tp.map (fun p => X + C (encPair p))).prod

/-- The difference is nonzero whenever the multisets of pairs differ — this is `prod_pair_inj` read
contrapositively, and it is what makes the `β` bad set below a genuine root set. -/
theorem pairProdDiff_ne_zero {sp tp : Multiset (Fp × Fp)} (h : sp ≠ tp) :
    pairProdDiff sp tp ≠ 0 :=
  fun h0 => h (prod_pair_inj (sub_eq_zero.mp h0))

/-- The difference of the two `γ`-products once `β` is fixed. -/
noncomputable def linProdDiff (s t : Multiset Fp) : Polynomial Fp :=
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
  have hD : linProdDiff s t ≠ 0 := fun h0 => hne (prod_X_add_u_inj (sub_eq_zero.mp h0))
  refine (not_mem_szBadSet.mp hgoodγ) hD ?_
  have hsv : (s.map (fun x => γ + x)).prod = (t.map (fun x => γ + x)).prod := by
    simpa [hs, ht, Multiset.map_map, Function.comp_def] using h
  rw [linProdDiff, eval_sub, eval_prod_X_add_u s γ, eval_prod_X_add_u t γ, hsv, sub_self]

/-- **The `β` step.** A challenge outside the roots of every coefficient of `pairProdDiff` turns
equality of the `value + β·name` multisets into equality of the `(value, name)` pairs. -/
theorem multiset_pair_eq_of_map_eq {sp tp : Multiset (Fp × Fp)} {β : Fp}
    (hgoodβ : ∀ j, β ∉ szBadSet ((pairProdDiff sp tp).coeff j))
    (h : sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β)) :
    sp = tp := by
  by_contra hne
  have hD : pairProdDiff sp tp ≠ 0 := pairProdDiff_ne_zero hne
  obtain ⟨j, hj⟩ : ∃ j, (pairProdDiff sp tp).coeff j ≠ 0 := by
    by_contra hall
    exact hD (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  refine (not_mem_szBadSet.mp (hgoodβ j)) hj ?_
  -- mapping `β` through the coefficients kills the whole difference, hence every coefficient
  have hmapped : (pairProdDiff sp tp).map (evalRingHom β) = 0 := by
    have hconv : ∀ m : Multiset (Fp × Fp),
        ((m.map (fun p => X + C (encPair p))).prod).map (evalRingHom β)
          = ((m.map (fun p => p.1 + p.2 * β)).map (fun u => X + C u)).prod := by
      intro m
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => ?_)
      simp [encPair, Polynomial.map_add, Polynomial.map_mul]
    rw [pairProdDiff, Polynomial.map_sub, hconv sp, hconv tp, h, sub_self]
  have := congrArg (fun q => Polynomial.coeff q j) hmapped
  simpa [Polynomial.coeff_map] using this

/-- **The bridge.** The verifier's product identity at the sampled challenges gives the multiset of
`(value, name)` pairs, provided both challenges avoid their bad sets. This is what the permutation
argument feeds to `perm_copy_constraints`. -/
theorem multiset_pair_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet ((pairProdDiff sp tp).coeff j))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp = tp :=
  multiset_pair_eq_of_map_eq hgoodβ (map_eq_of_prod_eval_eq hgoodγ h)

/-- The `γ` bad set is small: at most the larger multiset's size. -/
theorem szBadSet_linProdDiff_card_le (s t : Multiset Fp) :
    (szBadSet (linProdDiff s t)).card ≤ max (Multiset.card s) (Multiset.card t) := by
  refine (szBadSet_card_le _).trans ?_
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_prod_X_add_u s, natDegree_prod_X_add_u t]



/-! ## The lookup argument's product

The lookup factors are `(input + β)·(table + γ)` with the two challenges on *separate* columns, not
`value + β·name + γ`. So the product splits into two independent univariate products, and the
kernel applies twice rather than through `encPair`. The `γ`-leading coefficient of the difference is
the difference of the two `β`-products, which is what separates the input columns from the table
columns. -/

/-- The difference of the two lookup products, in `γ` over `Fp[β]`. The input columns enter as
constants in `γ`; the table columns as the linear factors. -/
noncomputable def lookupProdDiff (a s inp tbl : Multiset Fp) : Polynomial (Polynomial Fp) :=
  C (a.map (fun u => X + C u)).prod * (s.map (fun u => X + C (C u))).prod
    - C (inp.map (fun u => X + C u)).prod * (tbl.map (fun u => X + C (C u))).prod

/-- Evaluating the lookup difference at the sampled challenges is the verifier's own product
comparison. -/
theorem eval_lookupProdDiff (a s inp tbl : Multiset Fp) (β γ : Fp) :
    ((lookupProdDiff a s inp tbl).map (evalRingHom β)).eval γ
      = (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
        - (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod := by
  have hconv : ∀ m : Multiset Fp,
      ((m.map (fun u => X + C (C u))).prod).map (evalRingHom β)
        = (m.map (fun u => X + C u)).prod := by
    intro m
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => ?_)
    simp [Polynomial.map_add]
  rw [lookupProdDiff, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    hconv s, hconv tbl, map_C, map_C]
  simp only [eval_sub, eval_mul, eval_C, coe_evalRingHom]
  rw [eval_prod_X_add_u a β, eval_prod_X_add_u inp β, eval_prod_X_add_u s γ,
    eval_prod_X_add_u tbl γ]

/-- **The lookup product's multiset content.** With both challenges outside their bad sets, the
verifier's field product identity forces the input columns and the table columns to match as
multisets, separately. -/
theorem lookup_multisets_of_prod_eval_eq {a s inp tbl : Multiset Fp} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet ((lookupProdDiff a s inp tbl).map (evalRingHom β)))
    (hgoodβ : ∀ j, β ∉ szBadSet ((lookupProdDiff a s inp tbl).coeff j))
    (h : (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
       = (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod) :
    lookupProdDiff a s inp tbl = 0 := by
  -- the sampled challenges kill the difference, so the `β`-reduction is zero …
  have hev : ((lookupProdDiff a s inp tbl).map (evalRingHom β)).eval γ = 0 := by
    rw [eval_lookupProdDiff, h, sub_self]
  have hmap : (lookupProdDiff a s inp tbl).map (evalRingHom β) = 0 := by
    by_contra hne
    exact (not_mem_szBadSet.mp hgoodγ) hne hev
  -- … and then every coefficient is, so the difference itself is
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, (lookupProdDiff a s inp tbl).coeff j ≠ 0 := by
    by_contra hall
    exact hne (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  refine (not_mem_szBadSet.mp (hgoodβ j)) hj ?_
  have := congrArg (fun q => Polynomial.coeff q j) hmap
  simpa [Polynomial.coeff_map] using this

/-- **The lookup product separates the columns.** The `γ`-leading coefficient of each side is that
side's `β`-product, so the difference vanishing forces the input columns to match and then, after
cancelling, the table columns. -/
theorem lookup_multisets_of_diff_eq_zero {a s inp tbl : Multiset Fp}
    (h : lookupProdDiff a s inp tbl = 0) : a = inp ∧ s = tbl := by
  have hmonic : ∀ m : Multiset Fp, (m.map (fun u => X + C (C u))).prod.Monic := fun m =>
    monic_multiset_prod_of_monic _ _ fun u _ => monic_X_add_C _
  have hne : ∀ m : Multiset Fp, (m.map (fun u => X + C u)).prod ≠ 0 := fun m =>
    (monic_multiset_prod_of_monic _ _ fun u _ => monic_X_add_C u).ne_zero
  have heq : C (a.map (fun u => X + C u)).prod * (s.map (fun u => X + C (C u))).prod
      = C (inp.map (fun u => X + C u)).prod * (tbl.map (fun u => X + C (C u))).prod :=
    sub_eq_zero.mp h
  -- the leading coefficient in `γ` is the `β`-product on each side
  have hlead := congrArg Polynomial.leadingCoeff heq
  rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
    (hmonic s).leadingCoeff, (hmonic tbl).leadingCoeff, mul_one, mul_one] at hlead
  refine ⟨prod_X_add_u_inj hlead, ?_⟩
  -- cancel the common `β`-product and read off the table columns
  rw [hlead] at heq
  have hCne : (C (inp.map (fun u => X + C u)).prod : Polynomial (Polynomial Fp)) ≠ 0 := by
    simpa using hne inp
  have hQ := mul_left_cancel₀ hCne heq
  have hmap : (s.map C).map (fun v => X + C v) = s.map (fun u => X + C (C u)) := by
    simp [Multiset.map_map]
  have hmapt : (tbl.map C).map (fun v => X + C v) = tbl.map (fun u => X + C (C u)) := by
    simp [Multiset.map_map]
  have hstep : (((s.map C)).map (fun v => X + C v)).prod
      = (((tbl.map C)).map (fun v => X + C v)).prod := by rw [hmap, hmapt]; exact hQ
  exact Multiset.map_injective (C_injective (R := Fp)) (prod_X_add_u_inj hstep)

/-! ## The permutation argument, from the row recurrence to the copy constraints

Composing the two halves. `RunningProduct` turns the verifier's per-row recurrence into a product
over every cell; the bridge above turns that product into the multiset of `(value, name)` pairs;
`Soundness.Permutation.perm_copy_constraints` turns the multiset into the copy constraints. One
branch survives all the way: a vanishing factor, meaning the running product ended at zero or a
`value + β·name + γ` collided. It stays in the conclusion rather than being assumed away. -/

/-- The `(value, name)` pair of every cell of an `m × k` table. -/
noncomputable def cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (Fin m × Fin k)).val.map
    (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))

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
      ((pairProdDiff (cellPairs m k value sigmaName) (cellPairs m k value nm)).coeff j)) :
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
      ((pairProdDiff (cellPairs m k value sigmaName) (cellPairs m k value nm)).coeff j))
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
      ((pairProdDiff (cellPairs m k value sigmaName) (cellPairs m k value nm)).coeff j))
    {x y : Fin m × Fin k} (hxy : Relation.EqvGen (fun u v => (u, v) ∈ cs) x y) :
    value (x.1 : ℕ) (x.2 : ℕ) = value (y.1 : ℕ) (y.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 :=
  perm_copy_constraints_of_running_product z value nm sigmaName β γ (PermConstruction.build cs)
    hσ hnm hrec hz0 hzm hgoodγ hgoodβ ((PermConstruction.build_correct cs x y).mpr hxy)

end Zcash.Snark
