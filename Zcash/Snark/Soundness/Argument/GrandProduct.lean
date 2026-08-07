import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import CompPoly.Univariate.ToPoly
import Zcash.Common.CPolynomial

/-!
# The grand-product-to-multiset kernel (permutation & lookup soundness)

Both halo2 arguments enforce their relation by a **grand product of factors linear in the
challenges**, and both reduce to the same soundness step: such a product, equal at the random
challenge, forces the underlying multiset identity. This file isolates that step. It rests on the
roots theory `CPolynomial` wraps from Mathlib, but nothing here is stated or proved through
`Polynomial`.

* `prod_cX_add_u_inj` — equal products of the monic linear factors `X + uᵢ` force equal multisets
  `{uᵢ}`: a product is determined by its roots.
* `card_eval_prod_eq_le` — univariate Schwartz–Zippel: for distinct multisets, the challenges
  where the field products collide form a bad set of size `≤ max |s| |t|`.
* `prod_cpair_inj` — the same for factors carrying `(value, name)` pairs, by running the first
  lemma over `R = F[β]`. The permutation argument needs this; the lookup argument instead uses
  `prod_cX_add_u_inj` twice, with independent `β` and `γ`.

The per-argument wrappers — telescoping the running product, the boundary and blinding-row rules,
and the lookup permuted-column structure — build on this in `Permutation.lean` and `Lookup.lean`,
where the structural steps are proven and telescoping remains open.
-/

namespace Zcash.Snark

/-- Encode a pair `(v, n)` as the `F[β]`-element `v + n·β` (here `β = X`).
Injective, since `v` and `n` are its degree-0 and degree-1 coefficients. -/
def encPair {F : Type*} [Field F] [BEq F] [LawfulBEq F] (p : F × F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.C p.1 + CompPoly.CPolynomial.C p.2 * CompPoly.CPolynomial.X

theorem encPair_injective {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    Function.Injective (encPair (F := F)) := by
  intro p q hpq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · have h : CompPoly.CPolynomial.coeff (encPair p) 0
        = CompPoly.CPolynomial.coeff (encPair q) 0 := by rw [hpq]
    rw [encPair, encPair, CompPoly.CPolynomial.coeff_add, CompPoly.CPolynomial.coeff_add,
      CompPoly.CPolynomial.coeff_C, CompPoly.CPolynomial.coeff_C,
      CompPoly.CPolynomial.coeff_mul_X_zero, CompPoly.CPolynomial.coeff_mul_X_zero] at h
    simpa using h
  · have h : CompPoly.CPolynomial.coeff (encPair p) 1
        = CompPoly.CPolynomial.coeff (encPair q) 1 := by rw [hpq]
    rw [encPair, encPair, CompPoly.CPolynomial.coeff_add, CompPoly.CPolynomial.coeff_add,
      CompPoly.CPolynomial.coeff_C, CompPoly.CPolynomial.coeff_C,
      CompPoly.CPolynomial.coeff_mul_X_succ, CompPoly.CPolynomial.coeff_mul_X_succ,
      CompPoly.CPolynomial.coeff_C, CompPoly.CPolynomial.coeff_C] at h
    simpa using h

end Zcash.Snark

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R]

/-- Evaluating a product of linear factors is the product of the shifted points. -/
theorem eval_cprod_X_add_u (m : Multiset R) (β : R) :
    eval β (m.map (fun u => X + C u)).prod = (m.map (fun x => β + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by
    rw [Function.comp_apply, eval_add, eval_X, eval_C])

/-- `∏ (X + uᵢ)` has degree `|m|`. -/
theorem natDegree_cprod_X_add_u (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).natDegree = Multiset.card m :=
  natDegree_prod_X_add_C m

/-- **Multiset-from-product.** Equal products of the monic linear factors `X + uᵢ` force equal
multisets — the kernel behind both permutation and lookup soundness.  Over a domain a product is
determined by its roots, here the negated shifts, and negation is injective. -/
theorem prod_cX_add_u_inj {s t : Multiset R}
    (h : (s.map (fun u => X + C u)).prod = (t.map (fun u => X + C u)).prod) : s = t := by
  refine Multiset.map_injective neg_injective ?_
  rw [← roots_prod_X_add_C s, ← roots_prod_X_add_C t, h]

/-- **The lookup split.** The two lookup products live over separate indeterminates, so equality
forces both column multisets to agree: the leading coefficient in the outer variable is each side's
inner product, and cancelling it leaves the outer one. -/
theorem prod_split_inj {F : Type*} [Field F] [BEq F] [LawfulBEq F] {a s inp tbl : Multiset F}
    (h : C (a.map (fun u => X + C u)).prod * (s.map (fun u => X + C (C u))).prod
       = (C (inp.map (fun u => X + C u)).prod * (tbl.map (fun u => X + C (C u))).prod
           : CompPoly.CPolynomial (CompPoly.CPolynomial F))) : a = inp ∧ s = tbl := by
  -- The outer factors are monic, so the outer leading coefficient of each side is its inner
  -- product; that identifies the input columns.
  have hmap : ∀ m : Multiset F,
      m.map (fun u => (X + C (C u) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))
        = (m.map C).map (fun v => X + C v) := by
    intro m; rw [Multiset.map_map]; rfl
  have hlead := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C, hmap s, hmap tbl,
    leadingCoeff_prod_X_add_C, leadingCoeff_prod_X_add_C, _root_.mul_one, _root_.mul_one] at hlead
  refine ⟨prod_cX_add_u_inj hlead, ?_⟩
  -- Cancelling that common factor leaves the table columns.
  rw [hlead] at h
  have hCne : (C (inp.map (fun u => X + C u)).prod
      : CompPoly.CPolynomial (CompPoly.CPolynomial F)) ≠ 0 := by
    simpa using (C_eq_zero_iff (R := CompPoly.CPolynomial F)).not.mpr (prod_X_add_C_ne_zero inp)
  have hQ := mul_left_cancel₀ hCne h
  rw [hmap s, hmap tbl] at hQ
  exact Multiset.map_injective (C_injective (R := F)) (prod_cX_add_u_inj hQ)

/-- **Univariate Schwartz–Zippel at a point.** For `s ≠ t` over a finite field, the challenges `β`
at which the shifted-factor products `∏ (xᵢ + β)` agree form a "bad set" of size `≤ max |s| |t|` —
the roots of the (nonzero, by `prod_cX_add_u_inj`) difference polynomial. That is, product-equality
at a random `β` forces the multiset identity except on a negligible bad set. -/
theorem card_eval_prod_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {s t : Multiset F} (hst : s ≠ t) :
    (Finset.univ.filter
      (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ max (Multiset.card s) (Multiset.card t) := by
  classical
  set D : CompPoly.CPolynomial F :=
    (s.map (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u)).prod
      - (t.map (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u)).prod with hDdef
  -- the difference is nonzero, since `s ≠ t` (`prod_cX_add_u_inj` contrapositive)
  have hD : D ≠ 0 := fun h0 => hst (prod_cX_add_u_inj (sub_eq_zero.mp h0))
  calc (Finset.univ.filter
          (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ D.roots.toFinset.card := by
        -- every "bad" β is a root of the difference
        apply Finset.card_le_card
        intro β hβ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
        rw [Multiset.mem_toFinset, CompPoly.CPolynomial.mem_roots hD, hDdef,
          CompPoly.CPolynomial.eval_sub, eval_cprod_X_add_u s β, eval_cprod_X_add_u t β, hβ,
          sub_self]
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := CompPoly.CPolynomial.card_roots_le _
    _ ≤ max ((s.map (fun u => CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u)).prod).natDegree
            ((t.map (fun u =>
              CompPoly.CPolynomial.X + CompPoly.CPolynomial.C u)).prod).natDegree :=
          CompPoly.CPolynomial.natDegree_sub_le _ _
    _ = max (Multiset.card s) (Multiset.card t) := by
          rw [natDegree_cprod_X_add_u s, natDegree_cprod_X_add_u t]

/-- **Multisets of pairs.** The same, for factors carrying `(value, name)` pairs, run over the
computable coefficient ring `CPolynomial F`. -/
theorem prod_cpair_inj {F : Type*} [Field F] [BEq F] [LawfulBEq F] {sp tp : Multiset (F × F)}
    (h : (sp.map (fun p =>
        (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod
       = (tp.map (fun p =>
        (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod) : sp = tp := by
  refine Multiset.map_injective encPair_injective (prod_cX_add_u_inj ?_)
  have conv : ∀ m : Multiset (F × F),
      m.map (fun p => (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))
        = (m.map encPair).map (fun u => X + C u) := by
    intro m; rw [Multiset.map_map]; rfl
  rw [← conv sp, ← conv tp]
  exact h

end Zcash.Snark
