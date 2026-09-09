import Zcash.Snark.Soundness.Canonical.PolynomialEnvironment

/-!
# Canonical evaluation-domain selector polynomials

Halo 2's permutation and lookup arguments use three circuit-independent Lagrange
polynomials:

* `l₀`, one at the first row and zero elsewhere;
* `l_last`, one at the final usable row and zero elsewhere;
* `l_blind`, one on the rows after `l_last` and zero through the usable rows.

This module defines those polynomials by their domain rows and proves the evaluations
needed by the generic permutation and lookup semantic records. Identifying the
verifier's decoded `l₀`/`l_last`/`l_blind` with these canonical polynomials remains a
multiopen/domain-polynomial provenance step, not a circuit-specific layout fact.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

/-- The Lagrange row selector that is one at `selected` and zero at every other row. -/
def rowSelectorPolynomial {n : ℕ}
    (omega : Fp) (selected : Fin n) : CPoly :=
  rowPolynomial omega (Pi.single selected 1)

/-- The selector that is one exactly on rows strictly after the final usable row. -/
def blindSelectorPolynomial {n : ℕ}
    (omega : Fp) (lastUsable : Fin n) : CPoly :=
  rowPolynomial omega fun row : Fin n =>
    if lastUsable.val < row.val then 1 else 0

/-- A single-row selector has degree below the size of its evaluation domain. -/
theorem rowSelectorPolynomial_natDegree_lt {n : ℕ} {omega : Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (selected : Fin n) : (rowSelectorPolynomial omega selected).natDegree < n := by
  exact rowPolynomial_natDegree_lt hrows (Nat.zero_lt_of_lt selected.isLt)

/-- The selector for the blinded rows has degree below the size of its domain. -/
theorem blindSelectorPolynomial_natDegree_lt {n : ℕ} {omega : Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (lastUsable : Fin n) : (blindSelectorPolynomial omega lastUsable).natDegree < n := by
  exact rowPolynomial_natDegree_lt hrows (Nat.zero_lt_of_lt lastUsable.isLt)

/-- A row selector is exactly the corresponding Lagrange basis polynomial. -/
theorem toPoly_rowSelectorPolynomial {n : ℕ}
    (omega : Fp) (selected : Fin n) :
    (rowSelectorPolynomial omega selected).toPoly =
      Lagrange.basis Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) selected := by
  classical
  rw [rowSelectorPolynomial, toPoly_rowPolynomial, Lagrange.interpolate_apply]
  rw [Finset.sum_eq_single selected]
  · simp
  · intro row _ hne
    simp [hne]
  · simp

/--
The nodal polynomial of an injectively enumerated size-`n` root-of-unity domain
is the usual vanishing polynomial `Xⁿ - 1`.
-/
private theorem domainNodal_eq_vanishing {n : ℕ} {omega : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1) :
    Lagrange.nodal Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) =
      Polynomial.X ^ n - 1 := by
  have hdegree : (1 : Polynomial Fp).degree < ((Polynomial.X : Polynomial Fp) ^ n).degree := by
    simp [hn]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ hrows.injOn
  · simp
  · rw [Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin,
      Polynomial.degree_sub_eq_left_of_degree_lt hdegree, Polynomial.degree_pow,
      Polynomial.degree_X, nsmul_eq_mul, _root_.mul_one]
  · rw [Lagrange.nodal_monic, Polynomial.leadingCoeff_sub_of_degree_lt hdegree,
      Polynomial.monic_X_pow]
  · intro row hrow
    rw [Lagrange.eval_nodal_at_node
      (s := Finset.univ) (v := fun i : Fin n => omega ^ (i : ℕ)) hrow]
    have hpow : (omega ^ (row : ℕ)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
    simp [Polynomial.eval_sub, Polynomial.eval_pow, hpow]

/-- The barycentric weight of row `i` in a root-of-unity domain is `ωⁱ / n`. -/
private theorem domainNodalWeight_eq {n : ℕ} {omega : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (row : Fin n) :
    Lagrange.nodalWeight Finset.univ
        (fun i : Fin n => omega ^ (i : ℕ)) row =
      omega ^ (row : ℕ) / (n : Fp) := by
  have hrowRoot : (omega ^ (row : ℕ)) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ row),
    domainNodal_eq_vanishing hn hrows hroot, Polynomial.derivative_sub,
    Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow]
  apply inv_eq_of_mul_eq_one_right
  field_simp
  rw [Polynomial.eval_X, _root_.mul_comm, ← pow_succ,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hn))]
  exact hrowRoot

/--
Away from its selected domain node, a canonical row selector evaluates to the
closed formula used by the deployed verifier.
-/
theorem rowSelectorPolynomial_eval_eq_lagrangeBasisValue
    {n : ℕ} {omega x : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (selected : Fin n)
    (hx : x ≠ omega ^ (selected : ℕ)) :
    (rowSelectorPolynomial omega selected).eval x =
      lagrangeBasisValue omega n (x ^ n) x (selected : ℤ) := by
  rw [eval_toPoly, toPoly_rowSelectorPolynomial,
    Lagrange.eval_basis_not_at_node (Finset.mem_univ selected) hx,
    domainNodal_eq_vanishing hn hrows hroot,
    domainNodalWeight_eq hn hrows hroot hnFp selected]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  simp [lagrangeBasisValue, div_eq_mul_inv]
  ring

/-- The same verifier formula, expressed at any rotation naming the selected row. -/
theorem rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation
    {n : ℕ} {omega x : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (selected : Fin n) (rotation : ℤ)
    (hrotation : omega ^ (selected : ℕ) = omega ^ rotation)
    (hx : x ≠ omega ^ rotation) :
    (rowSelectorPolynomial omega selected).eval x =
      lagrangeBasisValue omega n (x ^ n) x rotation := by
  have hxSelected : x ≠ omega ^ (selected : ℕ) := by
    simpa [hrotation] using hx
  rw [rowSelectorPolynomial_eval_eq_lagrangeBasisValue
    hn hrows hroot hnFp selected hxSelected]
  simp only [lagrangeBasisValue]
  rw [show omega ^ (selected : ℤ) = omega ^ (selected : ℕ) by simp,
    hrotation]

/-- A row counted backward from the end of the domain is the matching negative rotation. -/
theorem domain_pow_sub_eq_zpow_neg {n t : ℕ} {omega : Fp}
    (ht : t ≤ n) (hroot : omega ^ n = 1) :
    omega ^ (n - t) = omega ^ (-(t : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel ht, hroot]

/-- The last usable row when `blinding` rows are reserved at the domain's end. -/
def lastUsableDomainRow {n blinding : ℕ}
    (hblinding : blinding < n) : Fin n :=
  ⟨n - blinding - 1, by omega⟩

/-- Blinding rotation `-(j+1)` represented as its nonnegative domain row. -/
def blindingDomainRow {n blinding : ℕ}
    (hblinding : blinding < n) (j : Fin blinding) : Fin n :=
  ⟨n - (j + 1), by omega⟩

/--
Negative blinding rotations enumerate exactly the rows after the final usable
row. The reverse ordering is immaterial to their sum.
-/
def blindingDomainRowEquiv {n blinding : ℕ}
    (hblinding : blinding < n) :
    Fin blinding ≃
      {row : Fin n // (lastUsableDomainRow hblinding).val < row.val} where
  toFun j := ⟨blindingDomainRow hblinding j, by
    simp only [lastUsableDomainRow, blindingDomainRow]
    omega⟩
  invFun row := ⟨n - row.val - 1, by
    have hlast := row.property
    have hrow := row.val.isLt
    simp only [lastUsableDomainRow] at hlast
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only [blindingDomainRow]
    omega
  right_inv row := by
    apply Subtype.ext
    apply Fin.ext
    simp only [blindingDomainRow]
    have hrow := row.val.isLt
    omega

/-- The blinding selector is the sum of the row selectors after `lastUsable`. -/
theorem blindSelectorPolynomial_eq_sum {n : ℕ}
    (omega : Fp) (lastUsable : Fin n) :
    blindSelectorPolynomial omega lastUsable =
      ∑ row ∈ (Finset.univ : Finset (Fin n)).filter
          (fun row => lastUsable.val < row.val),
        rowSelectorPolynomial omega row := by
  classical
  apply toPoly_injective
  rw [blindSelectorPolynomial, toPoly_rowPolynomial, Lagrange.interpolate_apply, toPoly_sum]
  simp_rw [toPoly_rowSelectorPolynomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hselected : lastUsable.val < row.val
  · simp [hselected]
  · simp [hselected]

private theorem foldl_add_map_range (f : ℕ → Fp) (n : ℕ) :
    ((List.range n).map f).foldl (· + ·) 0 =
      ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_eq_foldl]
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/--
The canonical blinding selector evaluates to the exact sum of negative-rotation
Lagrange values used by the deployed verifier.
-/
theorem blindSelectorPolynomial_eval_eq_lagrangeBasis
    {n blinding : ℕ} {omega x : Fp}
    (hblinding : blinding < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (hxDomain : x ^ n ≠ 1) :
    (blindSelectorPolynomial omega (lastUsableDomainRow hblinding)).eval x =
      ((List.range blinding).map (fun j : ℕ =>
        lagrangeBasisValue omega n (x ^ n) x
          (-((j : ℤ) + 1)))).foldl (· + ·) 0 := by
  classical
  let e := blindingDomainRowEquiv hblinding
  letI : Fintype
      {row : Fin n // (lastUsableDomainRow hblinding).val < row.val} :=
    Fintype.ofEquiv (Fin blinding) e
  have hxRow (row : Fin n) : x ≠ omega ^ (row : ℕ) := by
    intro heq
    apply hxDomain
    rw [heq]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  rw [blindSelectorPolynomial_eq_sum, eval_finsetSum]
  rw [Finset.sum_subtype
    (p := fun row : Fin n =>
      (lastUsableDomainRow hblinding).val < row.val)
    ((Finset.univ : Finset (Fin n)).filter
      (fun row => (lastUsableDomainRow hblinding).val < row.val))
    (by simp) (fun row => (rowSelectorPolynomial omega row).eval x)]
  rw [← e.sum_comp]
  rw [show (∑ j : Fin blinding,
      (rowSelectorPolynomial omega (e j).val).eval x) =
      ∑ j : Fin blinding,
        lagrangeBasisValue omega n (x ^ n) x
          (-((j : ℤ) + 1)) by
    apply Fintype.sum_congr
    intro j
    have hrotation :
        omega ^ ((e j).val : ℕ) = omega ^ (-((j : ℤ) + 1)) := by
      change omega ^ (n - (j.val + 1)) =
        omega ^ (-((j : ℤ) + 1))
      simpa using domain_pow_sub_eq_zpow_neg (omega := omega)
        (t := j.val + 1) (by omega) hroot
    apply rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation
      (Nat.zero_lt_of_lt hblinding) hrows hroot hnFp _ _ hrotation
    intro heq
    exact hxRow (e j).val (heq.trans hrotation.symm)]
  let f : ℕ → Fp := fun j =>
    lagrangeBasisValue omega n (x ^ n) x (-((j : ℤ) + 1))
  change (∑ j : Fin blinding, f j.val) =
    ((List.range blinding).map f).foldl (· + ·) 0
  rw [Fin.sum_univ_eq_sum_range f blinding]
  exact (foldl_add_map_range f blinding).symm

/-- The three fixed selector polynomials corresponding to the verifier's Lagrange triple. -/
def canonicalLagrangePolynomials
    {n blinding : ℕ} (omega : Fp) (hblinding : blinding < n) :
    CPoly × CPoly × CPoly :=
  (rowSelectorPolynomial omega ⟨0, Nat.zero_lt_of_lt hblinding⟩,
    rowSelectorPolynomial omega (lastUsableDomainRow hblinding),
    blindSelectorPolynomial omega (lastUsableDomainRow hblinding))

/--
Evaluating the fixed canonical selector triple away from the evaluation domain
is exactly the deployed verifier's `lagrangeBasis` computation.
-/
theorem canonicalLagrangePolynomials_eval
    {n blinding : ℕ} {omega x : Fp}
    (hblinding : blinding < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (hxDomain : x ^ n ≠ 1) :
    let selectors := canonicalLagrangePolynomials omega hblinding
    (selectors.1.eval x, selectors.2.1.eval x, selectors.2.2.eval x) =
      lagrangeBasis omega n blinding (x ^ n) x := by
  have hn : 0 < n := Nat.zero_lt_of_lt hblinding
  have hxRow (row : Fin n) : x ≠ omega ^ (row : ℕ) := by
    intro heq
    apply hxDomain
    rw [heq]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  have hfirst :
      (rowSelectorPolynomial omega ⟨0, hn⟩).eval x =
        lagrangeBasisValue omega n (x ^ n) x 0 := by
    apply rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation
      hn hrows hroot hnFp _ 0
    · simp
    · simpa using hxRow ⟨0, hn⟩
  have hlastRotation :
      omega ^ ((lastUsableDomainRow hblinding : Fin n) : ℕ) =
        omega ^ (-((blinding : ℤ) + 1)) := by
    change omega ^ (n - blinding - 1) =
      omega ^ (-((blinding : ℤ) + 1))
    rw [show n - blinding - 1 = n - (blinding + 1) by omega]
    exact domain_pow_sub_eq_zpow_neg (omega := omega)
      (t := blinding + 1) (by omega) hroot
  have hlast :
      (rowSelectorPolynomial omega
          (lastUsableDomainRow hblinding)).eval x =
        lagrangeBasisValue omega n (x ^ n) x
          (-((blinding : ℤ) + 1)) := by
    apply rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation
      hn hrows hroot hnFp _ _ hlastRotation
    intro heq
    exact hxRow (lastUsableDomainRow hblinding)
      (heq.trans hlastRotation.symm)
  have hblind :=
    blindSelectorPolynomial_eval_eq_lagrangeBasis
      hblinding hrows hroot hnFp hxDomain
  simp only [canonicalLagrangePolynomials, lagrangeBasis]
  rw [hfirst, hlast, hblind]
  have hcastList :
      (do
        let a ← List.range blinding
        pure (a : ℤ)) =
        (List.range blinding).map (fun a : ℕ => (a : ℤ)) := by
    exact List.flatMap_pure_eq_map
      (fun a : ℕ => (a : ℤ)) (List.range blinding)
  rw [hcastList, List.map_map]
  rfl

@[simp] theorem rowSelectorPolynomial_eval {n : ℕ}
    {omega : Fp} (selected row : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega selected).eval (omega ^ (row : ℕ)) =
      if row = selected then 1 else 0 := by
  rw [rowSelectorPolynomial, rowPolynomial_eval hrows]
  by_cases h : row = selected
  · subst row
    simp
  · simp [h]

@[simp] theorem blindSelectorPolynomial_eval {n : ℕ}
    {omega : Fp} (lastUsable row : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (blindSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ)) =
      if lastUsable.val < row.val then 1 else 0 := by
  rw [blindSelectorPolynomial, rowPolynomial_eval hrows]

/-- `l₀` is nonzero at the first row. -/
theorem firstSelectorPolynomial_nonzero {n : ℕ}
    {omega : Fp} (first : Fin n) (hfirst : (first : ℕ) = 0)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega first).eval (omega ^ 0) ≠ 0 := by
  have hpow : omega ^ (first : ℕ) = omega ^ 0 := by rw [hfirst]
  rw [← hpow, rowSelectorPolynomial_eval first first hrows]
  norm_num

/-- `l_last` is nonzero at the final usable row. -/
theorem lastSelectorPolynomial_nonzero {n : ℕ}
    {omega : Fp} (lastUsable : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega lastUsable).eval
        (omega ^ (lastUsable : ℕ)) ≠ 0 := by
  rw [rowSelectorPolynomial_eval lastUsable lastUsable hrows]
  norm_num

/--
Before the final usable row, both `l_last` and `l_blind` vanish, so the
permutation/lookup recurrence's active-row multiplier is one.
-/
theorem last_add_blind_active {n : ℕ}
    {omega : Fp} (lastUsable row : Fin n)
    (hrow : (row : ℕ) < lastUsable)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    1 -
      ((rowSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ)) +
       (blindSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ))) ≠ 0 := by
  rw [rowSelectorPolynomial_eval lastUsable row hrows,
    blindSelectorPolynomial_eval lastUsable row hrows]
  have hne : row ≠ lastUsable := Fin.ne_of_lt hrow
  simp [hne, Nat.not_lt.mpr (Nat.le_of_lt hrow)]

end Zcash.Snark
