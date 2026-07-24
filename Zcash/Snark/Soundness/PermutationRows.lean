import Mathlib
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge

/-!
# The verifier's permutation constraints, read row by row

`GrandProductBridge` closes the permutation argument from a one-row recurrence on the running
product. This module produces that recurrence from the verifier's own constraint list, so nothing
about the shape of the checks is assumed.

The route is short once the constraints are individually known to vanish on the domain
(`FoldSplit.constraints_dvd_of_good_y`):

* `eval_eq_zero_of_dvd_vanishing` — a constraint divisible by `Xⁿ − 1` vanishes at every row.
* `permSetPolys` — the running product as a permutation set: this row is `z`, the next row is
  `z` composed with the rotation `ω·X`, which at row `ωⁱ` reads `z(ω^{i+1})`.
* `perm_row_recurrence` — the step rule at row `ωⁱ`, with the row switched on, *is* the recurrence.
* `running_product_start` / `running_product_end` — the boundary rules give `z = 1` at the first row
  and `z ∈ {0, 1}` at the last.
* `name_injective_of_coset` — the identity names `ωⁱ·δ^j` are distinct across cells, from `ω`'s
  order and the `δ`-coset distinctness the keygen chooses `δ` to satisfy.

Everything here is about the deployed `permChunkExpression`, not a restatement of it.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- A constraint that vanishes on the whole domain vanishes at each row. -/
theorem eval_eq_zero_of_dvd_vanishing {n : ℕ} {c : Polynomial Fp}
    (h : (X ^ n - 1 : Polynomial Fp) ∣ c) {r : Fp} (hr : r ^ n = 1) : c.eval r = 0 := by
  obtain ⟨d, rfl⟩ := h
  simp [hr]

/-- The running product as a permutation set: `eval` is this row, `nextEval` is the next row (the
polynomial composed with the rotation `ω·X`), and `lastEval` is supplied by the caller. -/
noncomputable def permSetPolys (omega : Fp) (z : Polynomial Fp)
    (last : Option (Polynomial Fp)) : PermSetEval (Polynomial Fp) :=
  { eval := z, nextEval := z.comp (C omega * X), lastEval := last }

@[simp] theorem permSetPolys_eval (omega : Fp) (z : Polynomial Fp) (last) :
    (permSetPolys omega z last).eval = z := rfl

/-- The next-row component really is the next row: at `ωⁱ` it reads `z(ω^{i+1})`. -/
theorem eval_permSetPolys_nextEval (omega : Fp) (z : Polynomial Fp) (last) (i : ℕ) :
    ((permSetPolys omega z last).nextEval).eval (omega ^ i) = z.eval (omega ^ (i + 1)) := by
  rw [permSetPolys, eval_comp_rotate, pow_succ, mul_comm]

/-- **The step rule is the recurrence.** At a row the verifier has switched on, the deployed
`permChunkExpression` vanishing says exactly that the running product advances by the ratio of the
`σ`-named factors to the identity-named ones. The identity name of column `j` in chunk `c` at row
`ωⁱ` is `ωⁱ·δ^{c·chunkLen + j}`. -/
theorem perm_row_recurrence (omega beta gamma delta : Fp) (chunkLen chunkIndex : ℕ)
    (z : Polynomial Fp) (last : Option (Polynomial Fp))
    (pairs : List (Polynomial Fp × Polynomial Fp)) (lLastP lBlindP : Polynomial Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ permChunkExpression (C beta) (C gamma) X (C delta)
      chunkLen chunkIndex (permSetPolys omega z last) pairs lLastP lBlindP)
    {i : ℕ} (hpow : (omega ^ i) ^ n = 1)
    (hactive : 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0) :
    z.eval (omega ^ (i + 1)) * ∏ j ∈ range pairs.length,
        ((pairs.getD j (0, 0)).1.eval (omega ^ i)
          + beta * (pairs.getD j (0, 0)).2.eval (omega ^ i) + gamma)
      = z.eval (omega ^ i) * ∏ j ∈ range pairs.length,
        ((pairs.getD j (0, 0)).1.eval (omega ^ i)
          + beta * (omega ^ i * delta ^ (chunkIndex * chunkLen + j)) + gamma) := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  rw [permChunkExpression_eq] at hzero
  simp only [eval_mul, eval_sub, eval_prod, eval_add, eval_C, eval_X, eval_one, eval_pow,
    eval_permSetPolys_nextEval, permSetPolys_eval] at hzero
  rcases mul_eq_zero.mp hzero with hbr | hact
  · have := sub_eq_zero.mp hbr
    rw [this]
    exact congrArg _ (prod_congr rfl fun j _ => by ring)
  · exact absurd hact hactive

/-- The first-row rule `ℓ₀·(1 − z) = 0` pins the running product to `1` where `ℓ₀` is nonzero. -/
theorem running_product_start {l0P zP : Polynomial Fp} {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (1 - zP)) {r : Fp} (hr : r ^ n = 1)
    (hl0 : l0P.eval r ≠ 0) : zP.eval r = 1 := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub, eval_one] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hl0
  · exact (sub_eq_zero.mp h).symm

/-- The last-row rule `(z² − z)·ℓ_last = 0` leaves the running product at `0` or `1` where
`ℓ_last` is nonzero. -/
theorem running_product_end {lLastP zP : Polynomial Fp} {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ (zP ^ 2 - zP) * lLastP) {r : Fp} (hr : r ^ n = 1)
    (hlast : lLastP.eval r ≠ 0) : zP.eval r = 0 ∨ zP.eval r = 1 := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub, eval_pow] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · have hfac : zP.eval r * (zP.eval r - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · exact absurd h hlast

/-! ## The identity names are distinct

halo2 names cell `(row i, column j)` by `ωⁱ·δ^j`. Distinctness of those names is what turns the
multiset identity into the per-cell copy constraints, and it rests on two facts about the verifying
key's constants: `ω` generates a subgroup of order `u`, and the powers of `δ` below the column count
lie in distinct cosets of that subgroup. The second is the property halo2's keygen picks `δ` to
have; it is a statement about the concrete key, checkable for a given one, not an assumption about
the proof system. -/

/-- **Name distinctness.** With `ω` of order `u` and the column names in distinct cosets of `⟨ω⟩`,
the cell names `ωⁱ·colName j` separate the cells. -/
theorem name_injective_of_coset {omega : Fp} {u k : ℕ} (colName : Fin k → Fp)
    (hne : ∀ j, colName j ≠ 0) (homega : omega ^ u = 1)
    (horder : ∀ i i' : ℕ, i < u → i' < u → omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀ (j j' : Fin k) (t : ℕ), colName j = omega ^ t * colName j' → j = j') :
    Function.Injective fun c : Fin u × Fin k => omega ^ (c.1 : ℕ) * colName c.2 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h
  -- multiply by `ω^{u−i}` to clear the row factor without dividing
  have hshift : colName j = omega ^ (u - (i : ℕ) + (i' : ℕ)) * colName j' := by
    have hmul := congrArg (fun v => omega ^ (u - (i : ℕ)) * v) h
    simp only at hmul
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt i.isLt), homega, one_mul] at hmul
    rw [hmul, ← mul_assoc, ← pow_add]
  have hj : j = j' := hcoset _ _ _ hshift
  have hi : (i : ℕ) = (i' : ℕ) := by
    refine horder _ _ i.isLt i'.isLt ?_
    rw [hj] at h
    exact mul_right_cancel₀ (hne j') h
  exact Prod.ext (Fin.ext hi) hj

/-! ## The permutation argument at the deployed constraints

Naming the three families the row reading produces, so the end-to-end statement stays readable: the
committed column value at a cell, the permutation column's value there (the `σ`-side name), and the
identity name `ωⁱ·δ^{offset + j}` halo2 assigns the cell. -/

/-- The committed column's value at row `ωⁱ`, column `j`. -/
noncomputable def rowValue (omega : Fp) (pairs : List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → Fp := fun i j => (pairs.getD j (0, 0)).1.eval (omega ^ i)

/-- The permutation column's value at row `ωⁱ`, column `j` — the name `σ` sends the cell to. -/
noncomputable def rowSigmaName (omega : Fp) (pairs : List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → Fp := fun i j => (pairs.getD j (0, 0)).2.eval (omega ^ i)

/-- The identity name halo2 assigns to row `ωⁱ`, column `j` of a chunk starting at `off`. -/
noncomputable def rowName (omega delta : Fp) (off : ℕ) : ℕ → ℕ → Fp :=
  fun i j => omega ^ i * delta ^ (off + j)

open Finset in
/-- **The permutation argument, closed at the deployed constraints.** Every hypothesis is either a
constraint the verifier checks (`hstep`/`hstart`/`hend`, each vanishing on the domain), a fact about
the verifying key's constants (`hrow`/`hactive`/`hl0`/`hlast`/`hnm`), or a challenge avoiding a
priced root set. The conclusion is halo2's copy constraint: cells in the same cycle of `σ` hold
equal values. The surviving branch is a vanishing factor — the running product ended at zero, or a
name collided with a value. -/
theorem deployed_perm_copy_constraints
    (omega beta gamma delta : Fp) (chunkLen chunkIndex : ℕ)
    (z : Polynomial Fp) (last : Option (Polynomial Fp))
    (pairs : List (Polynomial Fp × Polynomial Fp)) (l0P lLastP lBlindP : Polynomial Fp)
    {n u : ℕ} (σ : Equiv.Perm (Fin u × Fin pairs.length))
    (hstep : (X ^ n - 1 : Polynomial Fp) ∣ permChunkExpression (C beta) (C gamma) X (C delta)
      chunkLen chunkIndex (permSetPolys omega z last) pairs lLastP lBlindP)
    (hstart : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (1 - z))
    (hend : (X ^ n - 1 : Polynomial Fp) ∣ (z ^ 2 - z) * lLastP)
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0)
    (hσ : ∀ c : Fin u × Fin pairs.length,
      rowSigmaName omega pairs (c.1 : ℕ) (c.2 : ℕ)
        = rowName omega delta (chunkIndex * chunkLen) ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin u × Fin pairs.length =>
      rowName omega delta (chunkIndex * chunkLen) (c.1 : ℕ) (c.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((cellPairs u pairs.length (rowValue omega pairs)
        (rowSigmaName omega pairs)).map (fun p => p.1 + p.2 * beta))
      ((cellPairs u pairs.length (rowValue omega pairs)
        (rowName omega delta (chunkIndex * chunkLen))).map (fun p => p.1 + p.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (cellPairs u pairs.length (rowValue omega pairs) (rowSigmaName omega pairs))
      (cellPairs u pairs.length (rowValue omega pairs)
        (rowName omega delta (chunkIndex * chunkLen)))).coeff j))
    {c d : Fin u × Fin pairs.length} (hcd : σ.SameCycle c d) :
    rowValue omega pairs (c.1 : ℕ) (c.2 : ℕ) = rowValue omega pairs (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ p ∈ range u ×ˢ range pairs.length,
          rowValue omega pairs p.1 p.2
            + beta * rowName omega delta (chunkIndex * chunkLen) p.1 p.2 + gamma = 0 := by
  refine perm_copy_constraints_of_running_product (fun i => z.eval (omega ^ i))
    (rowValue omega pairs) (rowName omega delta (chunkIndex * chunkLen))
    (rowSigmaName omega pairs) beta gamma σ hσ hnm ?_ ?_ ?_ hgoodγ hgoodβ hcd
  · intro i hi
    simpa [rowValue, rowSigmaName, rowName, pow_add, mul_assoc, mul_comm, mul_left_comm] using
      perm_row_recurrence omega beta gamma delta chunkLen chunkIndex z last pairs lLastP lBlindP
        hstep (hrow i) (hactive i hi)
  · simpa using running_product_start hstart (hrow 0) hl0
  · exact running_product_end hend (hrow u) hlast


/-! ## The deployed instantiation

`constraintPolys` leaves the permutation sets and chunks as parameters, because the column
polynomials come from the decode rather than the verifying key. These definitions make the choice
the soundness argument needs: each chunk's set *is* a committed running product together with the
rotation that reads the next row. -/

/-- The permutation sets at the polynomial level: chunk `c` carries its running product `z c`. -/
noncomputable def deployedPermSets (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) : List (PermSetEval (Polynomial Fp)) :=
  (List.range nc).map (fun c => permSetPolys omega (z c) (lastP c))

/-- The permutation chunks at the polynomial level: each set with its chunk's columns. -/
noncomputable def deployedPermChunks (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) (cols : ℕ → List (Polynomial Fp × Polynomial Fp)) :
    List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)) :=
  (List.range nc).map (fun c => (permSetPolys omega (z c) (lastP c), cols c))

@[simp] theorem length_deployedPermChunks (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) (cols : ℕ → List (Polynomial Fp × Polynomial Fp)) :
    (deployedPermChunks omega nc z lastP cols).length = nc := by
  simp [deployedPermChunks]

@[simp] theorem getElem_deployedPermChunks (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {c : ℕ} (hc : c < (deployedPermChunks omega nc z lastP cols).length) :
    (deployedPermChunks omega nc z lastP cols)[c]
      = (permSetPolys omega (z c) (lastP c), cols c) := by
  simp only [deployedPermChunks, List.getElem_map, List.getElem_range]

theorem head?_deployedPermSets (omega : Fp) {nc : ℕ} (hnc : 0 < nc) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) :
    (deployedPermSets omega nc z lastP).head? = some (permSetPolys omega (z 0) (lastP 0)) := by
  rw [deployedPermSets, List.head?_map]
  rcases nc with _ | nc
  · exact absurd hnc (lt_irrefl 0)
  · simp [List.range_succ_eq_map]

theorem getLast?_deployedPermSets (omega : Fp) {nc : ℕ} (hnc : 0 < nc) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) :
    (deployedPermSets omega nc z lastP).getLast?
      = some (permSetPolys omega (z (nc - 1)) (lastP (nc - 1))) := by
  rw [deployedPermSets, List.getLast?_map]
  rcases nc with _ | nc
  · exact absurd hnc (lt_irrefl 0)
  · simp [List.range_succ]

/-- The chaining rule at a row: the next chunk's running product starts where this one ended. -/
theorem running_product_chain {l0P A B : Polynomial Fp} {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ (A - B) * l0P) {r : Fp} (hr : r ^ n = 1)
    (hl0 : l0P.eval r ≠ 0) : A.eval r = B.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hl0

@[simp] theorem length_deployedPermSets (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) :
    (deployedPermSets omega nc z lastP).length = nc := by
  simp [deployedPermSets]

@[simp] theorem getElem_deployedPermSets (omega : Fp) (nc : ℕ) (z : ℕ → Polynomial Fp)
    (lastP : ℕ → Option (Polynomial Fp)) {c : ℕ}
    (hc : c < (deployedPermSets omega nc z lastP).length) :
    (deployedPermSets omega nc z lastP)[c] = permSetPolys omega (z c) (lastP c) := by
  simp only [deployedPermSets, List.getElem_map, List.getElem_range]

open Finset in
/-- **The copy constraints from the constraint identity.** Every input is either a constraint the
verifier's own polynomial identity supplies (`hidentity`), a challenge avoiding a priced root set,
or a condition on the verifying key's constants. Nothing about the shape of the checks is assumed:
the step rule and the two boundary rules are located inside the deployed constraint list and their
vanishing is read off the identity. Stated for a single permutation chunk; several are
`deployed_copy_constraints_of_identity_chunks` below. -/
theorem deployed_copy_constraints_of_identity
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n u : ℕ} (hn : n ≠ 0) (p : Fin np)
    (σ : Equiv.Perm (Fin u × Fin (cols 0).length))
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates
        (fun _ => deployedPermSets omega 1 z lastP)
        (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
        beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
      (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
      beta gamma delta theta chunkLen l0P lLastP lBlindP) n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0)
    (hσ : ∀ c : Fin u × Fin (cols 0).length,
      rowSigmaName omega (cols 0) (c.1 : ℕ) (c.2 : ℕ)
        = rowName omega delta 0 ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin u × Fin (cols 0).length =>
      rowName omega delta 0 (c.1 : ℕ) (c.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowSigmaName omega (cols 0))).map (fun q => q.1 + q.2 * beta))
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (cellPairs u (cols 0).length (rowValue omega (cols 0)) (rowSigmaName omega (cols 0)))
      (cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0))).coeff j))
    {c d : Fin u × Fin (cols 0).length} (hcd : σ.SameCycle c d) :
    rowValue omega (cols 0) (c.1 : ℕ) (c.2 : ℕ)
        = rowValue omega (cols 0) (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ q ∈ range u ×ˢ range (cols 0).length,
          rowValue omega (cols 0) q.1 q.2
            + beta * rowName omega delta 0 q.1 q.2 + gamma = 0 := by
  -- every constraint in the deployed list vanishes on the domain
  have hall := constraints_dvd_of_good_y _ hpoly hn hidentity hgoodY
  -- locate the step rule and the two boundary rules inside that list
  have hmemStep := mem_constraintPolys_of_mem_permutationExpressions fixedCols adviceCols
    instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
    (fun _ => deployedPermChunks omega 1 z lastP cols) lookups beta gamma delta theta chunkLen
    l0P lLastP lBlindP p
    (permChunkExpression_mem_permutationExpressions (deployedPermSets omega 1 z lastP)
      (deployedPermChunks omega 1 z lastP cols) (C beta) (C gamma) X (C delta) chunkLen
      l0P lLastP lBlindP (c := 0) (by simp))
  have hmemStart := mem_constraintPolys_of_mem_permutationExpressions fixedCols adviceCols
    instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
    (fun _ => deployedPermChunks omega 1 z lastP cols) lookups beta gamma delta theta chunkLen
    l0P lLastP lBlindP p
    (start_mem_permutationExpressions (deployedPermChunks omega 1 z lastP cols) (C beta) (C gamma)
      X (C delta) chunkLen l0P lLastP lBlindP
      (head?_deployedPermSets omega Nat.one_pos z lastP))
  have hmemEnd := mem_constraintPolys_of_mem_permutationExpressions fixedCols adviceCols
    instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
    (fun _ => deployedPermChunks omega 1 z lastP cols) lookups beta gamma delta theta chunkLen
    l0P lLastP lBlindP p
    (end_mem_permutationExpressions (deployedPermChunks omega 1 z lastP cols) (C beta) (C gamma)
      X (C delta) chunkLen l0P lLastP lBlindP
      (getLast?_deployedPermSets omega Nat.one_pos z lastP))
  have hstep := hall _ hmemStep
  have hstart := hall _ hmemStart
  have hend := hall _ hmemEnd
  simp only [getElem_deployedPermChunks, permSetPolys_eval] at hstep hstart hend
  have key := deployed_perm_copy_constraints omega beta gamma delta chunkLen 0 (z 0) (lastP 0)
    (cols 0) l0P lLastP lBlindP σ (by simpa using hstep) hstart hend hrow hactive hl0 hlast
    (by simpa [Nat.zero_mul] using hσ) (by simpa [Nat.zero_mul] using hnm)
    (by simpa [Nat.zero_mul] using hgoodγ) (by simpa [Nat.zero_mul] using hgoodβ) hcd
  simpa [Nat.zero_mul] using key


open Finset in
/-- **The circuit's declared equalities, from the constraint identity.** `deployed_copy_constraints_of_identity`
with the permutation taken to be the one built from the circuit's copy constraints, so the
conclusion names the equalities the circuit declared rather than the cycles of some permutation. -/
theorem deployed_declared_equalities_of_identity
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n u : ℕ} (hn : n ≠ 0) (p : Fin np)
    (cs : List ((Fin u × Fin (cols 0).length) × (Fin u × Fin (cols 0).length)))
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates
        (fun _ => deployedPermSets omega 1 z lastP)
        (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
        beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
      (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
      beta gamma delta theta chunkLen l0P lLastP lBlindP) n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0)
    (hσ : ∀ c : Fin u × Fin (cols 0).length,
      rowSigmaName omega (cols 0) (c.1 : ℕ) (c.2 : ℕ)
        = rowName omega delta 0 ((PermConstruction.build cs c).1 : ℕ)
            ((PermConstruction.build cs c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin u × Fin (cols 0).length =>
      rowName omega delta 0 (c.1 : ℕ) (c.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowSigmaName omega (cols 0))).map (fun q => q.1 + q.2 * beta))
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (cellPairs u (cols 0).length (rowValue omega (cols 0)) (rowSigmaName omega (cols 0)))
      (cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0))).coeff j))
    {x w : Fin u × Fin (cols 0).length}
    (hxw : Relation.EqvGen (fun a b => (a, b) ∈ cs) x w) :
    rowValue omega (cols 0) (x.1 : ℕ) (x.2 : ℕ)
        = rowValue omega (cols 0) (w.1 : ℕ) (w.2 : ℕ)
      ∨ ∃ q ∈ range u ×ˢ range (cols 0).length,
          rowValue omega (cols 0) q.1 q.2
            + beta * rowName omega delta 0 q.1 q.2 + gamma = 0 :=
  deployed_copy_constraints_of_identity omega beta gamma delta theta y chunkLen z lastP cols
    fixedCols adviceCols instanceCols gates lookups l0P lLastP lBlindP hpoly hn p
    (PermConstruction.build cs) hidentity hgoodY hrow hactive hl0 hlast hσ hnm hgoodγ hgoodβ
    ((PermConstruction.build_correct cs x w).mpr hxw)


/-! ## Cells across chunks of different widths

Orchard's key splits the permutation columns into chunks of different widths — 7, 7 and 1 at the
consensus shape — each with its own running product. A cell of the whole table is therefore a
dependent triple: chunk, row, and a column below that chunk's own width. The chunks chain end to
start, which makes the chunk products one more running product, so the single-chunk argument covers
the whole table. -/

/-- The `(value, name)` pair of every cell across chunks of varying widths. -/
noncomputable def chunkCellPairs (nc m : ℕ) (k : Fin nc → ℕ)
    (value nm : ℕ → ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset ((c : Fin nc) × Fin m × Fin (k c))).val.map
    (fun cell => (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
      nm (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)))

open Finset in
/-- A product over the chunked cell pairs is the chunk-by-chunk product the telescoping produces. -/
theorem prod_map_chunkCellPairs (nc m : ℕ) (k : Fin nc → ℕ) (value nm : ℕ → ℕ → ℕ → Fp)
    (f : Fp × Fp → Fp) :
    ((chunkCellPairs nc m k value nm).map f).prod
      = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
          f (value (c : ℕ) i j, nm (c : ℕ) i j) := by
  rw [chunkCellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod,
    ← Finset.univ_sigma_univ, Finset.prod_sigma]
  refine prod_congr rfl fun c _ => ?_
  rw [Fintype.prod_prod_type]
  simp only [Function.comp_apply]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => ∏ j ∈ range (k c), f (value (c : ℕ) i j, nm (c : ℕ) i j)) m]
  exact prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range
    (fun j => f (value (c : ℕ) (i : ℕ) j, nm (c : ℕ) (i : ℕ) j)) (k c)

open Finset in
/-- **The copy constraints across chunks of varying widths.** Per-chunk one-row recurrences, the
rule chaining consecutive chunks, and the two boundary values make the whole table one running
product; two challenge root counts then give the multiset identity, and cells in a cycle of `σ`
hold equal values. The surviving branch is a vanishing factor at some cell. -/
theorem perm_copy_constraints_of_chunk_products {nc m : ℕ} {k : Fin nc → ℕ} (hnc : 0 < nc)
    (Z : ℕ → ℕ → Fp) (value nm sigmaName : ℕ → ℕ → ℕ → Fp) (beta gamma : Fp)
    (σ : Equiv.Perm ((c : Fin nc) × Fin m × Fin (k c)))
    (hσ : ∀ cell : (c : Fin nc) × Fin m × Fin (k c),
      sigmaName (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
        = nm ((σ cell).1 : ℕ) ((σ cell).2.1 : ℕ) ((σ cell).2.2 : ℕ))
    (hnm : Function.Injective fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
      nm (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))
    (hrec : ∀ c : Fin nc, ∀ i < m,
      Z (c : ℕ) (i + 1)
          * ∏ j ∈ range (k c), (value (c : ℕ) i j + beta * sigmaName (c : ℕ) i j + gamma)
        = Z (c : ℕ) i * ∏ j ∈ range (k c), (value (c : ℕ) i j + beta * nm (c : ℕ) i j + gamma))
    (hchain : ∀ c : ℕ, c + 1 < nc → Z (c + 1) 0 = Z c m)
    (hz0 : Z 0 0 = 1) (hzend : Z (nc - 1) m = 0 ∨ Z (nc - 1) m = 1)
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((chunkCellPairs nc m k value sigmaName).map (fun q => q.1 + q.2 * beta))
      ((chunkCellPairs nc m k value nm).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff (chunkCellPairs nc m k value sigmaName)
      (chunkCellPairs nc m k value nm)).coeff j))
    {x w : (c : Fin nc) × Fin m × Fin (k c)} (hxw : σ.SameCycle x w) :
    value (x.1 : ℕ) (x.2.1 : ℕ) (x.2.2 : ℕ) = value (w.1 : ℕ) (w.2.1 : ℕ) (w.2.2 : ℕ)
      ∨ ∃ cell : (c : Fin nc) × Fin m × Fin (k c),
          value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + beta * nm (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ) + gamma = 0 := by
  classical
  -- the whole-chunk products, extended past the last chunk so the chunk chain telescopes
  set A : ℕ → Fp := fun c =>
    if h : c < nc then
      ∏ i ∈ range m, ∏ j ∈ range (k ⟨c, h⟩), (value c i j + beta * nm c i j + gamma)
    else 1 with hA
  set B : ℕ → Fp := fun c =>
    if h : c < nc then
      ∏ i ∈ range m, ∏ j ∈ range (k ⟨c, h⟩), (value c i j + beta * sigmaName c i j + gamma)
    else 1 with hB
  set zc : ℕ → Fp := fun c => if c < nc then Z c 0 else Z (nc - 1) m with hzc
  have hrec' : ∀ c < nc, zc (c + 1) * B c = zc c * A c := by
    intro c hc
    have htel := telescope_running_product (Z c)
      (fun i => ∏ j ∈ range (k ⟨c, hc⟩), (value c i j + beta * nm c i j + gamma))
      (fun i => ∏ j ∈ range (k ⟨c, hc⟩), (value c i j + beta * sigmaName c i j + gamma))
      (fun i hi => hrec ⟨c, hc⟩ i hi)
    have hzcc : zc c = Z c 0 := by simp [hzc, hc]
    have hzcc1 : zc (c + 1) = Z c m := by
      rcases lt_or_ge (c + 1) nc with h1 | h1
      · simp only [hzc, if_pos h1]
        exact hchain c h1
      · have hce : c = nc - 1 := by omega
        subst hce
        have hif : ¬ (nc - 1 + 1 < nc) := by omega
        simp only [hzc, if_neg hif]
    rw [hzcc, hzcc1, hA, hB]
    simp only [dif_pos hc]
    exact htel
  rcases prod_eq_or_factor_eq_zero zc A B hrec' (by simp [hzc, hnc, hz0])
      (by simpa [hzc, lt_irrefl] using hzend) with hprod | ⟨c, hc, hzero⟩
  · -- the two whole-table products agree: cross to the multiset identity
    have hBP : ∏ c ∈ range nc, B c
        = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
            (value (c : ℕ) i j + beta * sigmaName (c : ℕ) i j + gamma) := by
      rw [← Fin.prod_univ_eq_prod_range B nc]
      exact prod_congr rfl fun c _ => by simp [hB, c.isLt]
    have hAP : ∏ c ∈ range nc, A c
        = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
            (value (c : ℕ) i j + beta * nm (c : ℕ) i j + gamma) := by
      rw [← Fin.prod_univ_eq_prod_range A nc]
      exact prod_congr rfl fun c _ => by simp [hA, c.isLt]
    have hprod' : ((chunkCellPairs nc m k value sigmaName).map
          (fun q => gamma + (q.1 + q.2 * beta))).prod
        = ((chunkCellPairs nc m k value nm).map (fun q => gamma + (q.1 + q.2 * beta))).prod := by
      rw [prod_map_chunkCellPairs, prod_map_chunkCellPairs]
      calc ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
              (gamma + (value (c : ℕ) i j + sigmaName (c : ℕ) i j * beta))
          = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
              (value (c : ℕ) i j + beta * sigmaName (c : ℕ) i j + gamma) :=
            prod_congr rfl fun c _ => prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
        _ = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
              (value (c : ℕ) i j + beta * nm (c : ℕ) i j + gamma) := by
            rw [← hBP, ← hAP]; exact hprod
        _ = ∏ c : Fin nc, ∏ i ∈ range m, ∏ j ∈ range (k c),
              (gamma + (value (c : ℕ) i j + nm (c : ℕ) i j * beta)) :=
            prod_congr rfl fun c _ => prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
    have hmulti := multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ hprod'
    refine Or.inl (perm_copy_constraints σ hnm
      (fun cell => value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)) ?_ hxw)
    have hmulti' : (Finset.univ.val.map
          (fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
            (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
              nm (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))))
        = Finset.univ.val.map
          (fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
            (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
              sigmaName (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))) := by
      have h := hmulti.symm
      simp only [chunkCellPairs] at h
      exact h
    calc (Finset.univ.val.map
          (fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
            (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
              nm (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))))
        = Finset.univ.val.map
          (fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
            (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
              sigmaName (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))) := hmulti'
      _ = Finset.univ.val.map
          (fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
            (value (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ),
              nm ((σ cell).1 : ℕ) ((σ cell).2.1 : ℕ) ((σ cell).2.2 : ℕ))) :=
          Multiset.map_congr rfl fun cell _ => by rw [hσ cell]
  · -- a factor on the identity-name side vanished: surface the cell
    rw [hA] at hzero
    have hc' : c < nc := mem_range.mp hc
    simp only [dif_pos hc'] at hzero
    obtain ⟨i, hi, h2⟩ := prod_eq_zero_iff.mp hzero
    obtain ⟨j, hj, h3⟩ := prod_eq_zero_iff.mp h2
    exact Or.inr ⟨⟨⟨c, hc'⟩, ⟨i, mem_range.mp hi⟩, ⟨j, mem_range.mp hj⟩⟩, h3⟩

/-- The chunk-cell identity name: row `ωⁱ`, global column `c·chunkLen + j`. halo2 offsets every
chunk by `chunkLen` even when the last chunk is shorter, so the global indices stay distinct. -/
noncomputable def chunkName (omega delta : Fp) (chunkLen : ℕ) : ℕ → ℕ → ℕ → Fp :=
  fun c i j => omega ^ i * delta ^ (c * chunkLen + j)

/-- The committed column value of chunk `c` at a cell. -/
noncomputable def chunkValue (omega : Fp) (cols : ℕ → List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → ℕ → Fp := fun c => rowValue omega (cols c)

/-- The permutation column value of chunk `c` at a cell — the name `σ` sends the cell to. -/
noncomputable def chunkSigma (omega : Fp) (cols : ℕ → List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → ℕ → Fp := fun c => rowSigmaName omega (cols c)

/-- **Name distinctness across chunks.** With every chunk width below `chunkLen`, the global column
indices `c·chunkLen + j` are distinct, and the coset facts about `ω` and `δ` separate the cells. This
discharges the injectivity hypothesis of the chunked endpoints for a concrete key. -/
theorem chunkName_injective_of_coset {omega delta : Fp} {nc m chunkLen : ℕ} {k : Fin nc → ℕ}
    (hk : ∀ c, k c ≤ chunkLen) (hdelta : delta ≠ 0) (homega : omega ^ m = 1)
    (horder : ∀ i i' : ℕ, i < m → i' < m → omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀ a b : ℕ, a < nc * chunkLen → b < nc * chunkLen → ∀ t : ℕ,
      delta ^ a = omega ^ t * delta ^ b → a = b) :
    Function.Injective fun cell : (c : Fin nc) × Fin m × Fin (k c) =>
      chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ) := by
  have hlt : ∀ cell : (c : Fin nc) × Fin m × Fin (k c),
      (cell.1 : ℕ) * chunkLen + (cell.2.2 : ℕ) < nc * chunkLen := by
    rintro ⟨c, i, j⟩
    have h1 : (j : ℕ) < chunkLen := lt_of_lt_of_le j.isLt (hk c)
    calc (c : ℕ) * chunkLen + (j : ℕ) < (c : ℕ) * chunkLen + chunkLen := by omega
      _ = ((c : ℕ) + 1) * chunkLen := by ring
      _ ≤ nc * chunkLen := Nat.mul_le_mul_right chunkLen c.isLt
  rintro ⟨c, i, j⟩ ⟨c', i', j'⟩ h
  simp only [chunkName] at h
  -- clear the row factor without dividing
  have hshift : delta ^ ((c : ℕ) * chunkLen + (j : ℕ))
      = omega ^ (m - (i : ℕ) + (i' : ℕ)) * delta ^ ((c' : ℕ) * chunkLen + (j' : ℕ)) := by
    have hmul := congrArg (fun v => omega ^ (m - (i : ℕ)) * v) h
    simp only at hmul
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt i.isLt), homega, one_mul] at hmul
    rw [hmul, ← mul_assoc, ← pow_add]
  have hcol : (c : ℕ) * chunkLen + (j : ℕ) = (c' : ℕ) * chunkLen + (j' : ℕ) :=
    hcoset _ _ (hlt ⟨c, i, j⟩) (hlt ⟨c', i', j'⟩) _ hshift
  -- base-chunkLen: the chunk and the in-chunk column separate
  have hjc : (j : ℕ) < chunkLen := lt_of_lt_of_le j.isLt (hk c)
  have hjc' : (j' : ℕ) < chunkLen := lt_of_lt_of_le j'.isLt (hk c')
  have hLpos : 0 < chunkLen := lt_of_le_of_lt (Nat.zero_le (j : ℕ)) hjc
  have hcc : (c : ℕ) = (c' : ℕ) := by
    have h1 : ((j : ℕ) + (c : ℕ) * chunkLen) / chunkLen = (c : ℕ) := by
      rw [Nat.add_mul_div_right _ _ hLpos, Nat.div_eq_of_lt hjc, Nat.zero_add]
    have h2 : ((j' : ℕ) + (c' : ℕ) * chunkLen) / chunkLen = (c' : ℕ) := by
      rw [Nat.add_mul_div_right _ _ hLpos, Nat.div_eq_of_lt hjc', Nat.zero_add]
    rw [← h1, ← h2]
    congr 1
    omega
  obtain hc : c = c' := Fin.ext hcc
  subst hc
  have hjj : (j : ℕ) = (j' : ℕ) := by omega
  obtain hj : j = j' := Fin.ext hjj
  subst hj
  have hii : (i : ℕ) = (i' : ℕ) := by
    refine horder _ _ i.isLt i'.isLt ?_
    exact mul_right_cancel₀ (pow_ne_zero _ hdelta) h
  obtain hi : i = i' := Fin.ext hii
  subst hi
  rfl

open Finset in
/-- **The copy constraints across every chunk, from the constraint identity.** Chunks of different
widths, each with its own running product: the step rules give the per-chunk recurrences, the
chaining rules link consecutive chunks, and the first and last boundary rules pin the whole chain —
every one of them located inside the deployed constraint list and read off the identity. The last
chunk's boundary is derived from the located end rule rather than assumed. -/
theorem deployed_copy_constraints_of_identity_chunks
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ) {nc m : ℕ} (hnc : 0 < nc)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n : ℕ} (hn : n ≠ 0) (p : Fin np)
    (hsets : sets p = deployedPermSets omega nc z lastP)
    (hchunks : chunks p = deployedPermChunks omega nc z lastP cols)
    (σ : Equiv.Perm ((c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length))
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ m) ≠ 0)
    (hlastEval : ∀ c, c + 1 < nc → ((lastP c).getD 0).eval (omega ^ 0) = (z c).eval (omega ^ m))
    (hσ : ∀ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
      chunkSigma omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
        = chunkName omega delta chunkLen ((σ cell).1 : ℕ) ((σ cell).2.1 : ℕ) ((σ cell).2.2 : ℕ))
    (hnm : Function.Injective
      fun cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length =>
        chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols)).map (fun q => q.1 + q.2 * beta))
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols))
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen))).coeff j))
    {x w : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length} (hxw : σ.SameCycle x w) :
    chunkValue omega cols (x.1 : ℕ) (x.2.1 : ℕ) (x.2.2 : ℕ)
        = chunkValue omega cols (w.1 : ℕ) (w.2.1 : ℕ) (w.2.2 : ℕ)
      ∨ ∃ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
          chunkValue omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + beta * chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + gamma = 0 := by
  have hall := constraints_dvd_of_good_y _ hpoly hn hidentity hgoodY
  have hmem : ∀ v : Polynomial Fp,
      v ∈ permutationExpressions (deployedPermSets omega nc z lastP)
        (deployedPermChunks omega nc z lastP cols) (C beta) (C gamma) X (C delta) chunkLen
        l0P lLastP lBlindP → (X ^ n - 1 : Polynomial Fp) ∣ v := by
    intro v hv
    refine hall v (mem_constraintPolys_of_mem_permutationExpressions fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP
      p ?_)
    rw [hsets, hchunks]
    exact hv
  refine perm_copy_constraints_of_chunk_products hnc (fun c i => (z c).eval (omega ^ i))
    (chunkValue omega cols) (chunkName omega delta chunkLen) (chunkSigma omega cols) beta gamma
    σ hσ hnm ?_ ?_ ?_ ?_ hgoodγ hgoodβ hxw
  · -- each chunk's step rule gives that chunk's recurrence
    intro c i hi
    have hstep := hmem _ (permChunkExpression_mem_permutationExpressions
      (deployedPermSets omega nc z lastP) (deployedPermChunks omega nc z lastP cols)
      (C beta) (C gamma) X (C delta) chunkLen l0P lLastP lBlindP (c := (c : ℕ))
      (by simp))
    rw [getElem_deployedPermChunks] at hstep
    have hr := perm_row_recurrence omega beta gamma delta chunkLen (c : ℕ) (z (c : ℕ))
      (lastP (c : ℕ)) (cols (c : ℕ)) lLastP lBlindP hstep (hrow i) (hactive i hi)
    simpa [chunkValue, chunkSigma, chunkName, rowValue, rowSigmaName] using hr
  · -- the chaining rule links consecutive chunks
    intro c hc1
    have hchainMem := hmem _ (chain_mem_permutationExpressions
      (deployedPermSets omega nc z lastP) (deployedPermChunks omega nc z lastP cols)
      (C beta) (C gamma) X (C delta) chunkLen l0P lLastP lBlindP (c := c)
      (by simpa using hc1))
    rw [getElem_deployedPermSets, getElem_deployedPermSets] at hchainMem
    have h := running_product_chain hchainMem (hrow 0) hl0
    simp only [permSetPolys] at h
    simpa using h.trans (by simpa using hlastEval c hc1)
  · -- the first-row rule pins the first chunk's running product to `1`
    have hstart := hmem _ (start_mem_permutationExpressions
      (deployedPermChunks omega nc z lastP cols) (C beta) (C gamma) X (C delta) chunkLen
      l0P lLastP lBlindP (head?_deployedPermSets omega hnc z lastP))
    simpa using running_product_start (by simpa using hstart) (hrow 0) hl0
  · -- the last chunk's boundary, read from the located end rule
    have hend := hmem _ (end_mem_permutationExpressions
      (deployedPermChunks omega nc z lastP cols) (C beta) (C gamma) X (C delta) chunkLen
      l0P lLastP lBlindP (getLast?_deployedPermSets omega hnc z lastP))
    simp only [permSetPolys_eval] at hend
    exact running_product_end hend (hrow m) hlast


open Finset in
/-- **The circuit's declared equalities across every chunk.** The chunked endpoint with the
permutation taken to be the one keygen builds from the circuit's copy constraints: by
`build_correct` its cycles are exactly the classes those constraints force, so the conclusion names
the equalities the circuit declared. -/
theorem deployed_declared_equalities_of_identity_chunks
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ) {nc m : ℕ} (hnc : 0 < nc)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n : ℕ} (hn : n ≠ 0) (p : Fin np)
    (hsets : sets p = deployedPermSets omega nc z lastP)
    (hchunks : chunks p = deployedPermChunks omega nc z lastP cols)
    (cs : List (((c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length)
      × ((c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length)))
    (hidentity : combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP = hpoly * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ m) ≠ 0)
    (hlastEval : ∀ c, c + 1 < nc → ((lastP c).getD 0).eval (omega ^ 0) = (z c).eval (omega ^ m))
    (hσ : ∀ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
      chunkSigma omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
        = chunkName omega delta chunkLen ((PermConstruction.build cs cell).1 : ℕ)
            ((PermConstruction.build cs cell).2.1 : ℕ) ((PermConstruction.build cs cell).2.2 : ℕ))
    (hnm : Function.Injective
      fun cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length =>
        chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols)).map (fun q => q.1 + q.2 * beta))
      ((chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkSigma omega cols))
      (chunkCellPairs nc m (fun c => (cols (c : ℕ)).length) (chunkValue omega cols)
        (chunkName omega delta chunkLen))).coeff j))
    {x w : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length}
    (hxw : Relation.EqvGen (fun a b => (a, b) ∈ cs) x w) :
    chunkValue omega cols (x.1 : ℕ) (x.2.1 : ℕ) (x.2.2 : ℕ)
        = chunkValue omega cols (w.1 : ℕ) (w.2.1 : ℕ) (w.2.2 : ℕ)
      ∨ ∃ cell : (c : Fin nc) × Fin m × Fin (cols (c : ℕ)).length,
          chunkValue omega cols (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + beta * chunkName omega delta chunkLen (cell.1 : ℕ) (cell.2.1 : ℕ) (cell.2.2 : ℕ)
            + gamma = 0 :=
  deployed_copy_constraints_of_identity_chunks omega beta gamma delta theta y chunkLen hnc z lastP
    cols fixedCols adviceCols instanceCols gates sets chunks lookups l0P lLastP lBlindP hpoly hn p
    hsets hchunks (PermConstruction.build cs) hidentity hgoodY hrow hactive hl0 hlast hlastEval
    hσ hnm hgoodγ hgoodβ ((PermConstruction.build_correct cs x w).mpr hxw)

end Zcash.Snark
