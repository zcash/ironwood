import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Zcash.Snark.Soundness.Argument.LookupAssembly
import Zcash.Snark.Soundness.Argument.PermutationRows
import Zcash.Snark.Soundness.Pricing.GoodChallenge

/-!
# The verifier's lookup constraints, read row by row

This is the lookup counterpart of `PermutationRows`.  It reads the five polynomials emitted by
`lookupExpressions` on the evaluation domain:

* the first two pin the running product at its endpoints;
* the third is the product recurrence;
* the fourth pins the first permuted-input value to the first permuted-table value;
* the fifth says each later permuted-input value either matches the table at that row or repeats
  the preceding input value.

The last two facts feed `Lookup.run_structure`; the first three telescope through
`RunningProduct.prod_eq_or_factor_eq_zero`.  The exceptional zero-factor branch is retained.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial Finset
open scoped ENNReal

@[simp] theorem lookupEvalPolys_productEval (omega : Fp) (z a s : CPoly) :
    (lookupEvalPolys omega z a s).productEval = z := rfl

@[simp] theorem lookupEvalPolys_permutedInputEval (omega : Fp) (z a s : CPoly) :
    (lookupEvalPolys omega z a s).permutedInputEval = a := rfl

@[simp] theorem lookupEvalPolys_permutedTableEval (omega : Fp) (z a s : CPoly) :
    (lookupEvalPolys omega z a s).permutedTableEval = s := rfl

/-- The lookup product's next evaluation is the next domain row. -/
theorem eval_lookupEvalPolys_productNextEval (omega : Fp) (z a s : CPoly) (i : ℕ) :
    ((lookupEvalPolys omega z a s).productNextEval).eval (omega ^ i)
      = z.eval (omega ^ (i + 1)) := by
  rw [lookupEvalPolys,
    eval_comp_rotate, pow_succ, _root_.mul_comm]

/-- On every non-first row, the inverse-rotated lookup input is the preceding row. -/
theorem eval_lookupEvalPolys_permutedInputInvEval_succ
    (omega : Fp) (z a s : CPoly) (homega : omega ≠ 0) (i : ℕ) :
    ((lookupEvalPolys omega z a s).permutedInputInvEval).eval (omega ^ (i + 1))
      = a.eval (omega ^ i) := by
  change eval (omega ^ (i + 1)) (comp a (C omega⁻¹ * X)) = eval (omega ^ i) a
  rw [eval_comp_rotate, pow_succ]
  congr 1
  field_simp

/-- Constraint three, evaluated at an active row, is the lookup running-product recurrence. -/
theorem lookup_product_row_recurrence
    (omega beta gamma : Fp) (z a s input table lLastP lBlindP : CPoly) {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣
      (z.comp (C omega * X) * (a + C beta) * (s + C gamma)
        - z * (input + C beta) * (table + C gamma))
        * (1 - (lLastP + lBlindP)))
    {i : ℕ} (hpow : (omega ^ i) ^ n = 1)
    (hactive : 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0) :
    z.eval (omega ^ (i + 1)) * (a.eval (omega ^ i) + beta)
        * (s.eval (omega ^ i) + gamma)
      = z.eval (omega ^ i) * (input.eval (omega ^ i) + beta)
        * (table.eval (omega ^ i) + gamma) := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_one, eval_comp_rotate,
    _root_.mul_comm omega] at hzero
  rcases mul_eq_zero.mp hzero with hrec | hact
  · exact sub_eq_zero.mp hrec
  · exact absurd hact hactive

/-- Constraint four pins the first permuted-input value to the first permuted-table value. -/
theorem lookup_run_start_of_dvd
    (a s l0P : CPoly) {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣ l0P * (a - s))
    {r : Fp} (hpow : r ^ n = 1) (hl0 : l0P.eval r ≠ 0) :
    a.eval r = s.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  rw [eval_mul, eval_sub] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hl0)

/-- Constraint five says an active permuted-input row either matches the table row or repeats its
predecessor. -/
theorem lookup_run_step_of_dvd
    (a s aPrev lLastP lBlindP : CPoly) {n : ℕ}
    (hdvd : (X ^ n - 1 : CPoly) ∣
      (a - s) * (a - aPrev) * (1 - (lLastP + lBlindP)))
    {r : Fp} (hpow : r ^ n = 1)
    (hactive : 1 - (lLastP.eval r + lBlindP.eval r) ≠ 0) :
    a.eval r = s.eval r ∨ a.eval r = aPrev.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  simp only [eval_mul, eval_sub, eval_one, eval_add] at hzero
  have hpairs := (mul_eq_zero.mp hzero).resolve_right hactive
  rcases mul_eq_zero.mp hpairs with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- The deployed run constraints imply the semantic run structure over all active lookup rows. -/
theorem lookup_run_structure_of_dvd
    (omega : Fp) (a s l0P lLastP lBlindP : CPoly) {n u : ℕ}
    (homega : omega ≠ 0)
    (hstart : (X ^ n - 1 : CPoly) ∣ l0P * (a - s))
    (hstep : (X ^ n - 1 : CPoly) ∣
      (a - s) * (a - a.comp (C omega⁻¹ * X)) * (1 - (lLastP + lBlindP)))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u + 1,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) :
    ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      a.eval (omega ^ (i : ℕ)) = s.eval (omega ^ (j : ℕ)) := by
  have h0 : a.eval (omega ^ (0 : ℕ)) = s.eval (omega ^ (0 : ℕ)) :=
    lookup_run_start_of_dvd a s l0P hstart (hrow 0) hl0
  apply run_structure
    (fun i : Fin (u + 1) => a.eval (omega ^ (i : ℕ)))
    (fun i : Fin (u + 1) => s.eval (omega ^ (i : ℕ)))
    0 h0 (Or.inl h0)
  intro i
  have hs := lookup_run_step_of_dvd a s (a.comp (C omega⁻¹ * X)) lLastP lBlindP
    hstep (hrow (i + 1)) (hactive (i + 1) (by omega))
  rcases hs with hs | ha
  · exact Or.inl hs
  · exact Or.inr (by
      simpa using ha.trans
        (by
          simpa [lookupEvalPolys] using
              (eval_lookupEvalPolys_permutedInputInvEval_succ omega 0 a s homega i)))

/-- Constraints one through three telescope to the whole-column lookup product identity, or expose
an input/table factor that vanished in the legitimate `z`-ends-at-zero branch. -/
theorem lookup_product_eq_or_factor_eq_zero
    (omega beta gamma : Fp) (z a s input table l0P lLastP lBlindP : CPoly)
    {n m : ℕ}
    (hproduct : (X ^ n - 1 : CPoly) ∣
      (z.comp (C omega * X) * (a + C beta) * (s + C gamma)
        - z * (input + C beta) * (table + C gamma))
        * (1 - (lLastP + lBlindP)))
    (hstart : (X ^ n - 1 : CPoly) ∣ l0P * (1 - z))
    (hend : (X ^ n - 1 : CPoly) ∣ lLastP * (z ^ 2 - z))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0)
    (hlast : lLastP.eval (omega ^ m) ≠ 0) :
    ((∏ i ∈ range m, (a.eval (omega ^ i) + beta) * (s.eval (omega ^ i) + gamma))
        = ∏ i ∈ range m,
          (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma))
      ∨ ∃ i ∈ range m,
          (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma) = 0 := by
  apply prod_eq_or_factor_eq_zero
    (fun i => z.eval (omega ^ i))
    (fun i => (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma))
    (fun i => (a.eval (omega ^ i) + beta) * (s.eval (omega ^ i) + gamma))
  · intro i hi
    simpa [_root_.mul_assoc] using
      lookup_product_row_recurrence omega beta gamma z a s input table lLastP lBlindP
        hproduct (hrow i) (hactive i hi)
  · exact running_product_start hstart (hrow 0) hl0
  · exact running_product_end (by simpa [_root_.mul_comm] using hend) (hrow m) hlast

/-- A polynomial column read over the first `m` powers of the evaluation-domain generator. -/
def lookupColumnRows (omega : Fp) (p : CPoly) (m : ℕ) : Fin m → Fp :=
  fun i => p.eval (omega ^ (i : ℕ))

/-- Challenge values that make one row of a compressed lookup column's additive factor vanish. -/
def lookupColumnZeroBadSet
    (omega : Fp) (p : CPoly) (m : ℕ) : Finset Fp :=
  additiveZeroBadSet (lookupColumnRows omega p m)

/-- Membership in a lookup-column zero set is exactly a vanishing row factor. -/
theorem mem_lookupColumnZeroBadSet_iff
    (omega : Fp) (p : CPoly) (m : ℕ) (challenge : Fp) :
    challenge ∈ lookupColumnZeroBadSet omega p m ↔
      ∃ i : Fin m, p.eval (omega ^ (i : ℕ)) + challenge = 0 := by
  exact mem_additiveZeroBadSet_iff (lookupColumnRows omega p m) challenge

/-- The zero-factor exclusion for one compressed lookup column costs at most one challenge value
per participating row. -/
theorem uniformChallenge_lookupColumnZeroBadSet
    (omega : Fp) (p : CPoly) (m : ℕ) :
    uniformChallenge.toOuterMeasure (lookupColumnZeroBadSet omega p m)
      ≤ (m : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  simpa using uniformChallenge_additiveZeroBadSet (lookupColumnRows omega p m)

/-- The five deployed lookup constraints for coherent base polynomials, each known to vanish on the
size-`n` evaluation domain.  This is the compact interface between family-level
`ConstraintSatisfaction` and the row-semantic endpoint below. -/
structure LookupConstraintsDvd (n : ℕ) (omega beta gamma : Fp)
    (z a s input table l0P lLastP lBlindP : CPoly) : Prop where
  start : (X ^ n - 1 : CPoly) ∣ l0P * (1 - z)
  finish : (X ^ n - 1 : CPoly) ∣ lLastP * (z ^ 2 - z)
  product : (X ^ n - 1 : CPoly) ∣
    (z.comp (C omega * X) * (a + C beta) * (s + C gamma)
      - z * (input + C beta) * (table + C gamma))
      * (1 - (lLastP + lBlindP))
  runStart : (X ^ n - 1 : CPoly) ∣ l0P * (a - s)
  runStep : (X ^ n - 1 : CPoly) ∣
    (a - s) * (a - a.comp (C omega⁻¹ * X)) * (1 - (lLastP + lBlindP))

open Finset in
/-- **The deployed lookup argument.** The verifier's five lookup constraints imply that every
compressed input row occurs in the compressed table, unless the running product ends on its
legitimate zero branch and therefore exposes a vanishing input/table challenge factor.

The root-set hypotheses price the two sampled challenges used to separate the paired product into
the permuted-input/input and permuted-table/table multiset identities. -/
theorem deployed_lookup_subset
    (omega beta gamma : Fp) (z a s input table l0P lLastP lBlindP : CPoly)
    {n u : ℕ}
    (hdvd : LookupConstraintsDvd n omega beta gamma z a s input table l0P lLastP lBlindP)
    (homega : omega ≠ 0)
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u + 1,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0)
    (hlast : lLastP.eval (omega ^ (u + 1)) ≠ 0)
    (hgoodGamma : gamma ∉ szBadSet
      (lookupProdDiffGamma
        (univ.val.map (lookupColumnRows omega a (u + 1)))
        (univ.val.map (lookupColumnRows omega s (u + 1)))
        (univ.val.map (lookupColumnRows omega input (u + 1)))
        (univ.val.map (lookupColumnRows omega table (u + 1))) beta))
    (hgoodBeta : ∀ j, beta ∉ szBadSet
      (lookupProdDiffCoeff
        (univ.val.map (lookupColumnRows omega a (u + 1)))
        (univ.val.map (lookupColumnRows omega s (u + 1)))
        (univ.val.map (lookupColumnRows omega input (u + 1)))
        (univ.val.map (lookupColumnRows omega table (u + 1))) j)) :
    (∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      lookupColumnRows omega input (u + 1) i = lookupColumnRows omega table (u + 1) j)
    ∨ ∃ i ∈ range (u + 1),
      (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma) = 0 := by
  rcases lookup_product_eq_or_factor_eq_zero omega beta gamma z a s input table
      l0P lLastP lBlindP hdvd.product hdvd.start hdvd.finish hrow hactive hl0 hlast with
    hprod | hzero
  · left
    have hprod' :
        (∏ i, (beta + lookupColumnRows omega a (u + 1) i))
            * (∏ i, (gamma + lookupColumnRows omega s (u + 1) i))
          = (∏ i, (beta + lookupColumnRows omega input (u + 1) i))
            * (∏ i, (gamma + lookupColumnRows omega table (u + 1) i)) := by
      simp only [lookupColumnRows]
      rw [Fin.prod_univ_eq_prod_range
          (fun i => beta + a.eval (omega ^ i)) (u + 1),
        Fin.prod_univ_eq_prod_range
          (fun i => gamma + s.eval (omega ^ i)) (u + 1),
        Fin.prod_univ_eq_prod_range
          (fun i => beta + input.eval (omega ^ i)) (u + 1),
        Fin.prod_univ_eq_prod_range
          (fun i => gamma + table.eval (omega ^ i)) (u + 1)]
      simpa [prod_mul_distrib, _root_.mul_assoc, _root_.add_comm] using hprod
    obtain ⟨hain, hstbl⟩ := lookup_multisets_of_diff_eq_zero
      (lookup_multisets_of_prod_eval_eq hgoodGamma hgoodBeta (by
        simpa [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def] using hprod'))
    exact fun i => lookup_subset_of_components hain hstbl
      (lookup_run_structure_of_dvd omega a s l0P lLastP lBlindP homega
        hdvd.runStart hdvd.runStep hrow hactive hl0) i
  · exact Or.inr hzero

/-- **The deployed lookup argument without a residual zero branch.** Avoiding one `β` value per
compressed input row and one `γ` value per compressed table row rules out the legitimate
zero-product case left by `deployed_lookup_subset`, so every compressed input row occurs in the
compressed table.  These exclusions are schedule-correct: the compressed columns are fixed after
`θ`, before `β` and `γ` are squeezed. -/
theorem deployed_lookup_subset_of_nonzero_challenges
    (omega beta gamma : Fp) (z a s input table l0P lLastP lBlindP : CPoly)
    {n u : ℕ}
    (hdvd : LookupConstraintsDvd n omega beta gamma z a s input table l0P lLastP lBlindP)
    (homega : omega ≠ 0)
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u + 1,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0)
    (hlast : lLastP.eval (omega ^ (u + 1)) ≠ 0)
    (hgoodGamma : gamma ∉ szBadSet
      (lookupProdDiffGamma
        (univ.val.map (lookupColumnRows omega a (u + 1)))
        (univ.val.map (lookupColumnRows omega s (u + 1)))
        (univ.val.map (lookupColumnRows omega input (u + 1)))
        (univ.val.map (lookupColumnRows omega table (u + 1))) beta))
    (hgoodBeta : ∀ j, beta ∉ szBadSet
      (lookupProdDiffCoeff
        (univ.val.map (lookupColumnRows omega a (u + 1)))
        (univ.val.map (lookupColumnRows omega s (u + 1)))
        (univ.val.map (lookupColumnRows omega input (u + 1)))
        (univ.val.map (lookupColumnRows omega table (u + 1))) j))
    (hinputNonzero : beta ∉ lookupColumnZeroBadSet omega input (u + 1))
    (htableNonzero : gamma ∉ lookupColumnZeroBadSet omega table (u + 1)) :
    ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      lookupColumnRows omega input (u + 1) i =
        lookupColumnRows omega table (u + 1) j := by
  rcases deployed_lookup_subset omega beta gamma z a s input table l0P lLastP lBlindP
      hdvd homega hrow hactive hl0 hlast hgoodGamma hgoodBeta with hsubset | hzero
  · exact hsubset
  · exfalso
    rcases hzero with ⟨i, hi, hfactor⟩
    rcases mul_eq_zero.mp hfactor with hinput | htable
    · apply hinputNonzero
      rw [mem_lookupColumnZeroBadSet_iff]
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hinput⟩
    · apply htableNonzero
      rw [mem_lookupColumnZeroBadSet_iff]
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, htable⟩

end Zcash.Snark
