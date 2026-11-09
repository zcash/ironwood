import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Canonical.LookupRows
import Zcash.Common.RelationWitness

/-!
# Tuple compression and finite collision families

Outside the roots of the compression-polynomial difference, equality of compressed
values implies equality of the original tuples. The collision family is indexed by arbitrary tuple comparisons, independent of
circuit compilation.
-/

namespace Zcash.Snark

open Halo2 CompPoly CompPoly.CPolynomial
open scoped ENNReal

set_option maxHeartbeats 20000

/-! ## Compression soundness for one tuple comparison -/

/-- Compress already evaluated tuple entries with the verifier's left-to-right `θ` fold. -/
def compressValues (theta : Fp) (values : List Fp) : Fp :=
  values.foldl (fun acc value => acc * theta + value) 0

/-- `foldPoly` is the symbolic compression polynomial. -/
theorem eval_foldPoly_eq_compressValues (values : List Fp) (theta : Fp) :
    (foldPoly values).eval theta = compressValues theta values :=
  eval_foldPoly values theta

/-- Equal-length tuple encodings are equal as polynomials only when the tuples are equal. -/
theorem foldPoly_injective_of_length_eq
    {left right : List Fp} (hlength : left.length = right.length)
    (hpoly : foldPoly left = foldPoly right) :
    left = right := by
  induction left using List.reverseRecOn generalizing right with
  | nil =>
      have hzero : right.length = 0 := by simpa using hlength.symm
      have hright : right = [] := List.eq_nil_of_length_eq_zero hzero
      exact hright.symm
  | append_singleton left value ih =>
      induction right using List.reverseRecOn with
      | nil => simp at hlength
      | append_singleton right value' =>
          have hpolyP : (foldPoly left).toPoly * Polynomial.X + Polynomial.C value
              = (foldPoly right).toPoly * Polynomial.X + Polynomial.C value' := by
            simpa [foldPoly_concat] using congrArg CPolynomial.toPoly hpoly
          have hvalue : value = value' := by
            have hcoeff := congrArg (fun p : Polynomial Fp => p.coeff 0) hpolyP
            simpa [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.mul_coeff_zero]
              using hcoeff
          have hmul : (foldPoly left).toPoly * Polynomial.X
              = (foldPoly right).toPoly * Polynomial.X := by
            rw [hvalue] at hpolyP
            exact add_right_cancel hpolyP
          have hfold : foldPoly left = foldPoly right := by
            apply CPolynomial.toPoly_injective
            apply sub_eq_zero.mp
            apply (mul_eq_zero.mp ?_).resolve_right Polynomial.X_ne_zero
            rw [sub_mul, hmul, sub_self]
          have hlength' : left.length = right.length := by simpa using hlength
          rw [ih hlength' hfold, hvalue]

/-- The `θ` values on which two concrete tuples have the same compression despite being unequal. -/
def tupleCompressionBadSet
    (left right : List Fp) : Finset Fp :=
  szBadSet (foldPoly left - foldPoly right)

/-- Outside the explicit collision set, compressed equality of equal-length tuples lifts to tuple
equality. -/
theorem eq_of_compressValues_eq_of_not_mem
    {left right : List Fp} {theta : Fp}
    (hlength : left.length = right.length)
    (hgood : theta ∉ tupleCompressionBadSet left right)
    (heval : compressValues theta left = compressValues theta right) :
    left = right := by
  by_contra hne
  have hpoly : foldPoly left - foldPoly right ≠ 0 := by
    rw [sub_ne_zero]
    exact fun heq => hne (foldPoly_injective_of_length_eq hlength heq)
  apply (not_mem_szBadSet.mp hgood) hpoly
  rw [eval_sub, eval_foldPoly_eq_compressValues, eval_foldPoly_eq_compressValues, heval, sub_self]

/-- For unequal, equal-length tuples, the collision set contains fewer values than the tuple
length. -/
theorem tupleCompressionBadSet_card_lt
    {left right : List Fp} (hlength : left.length = right.length)
    (hne : left ≠ right) :
    (tupleCompressionBadSet left right).card < left.length := by
  have hleft : left ≠ [] := by
    intro hempty
    apply hne
    have hright : right = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hempty] using hlength.symm
    exact hempty.trans hright.symm
  have hright : right ≠ [] := by
    intro hempty
    apply hne
    have hleft : left = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hempty] using hlength
    exact hleft.trans hempty.symm
  refine lt_of_le_of_lt (szBadSet_card_le _) ?_
  refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
  · exact natDegree_foldPoly_lt hleft
  · simpa [hlength] using natDegree_foldPoly_lt hright

/-- Equal-length tuples exclude at most their arity many `θ` values (and strictly fewer when they
differ). -/
theorem tupleCompressionBadSet_card_le_length
    {left right : List Fp} (hlength : left.length = right.length) :
    (tupleCompressionBadSet left right).card ≤ left.length := by
  by_cases heq : left = right
  · subst right
    calc
      (tupleCompressionBadSet left left).card ≤ 0 := by
        simpa [tupleCompressionBadSet] using
          (szBadSet_card_le (0 : CPoly))
      _ ≤ left.length := Nat.zero_le _
  · exact (tupleCompressionBadSet_card_lt hlength heq).le


/-- The shared challenge must avoid collisions in every tuple comparison. -/
def tupleCollisionSet {ι : Type*} [Fintype ι]
    (left right : ι → List Fp) : Finset Fp :=
  Finset.univ.biUnion fun i => tupleCompressionBadSet (left i) (right i)

theorem not_mem_tupleCollisionSet_iff {ι : Type*} [Fintype ι]
    (left right : ι → List Fp) (theta : Fp) :
    theta ∉ tupleCollisionSet left right ↔
      ∀ i, theta ∉ tupleCompressionBadSet (left i) (right i) := by
  classical
  simp [tupleCollisionSet]


/-- Union-bound cost of equal-length tuple comparisons. -/
theorem tupleCollisionSet_card_le {ι : Type*} [Fintype ι]
    (left right : ι → List Fp)
    (hlength : ∀ i, (left i).length = (right i).length) :
    (tupleCollisionSet left right).card ≤ ∑ i, (left i).length := by
  classical
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun i _ => tupleCompressionBadSet_card_le_length (hlength i))

theorem uniformChallenge_tupleCollisionSet {ι : Type*} [Fintype ι]
    (left right : ι → List Fp)
    (hlength : ∀ i, (left i).length = (right i).length) :
    uniformChallenge.toOuterMeasure (tupleCollisionSet left right) ≤
      (∑ i, (left i).length : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast tupleCollisionSet_card_le left right hlength

end Zcash.Snark
