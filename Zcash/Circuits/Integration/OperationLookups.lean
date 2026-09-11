import Zcash.Circuits.Halo2.LookupOperations
import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Canonical.LookupRows
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Zcash.Common.RelationWitness

/-!
# Tuple compression and activation-indexed collision budgets

Outside the roots of the compression-polynomial difference, equality of compressed
values implies equality of the original tuples. Each activation's collision set
ranges over usable table rows; the polynomial bridge transports these budgets to
the compiler's row semantics.
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

/-- All `θ` collisions between one enabled input tuple and the usable table rows. -/
def EnabledLookup.thetaBadSet
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) : Finset Fp :=
  (Finset.range env.usableRows).biUnion fun row =>
    tupleCompressionBadSet
      (lookup.inputValues place env) (lookup.tableValues env row)

/-- Avoiding an enabled lookup's combined set is exactly avoiding every usable-row tuple
collision. -/
theorem EnabledLookup.not_mem_thetaBadSet_iff
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta : Fp) :
    theta ∉ lookup.thetaBadSet place env ↔
      ∀ row < env.usableRows,
        theta ∉ tupleCompressionBadSet
          (lookup.inputValues place env) (lookup.tableValues env row) := by
  simp [EnabledLookup.thetaBadSet]

/-- Compute avoidance of one enabled lookup's `θ` surface by checking its finite usable rows.
No root set is enumerated. -/
def EnabledLookup.thetaAvoidance?
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta : Fp) :
    Option (PLift (theta ∉ lookup.thetaBadSet place env)) :=
  match hrows : finForallOption (fun row : Fin env.usableRows =>
      szBadSetAvoidance?
        (foldPoly (lookup.inputValues place env)
          - foldPoly (lookup.tableValues env row.1)) theta) with
  | none => none
  | some rows => some ⟨(lookup.not_mem_thetaBadSet_iff place env theta).2
      fun row hrow => by
        simpa [tupleCompressionBadSet, tupleCompressionBadSet] using
          (rows ⟨row, hrow⟩).down⟩

theorem EnabledLookup.thetaAvoidance?_isSome_of
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta : Fp)
    (hgood : theta ∉ lookup.thetaBadSet place env) :
    (lookup.thetaAvoidance? place env theta).isSome := by
  have hrowsSpec := (lookup.not_mem_thetaBadSet_iff place env theta).1 hgood
  have hrows : ∀ row : Fin env.usableRows,
      (szBadSetAvoidance?
        (foldPoly (lookup.inputValues place env)
          - foldPoly (lookup.tableValues env row.1)) theta).isSome :=
    fun row => (szBadSetAvoidance?_isSome_iff _ _).2 (by
      simpa [tupleCompressionBadSet] using hrowsSpec row.1 row.2)
  have hall := finForallOption_isSome_of _ hrows
  unfold EnabledLookup.thetaAvoidance?
  generalize hresult : finForallOption (fun row : Fin env.usableRows =>
      szBadSetAvoidance?
        (foldPoly (lookup.inputValues place env)
          - foldPoly (lookup.tableValues env row.1)) theta) = result at hall ⊢
  cases result <;> simp_all

/-- One enabled lookup's tuple-collision budget is at most
`usableRows × inputArity`. -/
theorem EnabledLookup.thetaBadSet_card_le
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp)
    (hlength : ∀ row < env.usableRows,
      (lookup.inputValues place env).length = (lookup.tableValues env row).length) :
    (lookup.thetaBadSet place env).card ≤
      env.usableRows * (lookup.inputValues place env).length := by
  refine le_trans Finset.card_biUnion_le ?_
  calc
    ∑ row ∈ Finset.range env.usableRows,
        (tupleCompressionBadSet
          (lookup.inputValues place env) (lookup.tableValues env row)).card
      ≤ ∑ _row ∈ Finset.range env.usableRows,
          (lookup.inputValues place env).length := by
            exact Finset.sum_le_sum fun row hrow =>
              tupleCompressionBadSet_card_le_length
                (hlength row (Finset.mem_range.mp hrow))
    _ = env.usableRows * (lookup.inputValues place env).length := by simp

/-- Uniform `θ` hits one enabled lookup's tuple-collision set with probability at most
`usableRows × inputArity / |Fp|`. -/
theorem uniformChallenge_enabledLookupThetaBadSet
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp)
    (hlength : ∀ row < env.usableRows,
      (lookup.inputValues place env).length = (lookup.tableValues env row).length) :
    uniformChallenge.toOuterMeasure (lookup.thetaBadSet place env)
      ≤ (env.usableRows * (lookup.inputValues place env).length : ℝ≥0∞) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast lookup.thetaBadSet_card_le place env hlength


end Zcash.Snark
