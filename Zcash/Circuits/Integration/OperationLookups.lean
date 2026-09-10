import Zcash.Circuits.Integration.CircuitSatisfaction
import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Canonical.LookupRows
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Zcash.Common.RelationWitness

/-!
# Enabled operation lookups and tuple-compression soundness

This is the operation-trace side of the lookup bridge.  It extracts every
`RegionOperation.enableLookup` together with its region placement context and proves that
satisfying the extracted list is exactly the lookup constraint family.

The second half is independent of the concrete VK representation.  It turns membership of a
`θ`-compressed input value in a compressed table column back into equality of the original tuples,
outside the explicit root set of their compression-polynomial difference.  A concrete layout/VK
adapter only has to identify the compressed polynomial evaluations with the values defined here.
-/

namespace Zcash.Snark

open Halo2 CompPoly CompPoly.CPolynomial
open scoped ENNReal

set_option maxHeartbeats 20000

/-- One lookup activation in the placed operation stream. -/
structure EnabledLookup (F : Type) where
  argument : LookupArgument F
  enabled : List Selector
  region : RegionIndex
  row : ℕ

namespace EnabledLookup

variable {F : Type} [FiniteField F]

/-- Selector leaves occurring in an expression, with multiplicity and syntax order. -/
def expressionSelectorLeaves : Expression F Query → List Selector
  | .var (.selector selector) => [selector]
  | .var _ => []
  | .const _ => []
  | .add left right =>
      expressionSelectorLeaves left ++ expressionSelectorLeaves right
  | .mul left right =>
      expressionSelectorLeaves left ++ expressionSelectorLeaves right

/-- Selector leaves occurring in this lookup's input tuple. -/
def inputSelectorLeaves (lookup : EnabledLookup F) : List Selector :=
  lookup.argument.inputs.flatMap expressionSelectorLeaves

/-- The selector valuation carried by this particular lookup activation. -/
def selectorValue (lookup : EnabledLookup F) (index : ℕ) : F :=
  if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0

@[simp] theorem selectorValue_mk
    (argument : LookupArgument F) (enabled : List Selector)
    (region : RegionIndex) (row index : ℕ) :
    selectorValue
        ({ argument := argument, enabled := enabled, region := region, row := row } :
          EnabledLookup F) index =
      if ∃ selector ∈ enabled, selector.index = index then 1 else 0 := rfl

/-- The lookup input tuple at the activation's placed row. -/
def inputValues (place : RegionIndex → ℕ) (env : Environment F)
    (lookup : EnabledLookup F) : List F :=
  lookup.argument.inputs.map
    (Expression.eval
      (Query.eval env
        (fun index =>
          if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0)
        (place lookup.region + lookup.row : ℕ)))

/-- The lookup table tuple at one absolute usable row. -/
def tableValues (env : Environment F) (lookup : EnabledLookup F)
    (tableRow : ℕ) : List F :=
  lookup.argument.tables.map
    (Expression.eval
      (Query.eval env
        (fun index =>
          if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0)
        (tableRow : ℤ)))

/-- Clean's semantic lookup relation for one extracted activation. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (lookup : EnabledLookup F) : Prop :=
  ∃ tableRow : ℕ, tableRow < env.usableRows ∧
    lookup.inputValues place env = lookup.tableValues env tableRow

end EnabledLookup

/-- Lookup activations in one region, retaining the region index used by placement. -/
def regionEnabledLookups {F : Type} (self : RegionIndex) :
    RegionOperations F → List (EnabledLookup F)
  | [] => []
  | .enableLookup argument enabled row :: rest =>
      ⟨argument, enabled, self, row⟩ :: regionEnabledLookups self rest
  | _ :: rest => regionEnabledLookups self rest

/-- Lookup activations in a complete layouter stream, with region indices threaded exactly as in
`Halo2.Constraints`. -/
def operationEnabledLookups {F : Type} :
    Operations F → RegionIndex → List (EnabledLookup F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionEnabledLookups i body ++ operationEnabledLookups rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationEnabledLookups rest i
  | .loadTable _ _ :: rest, i => operationEnabledLookups rest i

/-- The reduced synthesis summary counts exactly the lookup activations extracted
from one region. -/
theorem regionEnabledLookups_length {F : Type}
    (self : RegionIndex) (body : RegionOperations F) :
    (regionEnabledLookups self body).length =
      (FloorPlanner.regionSynthesisSummary body).lookupActivationCount := by
  induction body with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [regionEnabledLookups, FloorPlanner.regionSynthesisSummary,
          FloorPlanner.RegionSynthesisSummary.combine_lookupActivationCount,
          FloorPlanner.RegionSynthesisSummary.ofOperation_lookupActivationCount,
          FloorPlanner.regionOperationLookupActivationCount,
          List.length_cons, inductionHypothesis] <;>
        omega

/-- The reduced synthesis summary counts exactly the lookup activations extracted
from a complete operation stream. -/
theorem operationEnabledLookups_length {F : Type}
    (operations : Operations F) (initial : RegionIndex) :
    (operationEnabledLookups operations initial).length =
      (FloorPlanner.synthesisSummary operations).lookupActivationCount := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [operationEnabledLookups, FloorPlanner.synthesisSummary,
          List.length_append, regionEnabledLookups_length,
          inductionHypothesis,
          FloorPlanner.SynthesisSummary.combine_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofRegion_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofInstanceRow_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofTableValues_lookupActivationCount,
          Nat.zero_add]

/-- Membership in a region's extracted lookup list is exactly membership of the
corresponding raw `.enableLookup` operation, with the enclosing region retained. -/
theorem mem_regionEnabledLookups_iff
    {F : Type} (lookup : EnabledLookup F)
    (self : RegionIndex) (body : RegionOperations F) :
    lookup ∈ regionEnabledLookups self body ↔
      lookup.region = self ∧
        RegionOperation.enableLookup lookup.argument lookup.enabled lookup.row ∈
          body := by
  rcases lookup with ⟨argument, enabled, region, row⟩
  induction body with
  | nil =>
      simp [regionEnabledLookups]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [regionEnabledLookups]
      all_goals aesop

/--
An extracted lookup points to the exact indexed region body containing its raw
activation operation.
-/
theorem mem_operationEnabledLookups_iff
    {F : Type} (lookup : EnabledLookup F)
    (operations : Operations F) (initial : RegionIndex) :
    lookup ∈ operationEnabledLookups operations initial ↔
      ∃ body,
        (lookup.region, body) ∈ (indexedRegions operations initial).1 ∧
          RegionOperation.enableLookup lookup.argument lookup.enabled lookup.row ∈
            body := by
  induction operations generalizing initial with
  | nil =>
      simp [operationEnabledLookups, indexedRegions]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [operationEnabledLookups, indexedRegions,
          mem_regionEnabledLookups_iff]
      all_goals aesop

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- The lookup-family projection of one region is exactly satisfaction of its extracted lookup
activations. -/
theorem region_lookup_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    regionConstraints .lookup place self env ops ↔
      (regionEnabledLookups self ops).Forall (EnabledLookup.Satisfied place env) := by
  induction ops with
  | nil => simp [regionConstraints, regionEnabledLookups]
  | cons op rest ih =>
      cases op <;>
        simp_all [regionConstraints, regionConstraint, RegionOperation.Constraints,
          regionEnabledLookups, EnabledLookup.Satisfied, EnabledLookup.inputValues,
          EnabledLookup.tableValues]

/-- The complete lookup-family projection is exactly satisfaction of all lookup activations in the
placed operation stream. -/
theorem lookup_constraints_iff_enabledLookups
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    constraints .lookup place env ops i ↔
      (operationEnabledLookups ops i).Forall (EnabledLookup.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [constraints, operationEnabledLookups]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [constraints, ih, region_lookup_constraints_iff]
          simp [operationEnabledLookups, List.forall_append]
      | constrainInstance cell col row =>
          rw [constraints, ih]
          simp [operationEnabledLookups]
      | loadTable table values =>
          rw [constraints, ih]
          simp [operationEnabledLookups]

end CircuitConstraintFamily

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

/-- One extracted lookup is satisfied once its compressed input occurs in the compressed table and
`θ` avoids the collision set for the selected tuple pair. -/
theorem EnabledLookup.satisfied_of_compressed
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta : Fp)
    (input table : ℕ → Fp)
    (hinput :
      compressValues theta (lookup.inputValues place env) =
        input (place lookup.region + lookup.row))
    (htable : ∀ row < env.usableRows,
      compressValues theta (lookup.tableValues env row) = table row)
    (hlength : ∀ row < env.usableRows,
      (lookup.inputValues place env).length = (lookup.tableValues env row).length)
    (hsubset : ∃ row < env.usableRows,
      input (place lookup.region + lookup.row) = table row)
    (hgood : ∀ row < env.usableRows,
      theta ∉ tupleCompressionBadSet
        (lookup.inputValues place env) (lookup.tableValues env row)) :
    lookup.Satisfied place env := by
  rcases hsubset with ⟨row, hrow, heq⟩
  refine ⟨row, hrow, ?_⟩
  apply eq_of_compressValues_eq_of_not_mem (hlength row hrow) (hgood row hrow)
  rw [hinput, htable row hrow, heq]

/-- The compressed membership bridge with one combined, priced `θ` exclusion for the activation. -/
theorem EnabledLookup.satisfied_of_compressed_avoiding
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta : Fp)
    (input table : ℕ → Fp)
    (hinput :
      compressValues theta (lookup.inputValues place env) =
        input (place lookup.region + lookup.row))
    (htable : ∀ row < env.usableRows,
      compressValues theta (lookup.tableValues env row) = table row)
    (hlength : ∀ row < env.usableRows,
      (lookup.inputValues place env).length = (lookup.tableValues env row).length)
    (hsubset : ∃ row < env.usableRows,
      input (place lookup.region + lookup.row) = table row)
    (hgood : theta ∉ lookup.thetaBadSet place env) :
    lookup.Satisfied place env :=
  lookup.satisfied_of_compressed place env theta input table
    hinput htable hlength hsubset
    ((lookup.not_mem_thetaBadSet_iff place env theta).mp hgood)

/-- Specialize the scalar bridge to the row functions returned by the deployed lookup theorem. -/
theorem EnabledLookup.satisfied_of_deployed_subset
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (lookup : EnabledLookup Fp) (theta omega : Fp)
    (input table : CPoly) (u : ℕ)
    (husable : env.usableRows = u + 1)
    (hrow : place lookup.region + lookup.row < u + 1)
    (hinput :
      compressValues theta (lookup.inputValues place env) =
        input.eval (omega ^ (place lookup.region + lookup.row)))
    (htable : ∀ row < env.usableRows,
      compressValues theta (lookup.tableValues env row) =
        table.eval (omega ^ row))
    (hlength : ∀ row < env.usableRows,
      (lookup.inputValues place env).length = (lookup.tableValues env row).length)
    (hsubset : ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      lookupColumnRows omega input (u + 1) i =
        lookupColumnRows omega table (u + 1) j)
    (hgood : ∀ row < env.usableRows,
      theta ∉ tupleCompressionBadSet
        (lookup.inputValues place env) (lookup.tableValues env row)) :
    lookup.Satisfied place env := by
  apply lookup.satisfied_of_compressed place env theta
      (fun row => input.eval (omega ^ row))
      (fun row => table.eval (omega ^ row))
      hinput htable hlength
  · obtain ⟨tableRow, heq⟩ :=
      hsubset ⟨place lookup.region + lookup.row, hrow⟩
    exact ⟨tableRow, by simpa [husable] using tableRow.isLt, by
      simpa [lookupColumnRows] using heq⟩
  · exact hgood

/-- The concrete data needed to connect one enabled Clean lookup to a deployed scalar lookup
endpoint.  Keeping it as a record makes the operation-list bridge readable and isolates the later
VK/layout coherence proof. -/
structure EnabledLookup.DeployedWitness
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (theta : Fp) (lookup : EnabledLookup Fp) where
  omega : Fp
  input : CPoly
  table : CPoly
  u : ℕ
  usableRows : env.usableRows = u + 1
  activationRow : place lookup.region + lookup.row < u + 1
  inputEval :
    compressValues theta (lookup.inputValues place env) =
      input.eval (omega ^ (place lookup.region + lookup.row))
  tableEval : ∀ row < env.usableRows,
    compressValues theta (lookup.tableValues env row) =
      table.eval (omega ^ row)
  tupleLength : ∀ row < env.usableRows,
    (lookup.inputValues place env).length = (lookup.tableValues env row).length
  scalarSubset : ∀ row : Fin (u + 1), ∃ tableRow : Fin (u + 1),
    lookupColumnRows omega input (u + 1) row =
      lookupColumnRows omega table (u + 1) tableRow
  thetaGood : theta ∉ lookup.thetaBadSet place env

/-- A deployed witness discharges the exact Clean semantics of its enabled lookup. -/
theorem EnabledLookup.DeployedWitness.satisfied
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {theta : Fp} {lookup : EnabledLookup Fp}
    (witness : lookup.DeployedWitness place env theta) :
    lookup.Satisfied place env := by
  apply lookup.satisfied_of_deployed_subset
    place env theta witness.omega witness.input witness.table witness.u
    witness.usableRows witness.activationRow witness.inputEval witness.tableEval
    witness.tupleLength witness.scalarSubset
  exact (lookup.not_mem_thetaBadSet_iff place env theta).mp witness.thetaGood

/-- The generic compressed-membership bridge, phrased as the lookup field of full circuit
satisfaction.  Concrete resolver/VK work supplies the scalar columns and the four per-activation
coherence premises. -/
theorem lookup_constraints_of_compressed
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex) (theta : Fp)
    (hlookup : ∀ lookup ∈ operationEnabledLookups ops i,
      ∃ input table : ℕ → Fp,
        compressValues theta (lookup.inputValues place env) =
            input (place lookup.region + lookup.row) ∧
        (∀ row < env.usableRows,
          compressValues theta (lookup.tableValues env row) = table row) ∧
        (∀ row < env.usableRows,
          (lookup.inputValues place env).length = (lookup.tableValues env row).length) ∧
        (∃ row < env.usableRows,
          input (place lookup.region + lookup.row) = table row) ∧
        (∀ row < env.usableRows,
          theta ∉ tupleCompressionBadSet
            (lookup.inputValues place env) (lookup.tableValues env row))) :
    CircuitConstraintFamily.constraints .lookup place env ops i := by
  rw [CircuitConstraintFamily.lookup_constraints_iff_enabledLookups]
  rw [List.forall_iff_forall_mem]
  intro lookup hmem
  rcases hlookup lookup hmem with
    ⟨input, table, hinput, htable, hlength, hsubset, hgood⟩
  exact lookup.satisfied_of_compressed
    place env theta input table hinput htable hlength hsubset hgood

/-- The operation-list lookup field obtained directly from deployed scalar lookup subsets.  The
remaining premises are precisely the representation boundary: identify each activation with its
input/table polynomials and show that polynomial row evaluation is the compression of the Clean
tuple at that row. -/
theorem lookup_constraints_of_deployed_subsets
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex) (theta : Fp)
    (hlookup : ∀ lookup ∈ operationEnabledLookups ops i,
      ∃ omega : Fp, ∃ input table : CPoly, ∃ u : ℕ,
        env.usableRows = u + 1 ∧
        place lookup.region + lookup.row < u + 1 ∧
        compressValues theta (lookup.inputValues place env) =
          input.eval (omega ^ (place lookup.region + lookup.row)) ∧
        (∀ row < env.usableRows,
          compressValues theta (lookup.tableValues env row) =
            table.eval (omega ^ row)) ∧
        (∀ row < env.usableRows,
          (lookup.inputValues place env).length = (lookup.tableValues env row).length) ∧
        (∀ row : Fin (u + 1), ∃ tableRow : Fin (u + 1),
          lookupColumnRows omega input (u + 1) row =
            lookupColumnRows omega table (u + 1) tableRow) ∧
        (∀ row < env.usableRows,
          theta ∉ tupleCompressionBadSet
            (lookup.inputValues place env) (lookup.tableValues env row))) :
    CircuitConstraintFamily.constraints .lookup place env ops i := by
  rw [CircuitConstraintFamily.lookup_constraints_iff_enabledLookups]
  rw [List.forall_iff_forall_mem]
  intro lookup hmem
  rcases hlookup lookup hmem with
    ⟨omega, input, table, u, husable, hrow, hinput, htable, hlength, hsubset, hgood⟩
  exact lookup.satisfied_of_deployed_subset
    place env theta omega input table u husable hrow hinput htable hlength hsubset hgood

/-- A concise operation-list bridge using one structured deployed witness per enabled lookup. -/
theorem lookup_constraints_of_deployed_witnesses
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex) (theta : Fp)
    (witness : ∀ lookup ∈ operationEnabledLookups ops i,
      EnabledLookup.DeployedWitness place env theta lookup) :
    CircuitConstraintFamily.constraints .lookup place env ops i := by
  rw [CircuitConstraintFamily.lookup_constraints_iff_enabledLookups]
  rw [List.forall_iff_forall_mem]
  intro lookup hmem
  exact (witness lookup hmem).satisfied

end Zcash.Snark
