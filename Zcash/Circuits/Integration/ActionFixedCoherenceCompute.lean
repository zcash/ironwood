import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Snark.Keygen.Lagrange
import Mathlib.Util.AssertNoSorry

/-!
# Interim closed computations for Action fixed-column coherence

These certificates unblock the Action integration while the generic layout
compiler is being equipped with structural consistency theorems.  They are
deliberately finite failure-list checks rather than opaque proofs of the final
coherence record.

Both checks are **INTERIM**:

* query coverage should follow from query registration;
* fixed realization should be decomposed across region cell-disjointness,
  region-local writes, tables, constants, selector packing, and generic
  last-write/dedup/scatter semantics.

Delete these computations once those compiler theorems construct the same facts.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (derivedUrsGLagrange derivedUrsGLagrange_length omegaOf)

open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionFixedCoherence

open Zcash.Snark.Keygen Polynomial

/--
**INTERIM:** every Action fixed column currently requested by
`TopLevelFixedCoherence` occurs in its compiler-derived fixed-query layout.
-/
theorem queryCoverageFailures_eq_nil :
    interimFixedQueryCoverageFailures actionCircuit = [] := by
  native_decide

/-- Query coverage extracted from the finite interim diagnostic. -/
theorem queryLayout :
    ∀ column,
      column < actionCircuit.pinnedCS.numFixedColumns →
        ∃ rotation,
          (column, rotation) ∈
            actionCircuit.pinnedCS.fixedQueryLayout :=
  fixedQueryCoverage_of_interimFailures_eq_nil
    actionCircuit queryCoverageFailures_eq_nil

/-- The same interim diagnostic rules out out-of-range fixed-query entries. -/
theorem queryLayoutBounded :
    ∀ column rotation,
      (column, rotation) ∈
          actionCircuit.pinnedCS.fixedQueryLayout →
        column < actionCircuit.pinnedCS.numFixedColumns :=
  fixedQueryBounded_of_interimFailures_eq_nil
    actionCircuit queryCoverageFailures_eq_nil

/--
**INTERIM:** the final dense Action fixed rows realize every table, region-fixed,
and packed-selector entry consumed by Clean constraint semantics.
-/
theorem realizationFailures_eq_nil :
    interimFixedRealizationFailures actionCircuit = [] := by
  native_decide

/-- Sparse-to-dense realization extracted from the finite interim diagnostic. -/
theorem realizes :
    ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        row < 2 ^ actionCircuit.domainExponent ∧
          column <
            actionCircuit.pinnedCS.numFixedColumns ∧
          (actionCircuit.fixedRows.getD column []).getD row 0 =
            (value : Fp) :=
  fixedRowsRealize_of_interimFailures_eq_nil
    actionCircuit realizationFailures_eq_nil

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

/--
Construct the Action fixed-coherence package from generic Lagrange-basis setup
facts.  Query coverage and sparse-to-dense realization are discharged by the two
interim certificates above; row shape, commitments, and query counts remain
generic consequences of `TopLevelCircuit.toVerifierKey`.

The remaining `hgenerators` premise is about the supplied URS, not the Action
circuit layout.
-/
def ofKeygen
    (pp : ProofParams) (urs : URS G)
    (hk : actionCircuit.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial
            (actionCircuit.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp))))) :
    TopLevelFixedCoherence actionCircuit pp urs :=
  TopLevelFixedCoherence.ofKeygen
    actionCircuit pp urs hk hlen hgenerators
    (by
      intro column hcolumn
      rw [actionCircuit.toVerifierKey_fixedQueryLayout_derived]
      change ∃ rotation,
        (column, rotation) ∈
          ActionPermutationDomain.derivedPinnedCS.fixedQueryLayout
      rw [ActionPermutationDomain.fixedQueryLayout_eq]
      exact queryLayout column hcolumn)
    (by
      intro column rotation hentry
      rw [actionCircuit.toVerifierKey_fixedQueryLayout_derived] at hentry
      change
        (column, rotation) ∈
          ActionPermutationDomain.derivedPinnedCS.fixedQueryLayout at hentry
      rw [ActionPermutationDomain.fixedQueryLayout_eq] at hentry
      exact queryLayoutBounded column rotation hentry)
    (by
      intro column row value hentry
      exact realizes column row value hentry)

/--
Construct Action fixed coherence directly from the symbolically proved
Lagrange-basis FFT specification. The only remaining computations are the
prominently interim layout failure lists above.
-/
def ofDerived
    (pp : ProofParams) (urs : URS G)
    (hk : actionCircuit.domainExponent = urs.k) :
    TopLevelFixedCoherence actionCircuit pp urs := by
  have hkUrs : urs.k ≤ 32 := by
    rw [← hk]
    exact Nat.le_of_lt_succ ActionPermutationDomain.domainExponent_lt
  have homega :
      (actionCircuit.toVerifierKey pp urs).omega =
        omegaOf urs.k := by
    change
      omegaOf actionCircuit.domainExponent =
        omegaOf urs.k
    rw [hk]
  apply ofKeygen pp urs hk (derivedUrsGLagrange_length urs)
  intro i
  simpa only [homega] using
    Keygen.ofPrefix_setup_of_closed urs hkUrs
      (Keygen.derivedUrsGLagrange_generator_eq urs hkUrs) i
      (by
        rw [derivedUrsGLagrange_length]
        exact i.isLt)

assert_no_sorry queryCoverageFailures_eq_nil
assert_no_sorry queryLayout
assert_no_sorry realizationFailures_eq_nil
assert_no_sorry realizes
assert_no_sorry ofDerived

end ActionFixedCoherence

end Zcash.Snark
