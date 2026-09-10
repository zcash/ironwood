import Zcash.Snark.Soundness.Canonical.PolynomialEnvironment
import Zcash.Circuits.Integration.CircuitSatisfaction
import Clean.Halo2.TopLevel

/-!
# Canonical polynomial-to-row Clean environments

Decoded member columns are polynomials.  Clean circuit semantics reads columns by integer row.
This file supplies the canonical adapter: row `r` of a column polynomial is its evaluation at
`ω^r`.  Integer rows make rotations definitionally uniform, including negative rotations.
The underlying row polynomials and their algebra are verifier-native and live in
`Zcash.Snark.Soundness.Canonical.PolynomialEnvironment`.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

/-- Reduce an integer domain-row exponent to its canonical natural representative. -/
theorem zpow_eq_pow_natMod
    (omega : Fp) (n : ℕ) (hn : 0 < n)
    (hroot : omega ^ n = 1) (row : ℤ) :
    omega ^ row = omega ^ row.natMod n := by
  have homega : omega ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn.ne'] at hroot
    exact zero_ne_one hroot
  calc
    omega ^ row =
        omega ^ (row % (n : ℤ) + (n : ℤ) * (row / (n : ℤ))) := by
      rw [Int.emod_add_mul_ediv]
    _ = omega ^ (row % (n : ℤ)) := by
      rw [zpow_add₀ homega, zpow_mul, show omega ^ (n : ℤ) = 1 by
        simpa using hroot, one_zpow, _root_.mul_one]
    _ = omega ^ row.natMod n := by
      rw [← zpow_natCast]
      congr 1
      simp only [Int.natMod]
      exact (Int.toNat_of_nonneg
        (Int.emod_nonneg row
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)))).symm

/-- Read fixed, advice, and instance column polynomials on the multiplicative `ω` row domain. -/
def polynomialEnvironment
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    Environment Fp where
  get column row :=
    match column.kind with
    | .fixed => (fixedCols column.index).eval (omega ^ row)
    | .advice => (adviceCols column.index).eval (omega ^ row)
    | .instance => (instanceCols column.index).eval (omega ^ row)
  usableRows := usableRows

/--
Resolve only the proof-varying part of a Clean top-level environment.

Fixed columns and usable rows intentionally do not appear here: the
`TopLevelCircuit` compiler supplies them when constructing its environment.
-/
def resolverAssignment
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) : ProofAssignment Fp where
  advice := fun column row =>
    (poly (.adviceCol proofIndex column.index)).eval (omega ^ row)
  inst := fun column row =>
    (poly (.instanceCol proofIndex column.index)).eval (omega ^ row)

@[simp] theorem resolverAssignment_advice
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) (column : Column .advice) (row : ℤ) :
    (resolverAssignment omega poly proofIndex).advice column row =
      (poly (.adviceCol proofIndex column.index)).eval (omega ^ row) :=
  rfl

@[simp] theorem resolverAssignment_instance
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) (column : Column .instance) (row : ℤ) :
    (resolverAssignment omega poly proofIndex).inst column row =
      (poly (.instanceCol proofIndex column.index)).eval (omega ^ row) :=
  rfl

@[simp] theorem polynomialEnvironment_usableRows
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).usableRows =
      usableRows := rfl

@[simp] theorem polynomialEnvironment_fixed
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .fixed) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).fixed column row =
      (fixedCols column.index).eval (omega ^ row) := rfl

@[simp] theorem polynomialEnvironment_advice
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .advice) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).advice column row =
      (adviceCols column.index).eval (omega ^ row) := rfl

@[simp] theorem polynomialEnvironment_instance
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .instance) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).inst column row =
      (instanceCols column.index).eval (omega ^ row) := rfl

/-- Natural row reads agree with the usual evaluation-domain spelling `ω ^ row`. -/
theorem polynomialEnvironment_fixed_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .fixed) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).fixed
        column (row : ℤ) =
      (fixedCols column.index).eval (omega ^ row) := by simp

theorem polynomialEnvironment_advice_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .advice) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).advice
        column (row : ℤ) =
      (adviceCols column.index).eval (omega ^ row) := by simp

theorem polynomialEnvironment_instance_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .instance) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).inst
        column (row : ℤ) =
      (instanceCols column.index).eval (omega ^ row) := by simp

/-- A rotated advice query is evaluation of the standard rotated column polynomial at the base
row point. -/
theorem polynomialEnvironment_query_advice
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .advice) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.advice column rotation) =
      ((adviceCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_advice, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- The fixed-column rotation adapter. -/
theorem polynomialEnvironment_query_fixed
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .fixed) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.fixed column rotation) =
      ((fixedCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_fixed, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- The instance-column rotation adapter. -/
theorem polynomialEnvironment_query_instance
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .instance) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.instance column rotation) =
      ((instanceCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_instance, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- The canonical Clean environment selected by a commitment-ID polynomial resolver for one
sub-proof. -/
def resolverEnvironment
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ) :
    Environment Fp :=
  polynomialEnvironment vk.omega usableRows
    (fun column => poly (.fixedCol column))
    (fun column => poly (.adviceCol p column))
    (fun column => poly (.instanceCol p column))

@[simp] theorem resolverEnvironment_fixed
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .fixed) (row : ℤ) :
    (resolverEnvironment vk poly p usableRows).fixed column row =
      (poly (.fixedCol column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem resolverEnvironment_advice
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .advice) (row : ℤ) :
    (resolverEnvironment vk poly p usableRows).advice column row =
      (poly (.adviceCol p column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem resolverEnvironment_instance
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .instance) (row : ℤ) :
    (resolverEnvironment vk poly p usableRows).inst column row =
      (poly (.instanceCol p column.index)).eval (vk.omega ^ row) := rfl

/--
Once commitment binding identifies a resolved instance column with its canonical
zero-padded row polynomial, the Clean environment reads the supplied public values.
-/
theorem resolverEnvironment_instance_of_rowPolynomial
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .instance) (values : List Fp)
    (hpoly : poly (.instanceCol p column.index) =
      instanceRowPolynomial (2 ^ shape.k) vk.omega values)
    (hrows : Function.Injective
      fun i : Fin (2 ^ shape.k) => vk.omega ^ (i : ℕ))
    (row : Fin (2 ^ shape.k)) :
    (resolverEnvironment vk poly p usableRows).inst column (row : ℤ) =
      values.getD (row : ℕ) 0 := by
  rw [resolverEnvironment_instance, hpoly]
  simpa using instanceRowPolynomial_eval hrows row

end Zcash.Snark
