import Zcash.Circuits.Halo2.CompiledGates
import Zcash.Circuits.Halo2.FieldSupport
import Zcash.Snark.Soundness.Argument.PermutationRows
import Zcash.Circuits.Integration.PolynomialQueries
import Zcash.Circuits.Integration.TopLevelConstraintModel

/-!
# Generic top-level gate bridge

Polynomial divisibility supplies vanishing on domain rows. Query-feed interpretation
and fixed-column binding transport this to the compiler's row semantics; selector
compression and source gate soundness belong to `Circuits/Halo2`.
-/

open Zcash.Arithmetic (omegaOf pastaDomain_omega_eq)

namespace Halo2.TopLevelCircuit

open Zcash.Arithmetic (omegaOf scalarFieldOrder deltaFp)
open Zcash Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}

/-- The polynomial query feeds interpret the circuit-derived pinned query state. -/
theorem polynomialQueries_interpret_pinned
    [CircuitFieldSupport top]
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (usableRows row : ℕ) :
    Interprets
      (pinnedQueryState top.pinnedCS)
      (fun query =>
        (fixedQueryFeedOfResolver
          (top.toVerifierKey urs) poly query).eval
          (top.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (Query.eval
        (polynomialEnvironmentOfCommitments
          (top.toVerifierKey urs) poly proofIndex usableRows)
        (fun _ => 0) row) := by
  have homega : top.omega ≠ 0 := CircuitFieldSupport.omega_ne_zero top
  have hfinal := polynomialQueryFeeds_interpret
    (top.toVerifierKey urs) poly proofIndex usableRows
    (fun _ => 0) row
    (by simpa only [top.toVerifierKey_omega] using homega)
    (pinnedQueryState top.pinnedCS)
    (by
      simp only [top.toVerifierKey_adviceQueryLayout,
        TopLevelCircuit.adviceQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_fixedQueryLayout,
        TopLevelCircuit.fixedQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_instanceQueryLayout,
        TopLevelCircuit.instanceQueryLayout, pinnedQueryState])
    (top.toVerifierKey_adviceQueryCount urs)
    (top.toVerifierKey_fixedQueryCount urs)
    (top.toVerifierKey_instanceQueryCount urs)
  simpa only [top.toVerifierKey_omega] using hfinal

/-- Polynomial evaluation commutes with lifting a verifier expression by `C`. -/
private theorem eval_map_C
    (fixed advice instanceFeed : ℕ → CPoly)
    (expression : Expr Fp) (x : Fp) :
    ((expression.map C).eval fixed advice instanceFeed).eval x =
      expression.eval
        (fun query => (fixed query).eval x)
        (fun query => (advice query).eval x)
        (fun query => (instanceFeed query).eval x) := by
  induction expression <;> simp_all [Expr.map, Expr.eval]

/-- Polynomial gate divisibility establishes the compiled row predicate. All
selector and source-operation reasoning is handled by the Halo2 compiler theorem. -/
theorem gatesCompiled_of_constraintSatisfaction
    {k : ℕ} [CircuitFieldSupport top]
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction : ConstraintSatisfaction (top.constraintModel pp urs ch poly) top.n)
    (hencoding : top.FixedColumnEncoding poly) :
    top.GatesCompiled (polynomialAssignment top.omega poly proofIndex) := by
  intro expression hmember row _
  obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hmember
  let gate := top.pinnedCS.gates[index].toExpr
  let polynomial := (gate.map C).eval
    (fixedQueryFeedOfResolver (top.toVerifierKey urs) poly)
    (adviceQueryFeedOfResolver (top.toVerifierKey urs) poly proofIndex)
    (instanceQueryFeedOfResolver (top.toVerifierKey urs) poly proofIndex)
  have hgate : gate ∈ (top.toVerifierKey urs).gates := by
    rw [top.toVerifierKey_gates, top.verifierCS_gates]
    exact List.mem_map.mpr ⟨_, List.getElem_mem hindex, rfl⟩
  have hpoly : polynomial ∈ (top.constraintModel pp urs ch poly).gateConstraints proofIndex := by
    rw [top.constraintModel_eq_constraintModelOfResolver, ConstraintPolyModel.gateConstraints_eq]
    exact List.mem_map.mpr ⟨gate.map C, List.mem_map.mpr ⟨gate, hgate, rfl⟩, rfl⟩
  have hzero := eval_eq_zero_of_dvd_vanishing (satisfaction.gates proofIndex polynomial hpoly)
    (show (top.omega ^ row) ^ top.n = 1 by
      rw [← pow_mul, Nat.mul_comm, pow_mul, top.omega_pow_n, one_pow])
  rw [eval_map_C, RichExpression.eval_toExpr] at hzero
  rw [top.pinnedCS_gates_eval_of_interprets _ _ _ _ _
    (top.polynomialQueries_interpret_pinned poly proofIndex
      (top.usableRowsAt top.domainExponent) row)] at hzero
  rwa [top.polynomialEnvironmentOfCommitments_eq_environment urs poly proofIndex hencoding] at hzero

end Halo2.TopLevelCircuit
