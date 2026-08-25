import Zcash.Snark.Keygen.Certificate
import Zcash.Circuits.Action.PlannerTrace
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.Pricing.DegreeWalk

/-!
# The single-Action captured key's static checks and degree budget

These captured facts validate the one-Action query layouts, domain, and `x`-squeeze degree cap
`D = Dq = 20470`.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Arithmetic
open Zcash.Circuits.Action (actionCircuit)

/-! Small record projections are exposed once so arithmetic proofs do not unfold the captured
key's 193 gate expressions.  These are definitional facts about the captured data. -/

theorem vk_n_eq : vk.n = 2048 := rfl

set_option maxRecDepth 100000 in
theorem vk_gates_length : vk.gates.length = 193 := rfl

theorem vk_permutationChunks_length : vk.permutationChunks.length = 3 := rfl

theorem vk_adviceQueryLayout_length : vk.adviceQueryLayout.length = 25 := rfl

theorem vk_instanceQueryLayout_length : vk.instanceQueryLayout.length = 1 := rfl

theorem vk_fixedQueryLayout_length : vk.fixedQueryLayout.length = 29 := rfl

private theorem action_domainExponent_eq : actionCircuit.domainExponent = 11 := by
  rw [Halo2.TopLevelCircuit.domainExponent,
    Zcash.Circuits.Action.actionCircuit_shape_eq,
    Zcash.Circuits.Action.actionShape_k]

private theorem vk_domain_eq :
    (vk.omega, vk.n) =
      (actionCircuit.omega, actionCircuit.n) := by
  have hscalars :=
    congrArg (fun bundle => bundle.2.2.2.1) Keygen.certificate
  apply Prod.ext
  · exact (congrArg (fun scalars => scalars.1) hscalars).symm
  · exact (congrArg (fun scalars => scalars.2.1) hscalars).symm

/-- The captured advice query layout covers the shape's advice query count. -/
theorem vk_advice_layout_length : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length := by
  rw [vk_adviceQueryLayout_length]
  norm_num [shape]

/-- The captured instance query layout covers the shape's instance query count. -/
theorem vk_instance_layout_length :
    shape.numInstanceQueries ≤ vk.instanceQueryLayout.length := by
  rw [vk_instanceQueryLayout_length]
  norm_num [shape]

/-- The captured fixed query layout covers the shape's fixed query count. -/
theorem vk_fixed_layout_length : shape.numFixedQueries ≤ vk.fixedQueryLayout.length := by
  rw [vk_fixedQueryLayout_length]
  norm_num [shape]

/-- The captured `ω` has order dividing `n`. -/
theorem vk_omega_order : vk.omega ^ vk.n = 1 := by
  have hdomain := vk_domain_eq
  simp only [Prod.mk.injEq] at hdomain
  rw [hdomain.1, hdomain.2]
  rw [Halo2.TopLevelCircuit.n_eq_two_pow_domainExponent]
  exact (omegaOf_isPrimitiveRoot actionCircuit.domainExponent (by
    rw [action_domainExponent_eq]
    norm_num)).pow_eq_one

/-- The captured domain size does not vanish in the scalar field. -/
theorem vk_n_cast_ne_zero : ((vk.n : ℕ) : Fp) ≠ 0 := by
  rw [vk_n_eq]
  simpa using domainSize_cast_ne_zero 11 (by norm_num)

/-- Every captured gate clears the degree cap at `B = 2047`. -/
theorem vk_gates_degree_le : ∀ e ∈ vk.gates, e.degreeBound * 2047 ≤ 20470 := by
  native_decide

/-- Every captured permutation chunk has width at most `7`. -/
theorem vk_chunk_width_le : ∀ c ∈ vk.permutationChunks, c.length ≤ 7 := by
  native_decide

/-- Every captured lookup input expression clears the compression cap. -/
theorem vk_lookup_input_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupInputExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- Every captured lookup table expression clears the compression cap. -/
theorem vk_lookup_table_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupTableExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- The captured quotient tail fits the budget. -/
theorem vk_quotient_tail_le :
    vk.n * shape.numQuotientPieces + (2 ^ shape.k - 1) ≤ 20470 := by
  rw [vk_n_eq]
  norm_num [shape]

/-- The captured `n − 1` fits the opening degree. -/
theorem vk_n_pred_le : vk.n - 1 ≤ 2047 := by
  rw [vk_n_eq]

/-- The captured opening degree: `2^k − 1 ≤ 2047`. -/
theorem shape_k_pred_le : 2 ^ shape.k - 1 ≤ 2047 := by
  norm_num [shape]

end Zcash.Snark.Fixture
