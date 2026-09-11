import Zcash.Circuits.Halo2.ConstraintFamilies
import Zcash.Arithmetic

/-!
# Fixed-data requirements in the operation stream

Fixed assignments and lookup-table loads are the circuit-fixed part of Clean's
authoritative semantics.  This file extracts both forms into one list and proves that
their satisfaction is exactly the fixed constraint family.

The fixed-layout compiler uses this characterization to establish fixed constraints
from its sparse assignments, including the default-fill rows of loaded tables.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- One fixed-data obligation declared by synthesis. -/
inductive FixedRequirement (F : Type) where
  | assignment (region : RegionIndex) (column : Column .fixed) (row : ℕ) (value : F)
  | table (column : TableColumn) (values : List F)

namespace FixedRequirement

variable {F : Type} [FiniteField F]

/-- The exact Clean semantics of one extracted fixed-data obligation. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F) :
    FixedRequirement F → Prop
  | .assignment region column row value =>
      env.fixed column (place region + row : ℕ) = value
  | .table column values =>
      (∀ row : ℕ, row < values.length →
        env.fixed column.inner (row : ℤ) = values[row]!) ∧
      (values ≠ [] → ∀ row : ℕ, values.length ≤ row → row < env.usableRows →
        env.fixed column.inner (row : ℤ) = values[0]!)

end FixedRequirement

/-- Fixed assignments in one region. -/
def regionFixedRequirements {F : Type} (self : RegionIndex) :
    RegionOperations F → List (FixedRequirement F)
  | [] => []
  | .assignFixed column row value :: rest =>
      .assignment self column row value :: regionFixedRequirements self rest
  | _ :: rest => regionFixedRequirements self rest

/-- Fixed assignments and table loads in one complete operation stream. -/
def operationFixedRequirements {F : Type} :
    Operations F → RegionIndex → List (FixedRequirement F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionFixedRequirements i body ++ operationFixedRequirements rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationFixedRequirements rest i
  | .loadTable column values :: rest, i =>
      .table column values :: operationFixedRequirements rest i

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region's fixed-family projection is exactly its extracted assignments. -/
theorem region_fixed_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    regionConstraints .fixed place self env ops ↔
      (regionFixedRequirements self ops).Forall
        (FixedRequirement.Satisfied place env) := by
  induction ops with
  | nil => simp [regionConstraints, regionFixedRequirements]
  | cons op rest ih =>
      cases op <;>
        simp_all [regionConstraints, regionConstraint, RegionOperation.Constraints,
          regionFixedRequirements, FixedRequirement.Satisfied, Environment.get_fixed]

/-- The complete fixed-family projection is satisfaction of every extracted requirement. -/
theorem fixed_constraints_iff_requirements
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    constraints .fixed place env ops i ↔
      (operationFixedRequirements ops i).Forall
        (FixedRequirement.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [constraints, operationFixedRequirements]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [constraints, ih, region_fixed_constraints_iff]
          simp [operationFixedRequirements, List.forall_append]
      | constrainInstance cell col row =>
          rw [constraints, ih]
          simp [operationFixedRequirements]
      | loadTable column values =>
          rw [constraints, ih]
          simp [operationFixedRequirements, FixedRequirement.Satisfied]

end CircuitConstraintFamily

/-- Build the full fixed family from one witness per extracted requirement. -/
theorem fixed_constraints_of_requirements
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex)
    (witness : ∀ requirement ∈ operationFixedRequirements ops i,
      requirement.Satisfied place env) :
    CircuitConstraintFamily.constraints .fixed place env ops i := by
  rw [CircuitConstraintFamily.fixed_constraints_iff_requirements]
  exact List.forall_iff_forall_mem.mpr witness

end Zcash.Snark
