import Zcash.Circuits.Integration.CircuitSatisfaction
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Clean.Halo2.Keygen.GateProjection
import Zcash.Snark.Soundness.Argument.PermutationRows

/-!
# Enabled operation gates

This file is the gate analogue of `OperationLookups`.  It extracts every
`RegionOperation.enableGate` with its placement context and proves that satisfaction of
those activations is exactly the gate constraint family.

`EnabledGate.PolynomialWitness` is the representation boundary to the deployed
constraint split. For each enabled Clean constraint it identifies a member of the
selected proof's polynomial gate family and transports verifier-side vanishing to
the Clean enabled-gate semantics. Divisibility by `X^n - 1` then supplies that
verifier-side vanishing on every domain row.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

/-- One custom-gate activation in the placed operation stream. -/
structure EnabledGate (F : Type) where
  gate : Gate F
  region : RegionIndex
  row : ℕ

namespace EnabledGate

variable {F : Type} [FiniteField F]

/-- Clean's semantic relation for one enabled gate. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (enabled : EnabledGate F) : Prop :=
  enabled.gate.constraints.Forall fun constraint =>
    constraint.poly.eval
      (Query.eval env
        (fun index => if index = enabled.gate.selector.index then 1 else 0)
        (place enabled.region + enabled.row : ℕ)) = 0

end EnabledGate

/-- Gate activations in one region, retaining the region index used by placement. -/
def regionEnabledGates {F : Type} (self : RegionIndex) :
    RegionOperations F → List (EnabledGate F)
  | [] => []
  | .enableGate gate row :: rest =>
      ⟨gate, self, row⟩ :: regionEnabledGates self rest
  | _ :: rest => regionEnabledGates self rest

/-- Gate activations in a complete layouter stream, with exact region-index threading. -/
def operationEnabledGates {F : Type} :
    Operations F → RegionIndex → List (EnabledGate F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionEnabledGates i body ++ operationEnabledGates rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationEnabledGates rest i
  | .loadTable _ _ :: rest, i => operationEnabledGates rest i

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region's gate-family projection is exactly its extracted enabled gates. -/
theorem region_gate_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    regionConstraints .gate place self env ops ↔
      (regionEnabledGates self ops).Forall (EnabledGate.Satisfied place env) := by
  induction ops with
  | nil => simp [regionConstraints, regionEnabledGates]
  | cons op rest ih =>
      cases op <;>
        simp_all [regionConstraints, regionConstraint, RegionOperation.Constraints,
          regionEnabledGates, EnabledGate.Satisfied]

/-- The complete gate-family projection is satisfaction of all extracted activations. -/
theorem gate_constraints_iff_enabledGates
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    constraints .gate place env ops i ↔
      (operationEnabledGates ops i).Forall (EnabledGate.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [constraints, operationEnabledGates]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [constraints, ih, region_gate_constraints_iff]
          simp [operationEnabledGates, List.forall_append]
      | constrainInstance cell col row =>
          rw [constraints, ih]
          simp [operationEnabledGates]
      | loadTable table values =>
          rw [constraints, ih]
          simp [operationEnabledGates]

end CircuitConstraintFamily

namespace EnabledGate

/-- One enabled Clean constraint represented by a deployed gate-family polynomial. -/
structure PolynomialWitness
    {np : ℕ} (M : ConstraintPolyModel np) (proofIndex : Fin np)
    (omega : Fp) (place : RegionIndex → ℕ) (env : Environment Fp)
    (enabled : EnabledGate Fp) (constraint : Constraint Fp) where
  polynomial : CPoly
  member : polynomial ∈ M.gateConstraints proofIndex
  zero_imp :
    polynomial.eval (omega ^ (place enabled.region + enabled.row)) = 0 →
      constraint.poly.eval
        (Query.eval env
          (fun index => if index = enabled.gate.selector.index then 1 else 0)
          (place enabled.region + enabled.row : ℕ)) = 0

/-- Deployed gate divisibility plus evaluation coherence satisfies one Clean activation. -/
theorem satisfied_of_polynomial_witnesses
    {np n : ℕ} {M : ConstraintPolyModel np} {proofIndex : Fin np}
    {omega : Fp} {place : RegionIndex → ℕ} {env : Environment Fp}
    {enabled : EnabledGate Fp}
    (satisfaction : ConstraintSatisfaction M n)
    (domain : ∀ row : ℕ, (omega ^ row) ^ n = 1)
    (witness : ∀ constraint ∈ enabled.gate.constraints,
      PolynomialWitness M proofIndex omega place env enabled constraint) :
    enabled.Satisfied place env := by
  rw [EnabledGate.Satisfied, List.forall_iff_forall_mem]
  intro constraint hconstraint
  let w := witness constraint hconstraint
  have hpoly : w.polynomial.eval
      (omega ^ (place enabled.region + enabled.row)) = 0 :=
    eval_eq_zero_of_dvd_vanishing
    (satisfaction.gates proofIndex w.polynomial w.member)
    (domain (place enabled.region + enabled.row))
  exact w.zero_imp hpoly

end EnabledGate

/-- Build the complete gate field from one polynomial witness per enabled constraint. -/
theorem gate_constraints_of_polynomial_witnesses
    {np n : ℕ} (M : ConstraintPolyModel np) (proofIndex : Fin np)
    (omega : Fp) (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex)
    (satisfaction : ConstraintSatisfaction M n)
    (domain : ∀ row : ℕ, (omega ^ row) ^ n = 1)
    (witness : ∀ enabled ∈ operationEnabledGates ops i,
      ∀ constraint ∈ enabled.gate.constraints,
        EnabledGate.PolynomialWitness
          M proofIndex omega place env enabled constraint) :
    CircuitConstraintFamily.constraints .gate place env ops i := by
  rw [CircuitConstraintFamily.gate_constraints_iff_enabledGates]
  rw [List.forall_iff_forall_mem]
  intro enabled henabled
  exact enabled.satisfied_of_polynomial_witnesses satisfaction domain
    (witness enabled henabled)

end Zcash.Snark
