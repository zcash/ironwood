import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Clean.Halo2.Operations
import Zcash.Arithmetic

/-!
# Full Halo2 circuit satisfaction, split by constraint family

The SNARK constraint polynomial separates custom gates, the permutation argument, and lookup
arguments.  Clean's operation semantics, however, exposes one authoritative
`Halo2.Constraints` predicate.  This file gives that predicate a lossless family decomposition:

* `gate` — enabled custom-gate polynomials;
* `copy` — equality, constant, and instance copies;
* `lookup` — enabled lookup membership;
* `fixed` — fixed assignments and loaded-table contents.

Witness-only advice assignments belong to no family because their constraint is `True`.  The
decomposition does not weaken or replace Clean semantics:
`FullCircuitSatisfaction.iff_constraints` proves exact equivalence.
-/

namespace Zcash.Snark

open Halo2

/-- The four semantic families carried by a complete circuit-satisfaction result. -/
inductive CircuitConstraintFamily where
  | gate
  | copy
  | lookup
  | fixed
deriving DecidableEq, Repr

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region operation's contribution to a selected constraint family. -/
def regionConstraint (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperation F → Prop
  | op@(.enableGate _ _) =>
      if family = .gate then op.Constraints place self env else True
  | op@(.constrainEqual _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.constrainConstant _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.constrainInstance _ _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.enableLookup _ _ _) =>
      if family = .lookup then op.Constraints place self env else True
  | op@(.assignFixed _ _ _) =>
      if family = .fixed then op.Constraints place self env else True
  | .assignAdvice _ _ _ => True

/-- A region operation satisfies all four family projections exactly when it satisfies Clean's
authoritative operation constraint. -/
theorem regionOperation_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (op : RegionOperation F) :
    op.Constraints place self env ↔
      regionConstraint .gate place self env op ∧
      regionConstraint .copy place self env op ∧
      regionConstraint .lookup place self env op ∧
      regionConstraint .fixed place self env op := by
  cases op <;> simp [regionConstraint, RegionOperation.Constraints]

/-- One family over a complete region-operation list. -/
def regionConstraints (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations F → Prop
  | [] => True
  | op :: rest =>
      regionConstraint family place self env op ∧
        regionConstraints family place self env rest

/-- Splitting a complete region by family loses no constraints. -/
theorem regionOperations_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionOperations.Constraints place self env ops ↔
      regionConstraints .gate place self env ops ∧
      regionConstraints .copy place self env ops ∧
      regionConstraints .lookup place self env ops ∧
      regionConstraints .fixed place self env ops := by
  induction ops with
  | nil => simp [RegionOperations.Constraints, regionConstraints]
  | cons op rest ih =>
      rw [RegionOperations.Constraints, ih]
      rw [regionOperation_constraints_iff]
      simp only [regionConstraints]
      tauto

/-- One family over the complete layouter operation stream, with the same region-index threading as
`Halo2.Constraints`. -/
def constraints (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (env : Environment F) :
    Operations F → RegionIndex → Prop
  | [], _ => True
  | .region _ body :: rest, i =>
      regionConstraints family place i env body ∧
        constraints family place env rest (i + 1)
  | op@(.constrainInstance _ _ _) :: rest, i =>
      (if family = .copy then
        match op with
        | .constrainInstance cell col row =>
            cell.eval place env = env.get col row
        | _ => True
       else True) ∧ constraints family place env rest i
  | .loadTable table values :: rest, i =>
      (if family = .fixed then
        (∀ r : ℕ, r < values.length →
          env.fixed table.inner (r : ℤ) = values[r]!) ∧
        (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
          env.fixed table.inner (r : ℤ) = values[0]!)
       else True) ∧ constraints family place env rest i

/-- The four layouter-level family projections are exactly `Halo2.Constraints`. -/
theorem operations_constraints_iff
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Halo2.Constraints place env ops i ↔
      constraints .gate place env ops i ∧
      constraints .copy place env ops i ∧
      constraints .lookup place env ops i ∧
      constraints .fixed place env ops i := by
  induction ops generalizing i with
  | nil => simp [Halo2.Constraints, constraints]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Halo2.Constraints, ih, regionOperations_constraints_iff]
          simp [constraints]
          tauto
      | constrainInstance cell col row =>
          rw [Halo2.Constraints, ih]
          simp [constraints]
          tauto
      | loadTable table values =>
          rw [Halo2.Constraints, ih]
          simp [constraints]
          tauto

end CircuitConstraintFamily

/-- Complete circuit satisfaction, exposed in the same semantic families as the SNARK argument.
The fields are a decomposition of—not a substitute for—Clean's `Halo2.Constraints`. -/
structure FullCircuitSatisfaction
    {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) : Prop where
  gates : CircuitConstraintFamily.constraints .gate place env ops i
  copies : CircuitConstraintFamily.constraints .copy place env ops i
  lookups : CircuitConstraintFamily.constraints .lookup place env ops i
  fixed : CircuitConstraintFamily.constraints .fixed place env ops i

namespace FullCircuitSatisfaction

variable {F : Type} [FiniteField F]

/-- Clean constraints immediately provide the family-separated interface. -/
theorem of_constraints
    {place : RegionIndex → ℕ} {env : Environment F}
    {ops : Operations F} {i : RegionIndex}
    (h : Halo2.Constraints place env ops i) :
    FullCircuitSatisfaction place env ops i := by
  rw [CircuitConstraintFamily.operations_constraints_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Reassembling all four fields recovers Clean's authoritative constraint predicate. -/
theorem constraints
    {place : RegionIndex → ℕ} {env : Environment F}
    {ops : Operations F} {i : RegionIndex}
    (h : FullCircuitSatisfaction place env ops i) :
    Halo2.Constraints place env ops i := by
  rw [CircuitConstraintFamily.operations_constraints_iff]
  exact ⟨h.gates, h.copies, h.lookups, h.fixed⟩

/-- The family interface and Clean semantics are propositionally equivalent. -/
theorem iff_constraints
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    FullCircuitSatisfaction place env ops i ↔
      Halo2.Constraints place env ops i :=
  ⟨constraints, of_constraints⟩

/-- Reassemble independently proved semantic families while preserving one shared exceptional
event from the permutation/lookup arguments. The event is carried as data: a caller that fails to
reassemble hands back the break it computed, not a proof that one exists. -/
def of_components_or_bad
    {place : RegionIndex → ℕ} {env : Environment F}
    {ops : Operations F} {i : RegionIndex} {Bad : Type}
    (hgates : CircuitConstraintFamily.constraints .gate place env ops i)
    (hcopies : CircuitConstraintFamily.constraints .copy place env ops i ⊕' Bad)
    (hlookups : CircuitConstraintFamily.constraints .lookup place env ops i ⊕' Bad)
    (hfixed : CircuitConstraintFamily.constraints .fixed place env ops i) :
    FullCircuitSatisfaction place env ops i ⊕' Bad := by
  rcases hcopies with hcopies | hbad
  · rcases hlookups with hlookups | hbad
    · exact PSum.inl ⟨hgates, hcopies, hlookups, hfixed⟩
    · exact PSum.inr hbad
  · exact PSum.inr hbad

end FullCircuitSatisfaction

end Zcash.Snark
