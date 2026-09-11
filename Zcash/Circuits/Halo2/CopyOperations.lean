import Zcash.Circuits.Halo2.ConstraintFamilies

/-!
# Declared operation copies and permutation-cycle satisfaction

This is the operation-trace side of the copy bridge.  It extracts the three copy forms carried by
Clean operations—cell equality, instance equality, and constant equality—into one endpoint type,
and proves that satisfying the extracted list is exactly the copy constraint family.

The characterization is independent of the compiler's concrete copy-pair representation.
-/

namespace Zcash.Snark

open Halo2

/-- A semantic endpoint of a Clean copy operation, with constants represented by value. -/
inductive CopyEndpoint (F : Type) where
  | cell : Cell → CopyEndpoint F
  | instance : Column .instance → ℕ → CopyEndpoint F
  | constant : F → CopyEndpoint F
deriving Repr

namespace CopyEndpoint

variable {F : Type} [FiniteField F]

/-- Read an endpoint in Clean's placed environment. -/
def eval (place : RegionIndex → ℕ) (env : Environment F) : CopyEndpoint F → F
  | .cell c => c.eval place env
  | .instance col row => env.get col (row : ℤ)
  | .constant value => value

end CopyEndpoint

/-- A declared semantic equality. -/
abbrev DeclaredCopy (F : Type) := CopyEndpoint F × CopyEndpoint F

namespace DeclaredCopy

variable {F : Type} [FiniteField F]

/-- The equality denoted by one declared copy. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (copy : DeclaredCopy F) : Prop :=
  copy.1.eval place env = copy.2.eval place env

end DeclaredCopy

/-- The copy, if any, declared by one region operation. -/
def regionOperationDeclaredCopy? {F : Type} : RegionOperation F → Option (DeclaredCopy F)
  | .constrainEqual left right => some (.cell left, .cell right)
  | .constrainConstant cell value => some (.cell cell, .constant value)
  | .constrainInstance cell col row => some (.cell cell, .instance col row)
  | _ => none

/-- Declared copies in one region, in operation order. -/
def regionDeclaredCopies {F : Type} :
    RegionOperations F → List (DeclaredCopy F)
  | [] => []
  | op :: rest =>
      match regionOperationDeclaredCopy? op with
      | some copy => copy :: regionDeclaredCopies rest
      | none => regionDeclaredCopies rest

/-- Declared copies in a complete layouter stream.  Region-local copies retain the `Cell` region
indices they were synthesized with; layouter-level instance copies are inserted in stream order. -/
def operationDeclaredCopies {F : Type} : Operations F → List (DeclaredCopy F)
  | [] => []
  | .region _ body :: rest => regionDeclaredCopies body ++ operationDeclaredCopies rest
  | .constrainInstance cell col row :: rest =>
      (.cell cell, .instance col row) :: operationDeclaredCopies rest
  | .loadTable _ _ :: rest => operationDeclaredCopies rest

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- The copy-family projection of a region is exactly satisfaction of its extracted copies. -/
theorem region_copy_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    regionConstraints .copy place self env ops ↔
      (regionDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops with
  | nil => simp [regionConstraints, regionDeclaredCopies]
  | cons op rest ih =>
      cases op <;>
        simp_all [regionConstraints, regionConstraint, RegionOperation.Constraints,
          regionDeclaredCopies, regionOperationDeclaredCopy?,
          DeclaredCopy.Satisfied, CopyEndpoint.eval]

/-- The complete copy-family projection is exactly satisfaction of the copies extracted from the
whole operation stream. -/
theorem copy_constraints_iff_declaredCopies
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    constraints .copy place env ops i ↔
      (operationDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [constraints, operationDeclaredCopies]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [constraints, ih, region_copy_constraints_iff]
          simp [operationDeclaredCopies, List.forall_append]
      | constrainInstance cell col row =>
          rw [constraints, ih]
          simp [operationDeclaredCopies, DeclaredCopy.Satisfied, CopyEndpoint.eval]
      | loadTable table values =>
          rw [constraints, ih]
          simp [operationDeclaredCopies]

end CircuitConstraintFamily

end Zcash.Snark
