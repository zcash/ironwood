import Zcash.Circuits.Halo2.CopyConstraints
import Zcash.Circuits.Halo2.FixedValues

/-! # Soundness of compiled copy semantics

Copy compilation resolves region-local cells to absolute coordinates and allocates
fixed cells for constants. Its semantic output is equality on these resolved pairs.
The permutation argument may enforce these equalities without exposing source operations.
-/

namespace Halo2.TopLevelCircuit

open Zcash Halo2.Layout

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

/-- Resolved copy pairs, including the fixed cells allocated for constant copies. -/
def copyPairs : List (ℕ × ℕ × ℕ × ℕ) :=
  Layout.V1.copyList (Layout.permColsOf top.constraintSystem) top.regionStarts
    top.operations (Layout.constantCopyEntries top.constraintSystem top.operations)

/-- Both endpoints of every compiled copy have equal values in the assignment. -/
def CopiesCompiled (assignment : ProofAssignment Fp) : Prop :=
  ∀ pair ∈ top.copyPairs,
    rawCopyValue (Layout.permColsOf top.constraintSystem) (top.environment assignment)
        (pair.1, pair.2.1) =
      rawCopyValue (Layout.permColsOf top.constraintSystem) (top.environment assignment)
        (pair.2.2.1, pair.2.2.2)

/-- Registration, placement, and constant allocation turn resolved copy equality
into all source copy constraints. Fixed values come from the circuit, not a hypothesis. -/
theorem copy_constraints_of_compiled (assignment : ProofAssignment Fp)
    (hcopies : top.CopiesCompiled assignment) :
    CircuitConstraintFamily.constraints .copy top.placement
      (top.environment assignment) top.operations 0 := by
  have hfit := top.constantValues_length_le_constantAssignments_length
  have hsiteFit : (operationConstSites top.operations).length ≤
      (Layout.constantCopyEntries top.constraintSystem top.operations).length := by
    simpa only [Layout.constantCopyEntries, List.length_map, operationConstSites_length] using hfit
  have hplace : (fun region => top.regionStarts.getD region 0) = top.placement := by
    funext region
    exact (top.placement_apply region).symm
  rw [← hplace]
  apply copy_constraints_of_rawPairValues top.constraintSystem top.operations
    top.keygenCoherent top.regionStarts (top.environment assignment)
    (Layout.constantCopyEntries top.constraintSystem top.operations) hsiteFit
    ?_ ?_ hcopies ?_ 0
  · intro site entry h
    apply constantAllocation_value top.operations
      (top.constraintSystem.constants.map (·.index))
      (by simpa only [operationConstSites_length] using hfit)
    simpa only [Layout.constantCopyEntries] using h
  · intro entry hentry
    rw [Layout.constantCopyEntries, List.mem_map] at hentry
    obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
    exact top.constantAssignmentColumn_mem_permutationColumns hentry
  · intro entry hentry
    rw [Layout.constantCopyEntries, List.mem_map] at hentry
    obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
    have hraw : (column, row, value) ∈ Layout.rawAssignments
        (top.usableRowsAt top.domainExponent) top.selectorMap
        top.constraintSystem top.operations := by
      simp only [Layout.rawAssignments, List.mem_append]
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact List.mem_map.mpr ⟨(value, column, row), hentry, rfl⟩
    simpa only [ZMod.natCast_zmod_val] using top.environment_fixed_of_mem_raw assignment hraw

end Halo2.TopLevelCircuit
