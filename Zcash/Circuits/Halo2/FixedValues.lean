import Clean.Halo2.TopLevel

/-! # Canonical environments realize compiler-owned fixed data -/

namespace Halo2.TopLevelCircuit

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Every emitted fixed assignment is already true in the canonical environment. -/
theorem environment_fixed_of_mem_raw (assignment : ProofAssignment F)
    {entry : Layout.FixedAssignment F}
    (hentry : entry ∈ Layout.rawAssignments (top.usableRowsAt top.domainExponent)
      top.selectorMap top.constraintSystem top.operations) :
    (top.environment assignment).fixed ⟨entry.1⟩ (entry.2.1 : ℤ) = entry.2.2 := by
  have hbounds := top.fixedAssignment_bounds_of_mem_raw entry hentry
  rw [top.environment_fixed, top.fixedValue_eq_fixedRows_getD]
  rw [Int.natMod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hbounds.2),
    Int.toNat_natCast]
  exact top.fixedRows_getD_getD_eq_of_mem_raw entry hentry

/-- A packed selector assignment is part of the compiler's fixed output. -/
theorem selectorAssignment_mem_raw {entry : Layout.FixedAssignment F}
    (hentry : entry ∈ Layout.selectorAssignments top.selectorMap top.selectorActivations) :
    entry ∈ Layout.rawAssignments (top.usableRowsAt top.domainExponent)
      top.selectorMap top.constraintSystem top.operations := by
  simpa only [Layout.rawAssignments, List.mem_append] using Or.inl (Or.inr hentry)

end Halo2.TopLevelCircuit
