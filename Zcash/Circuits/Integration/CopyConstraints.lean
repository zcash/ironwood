import Zcash.Circuits.Integration.CopyListMembership
import Zcash.Circuits.Integration.FixedColumns

/-! # From compiler copy pairs to Clean copy constraints

Read the compiler's raw column/row coordinates directly. Only coordinates occurring
in declared copies need to be valid; no total encoding into a nonempty finite cell
type, or second permutation replay, is required.
-/

namespace Zcash.Snark

open Halo2 Halo2.Layout

/-- Read a raw keygen coordinate through its permutation-column layout. -/
def rawCopyValue (columns : List ColRef) (env : Environment Fp) (cell : ℕ × ℕ) : Fp :=
  env.get (ColRef.toAny (columns.getD cell.1 (.advice 0))) (cell.2 : ℤ)

theorem rawCopyValue_permIndex
    (columns : List ColRef) (env : Environment Fp) (column : AnyColumn) (row : ℕ)
    (hcolumn : column ∈ columns.map ColRef.toAny) :
    rawCopyValue columns env (permIndex columns column, row) = env.get column (row : ℤ) := by
  simp only [rawCopyValue, permCols_getD_permIndex columns column (.advice 0) hcolumn]

/-- A declared constant copy occurs in the positional allocation part of the
compiler's copy list, with the requested literal retained by its allocated cell. -/
theorem constantPair_mem_copyList
    (columns : List ColRef) (starts : List ℕ) (ops : Operations Fp)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites ops).length ≤ constants.length)
    (hvalues : ∀ site entry, (site, entry) ∈ (operationConstSites ops).zip constants →
      entry.1 = site.2.val)
    {cell : Cell} {value : Fp}
    (hcopy : (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
      operationDeclaredCopies ops) :
    ∃ entry ∈ constants, entry.1 = value.val ∧
      (permIndex columns (ColRef.toAny (.fixed entry.2.1)), entry.2.2,
        (resolveCell columns starts cell).1, (resolveCell columns starts cell).2) ∈
        V1.copyList columns starts ops constants := by
  have hsite := mem_operationConstSites_of_declared_constant ops cell value hcopy
  obtain ⟨entry, hallocation⟩ :=
    exists_mem_zip_of_mem_left (operationConstSites ops) constants hfit hsite
  refine ⟨entry, (List.of_mem_zip hallocation).2, hvalues _ _ hallocation, ?_⟩
  have hgo := (V1_go_snd_eq columns starts ops constants hfit).1
  rw [V1.copyList, List.mem_append]
  right
  rw [hgo]
  exact List.mem_map.mpr ⟨((cell, value), entry), hallocation, rfl⟩

/-- Raw pair equality and reads of allocated constants suffice for all declared
copies. Registration is the only address requirement; this also covers an empty
permutation-column layout. -/
def copyConstraints_of_rawPairValues_or_bad
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs ops)
    (starts : List ℕ) (env : Environment Fp)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites ops).length ≤ constants.length)
    (hvalues : ∀ site entry, (site, entry) ∈ (operationConstSites ops).zip constants →
      entry.1 = site.2.val)
    (hcolumns : ∀ entry ∈ constants,
      AnyColumn.mk .fixed entry.2.1 ∈ cs.permutationColumns)
    {Bad : Type}
    (pairValues : ∀ pair ∈ V1.copyList (Keygen.permColsOf cs) starts ops constants,
      rawCopyValue (Keygen.permColsOf cs) env (pair.1, pair.2.1) =
        rawCopyValue (Keygen.permColsOf cs) env (pair.2.2.1, pair.2.2.2) ⊕' Bad)
    (constantValues : ∀ entry ∈ constants,
      env.get (AnyColumn.mk .fixed entry.2.1) (entry.2.2 : ℤ) = (entry.1 : Fp) ⊕' Bad)
    (i : RegionIndex) :
    CircuitConstraintFamily.constraints .copy
      (fun region => starts.getD region 0) env ops i ⊕' Bad := by
  obtain pairValues | bad :=
    listForallOrRelationWitness (V1.copyList (Keygen.permColsOf cs) starts ops constants) pairValues
  swap
  · exact PSum.inr bad
  refine bindOrRelationWitness
    (listForallOrRelationWitness constants constantValues) fun constantValues => ?_
  apply (CircuitConstraintFamily.copy_constraints_iff_declaredCopies _ env ops i).mpr
  apply List.forall_iff_forall_mem.mpr
  intro copy hcopy
  have hregisteredCopy := operationDeclaredCopies_permutationColumns cs ops hregistered copy hcopy
  have hshape := declared_shape ops (Keygen.permColsOf cs) starts copy hcopy
  rcases copy with ⟨left, right⟩
  cases left with
  | cell left =>
      have hleft : left.column ∈ (Keygen.permColsOf cs).map ColRef.toAny := by
        rw [Keygen.permColsOf_map_toAny]
        exact hregisteredCopy.1
      have hreadLeft :
          rawCopyValue (Keygen.permColsOf cs) env (resolveCell (Keygen.permColsOf cs) starts left) =
            left.eval (fun region => starts.getD region 0) env := by
        simpa only [resolveCell, place, Cell.eval] using
          rawCopyValue_permIndex (Keygen.permColsOf cs) env left.column
            (starts.getD left.regionIndex 0 + left.rowOffset) hleft
      cases right with
      | cell right =>
          have hright : right.column ∈ (Keygen.permColsOf cs).map ColRef.toAny := by
            rw [Keygen.permColsOf_map_toAny]
            exact hregisteredCopy.2
          have hreadRight :
              rawCopyValue (Keygen.permColsOf cs) env (resolveCell (Keygen.permColsOf cs) starts right) =
                right.eval (fun region => starts.getD region 0) env := by
            simpa only [resolveCell, place, Cell.eval] using
              rawCopyValue_permIndex (Keygen.permColsOf cs) env right.column
                (starts.getD right.regionIndex 0 + right.rowOffset) hright
          have hmem := mem_V1_copyList_of_declared (Keygen.permColsOf cs) starts ops constants
            (.cell left, .cell right) _ rfl hcopy
          simpa only [DeclaredCopy.Satisfied, CopyEndpoint.eval, hreadLeft, hreadRight]
            using pairValues _ hmem
      | «instance» column row =>
          have hcolumn : column.toAny ∈ (Keygen.permColsOf cs).map ColRef.toAny := by
            rw [Keygen.permColsOf_map_toAny]
            exact hregisteredCopy.2
          have hmem := mem_V1_copyList_of_declared (Keygen.permColsOf cs) starts ops constants
            (.cell left, .instance column row) _ rfl hcopy
          simpa only [DeclaredCopy.Satisfied, CopyEndpoint.eval, hreadLeft,
            rawCopyValue_permIndex _ _ _ _ hcolumn] using pairValues _ hmem
      | constant value =>
          obtain ⟨entry, hentry, hvalue, hmem⟩ :=
            constantPair_mem_copyList (Keygen.permColsOf cs) starts ops constants
              hfit hvalues hcopy
          have hcolumn : AnyColumn.mk .fixed entry.2.1 ∈
              (Keygen.permColsOf cs).map ColRef.toAny := by
            rw [Keygen.permColsOf_map_toAny]
            exact hcolumns entry hentry
          have hpair := pairValues _ hmem
          have hconstant := constantValues entry hentry
          have hreadConstant := rawCopyValue_permIndex (Keygen.permColsOf cs) env
            (AnyColumn.mk .fixed entry.2.1) entry.2.2 hcolumn
          have heq := hpair.symm.trans (hreadConstant.trans hconstant)
          simpa only [DeclaredCopy.Satisfied, CopyEndpoint.eval, hreadLeft, hvalue,
            ZMod.natCast_zmod_val] using heq
  | «instance» column row =>
      exfalso
      rcases hshape with ⟨tuple, hresolve⟩ | ⟨cell, value, hshape⟩
      · simp [resolveDeclared] at hresolve
      · simp at hshape
  | constant value =>
      exfalso
      rcases hshape with ⟨tuple, hresolve⟩ | ⟨cell, value, hshape⟩
      · simp [resolveDeclared] at hresolve
      · simp at hshape

/-- A top-level circuit discharges registration and constant allocation internally.
The semantic inputs are equality on compiler copy pairs and fixed-cell reads. -/
def topLevelCopyConstraints_of_rawPairValues_or_bad
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (env : Environment Fp) {Bad : Type}
    (pairValues : ∀ (pair : ℕ × ℕ × ℕ × ℕ), pair ∈ V1.copyList (Keygen.permColsOf top.constraintSystem)
        top.regionStarts top.operations
        (Keygen.constantCopyEntries top.constraintSystem top.operations) →
      rawCopyValue (Keygen.permColsOf top.constraintSystem) env (pair.1, pair.2.1) =
        rawCopyValue (Keygen.permColsOf top.constraintSystem) env
          (pair.2.2.1, pair.2.2.2) ⊕' Bad)
    (fixedRead : ∀ {column row : ℕ} {value : Fp},
      (column, row, value) ∈ topLevelRequiredFixedEntries top →
        env.fixed ⟨column⟩ (row : ℤ) = value ⊕' Bad) :
    CircuitConstraintFamily.constraints .copy top.placement env top.operations 0 ⊕' Bad := by
  have hfit := top.constantValues_length_le_constantAssignments_length
  have hsiteFit : (operationConstSites top.operations).length ≤
      (Keygen.constantCopyEntries top.constraintSystem top.operations).length := by
    simpa only [Keygen.constantCopyEntries, List.length_map, operationConstSites_length] using hfit
  have hplace : (fun region => top.regionStarts.getD region 0) = top.placement := by
    funext region
    exact (top.placement_apply region).symm
  rw [← hplace]
  refine copyConstraints_of_rawPairValues_or_bad top.constraintSystem top.operations
    top.keygenCoherent top.regionStarts env
    (Keygen.constantCopyEntries top.constraintSystem top.operations) hsiteFit
    ?_ ?_ pairValues ?_ 0
  · intro site entry h
    apply constantAllocation_value top.operations
      (top.constraintSystem.constants.map (·.index))
      (by simpa only [operationConstSites_length] using hfit)
    simpa only [Keygen.constantCopyEntries] using h
  · intro entry hentry
    rw [Keygen.constantCopyEntries, List.mem_map] at hentry
    obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
    exact top.constantAssignmentColumn_mem_permutationColumns hentry
  · intro entry hentry
    have hfixed : (entry.2.1, entry.2.2, (entry.1 : Fp)) ∈ topLevelConstantEntries top := by
      rw [Keygen.constantCopyEntries, List.mem_map] at hentry
      obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
      rw [topLevelConstantEntries, Layout.constantAssignments, List.mem_map]
      exact ⟨(value, column, row), hentry, by simp only [ZMod.natCast_zmod_val]⟩
    exact fixedRead (mem_topLevelCompilerFixedEntries_of_constant top hfixed)

end Zcash.Snark
