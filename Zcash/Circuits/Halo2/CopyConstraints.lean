import Zcash.Circuits.Halo2.CopyListMembership

/-! # Soundness of the compiler copy list

Allocated constants and resolved cell equalities recover the source copy constraints.
-/

namespace Halo2

open Zcash Halo2.Layout

/-- Read a raw keygen coordinate through its permutation-column layout. -/
def rawCopyValue (columns : List ColRef) (env : Environment Fp) (cell : ℕ × ℕ) : Fp :=
  env.get (ColRef.toAny (columns.getD cell.1 (.advice 0))) (cell.2 : ℤ)

theorem rawCopyValue_permIndex
    (columns : List ColRef) (env : Environment Fp) (column : AnyColumn) (row : ℕ)
    (hcolumn : column ∈ columns.map ColRef.toAny) :
    rawCopyValue columns env (permIndex columns column, row) = env.get column (row : ℤ) := by
  simp only [rawCopyValue, permCols_getD_permIndex columns column (.advice 0) hcolumn]

/-- Resolving a registered cell preserves its environment read. -/
theorem rawCopyValue_resolveCell
    (cs : ConstraintSystem Fp) (starts : List ℕ) (env : Environment Fp) (cell : Cell)
    (hColumn : cell.column ∈ cs.permutationColumns) :
    rawCopyValue (permColsOf cs) env (resolveCell (permColsOf cs) starts cell) =
      cell.eval (fun region => starts.getD region 0) env := by
  simpa only [resolveCell, place, Cell.eval] using
    rawCopyValue_permIndex (permColsOf cs) env cell.column
      (starts.getD cell.regionIndex 0 + cell.rowOffset)
      (by simpa only [permColsOf_map_toAny] using hColumn)

/-- Resolution changes only coordinates, not the equality denoted by a copy. -/
theorem resolveDeclared_satisfied_iff
    (cs : ConstraintSystem Fp) (starts : List ℕ) (env : Environment Fp)
    (copy : DeclaredCopy Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared (permColsOf cs) starts copy = some tuple)
    (hColumns : copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs) :
    DeclaredCopy.Satisfied (fun region => starts.getD region 0) env copy ↔
      rawCopyValue (permColsOf cs) env (tuple.1, tuple.2.1) =
        rawCopyValue (permColsOf cs) env (tuple.2.2.1, tuple.2.2.2) := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  · simp only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env _ hColumns.1,
      rawCopyValue_resolveCell cs starts env _ hColumns.2]
  · rename_i cell column row
    simp only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env _ hColumns.1,
      rawCopyValue_permIndex (permColsOf cs) env column.toAny row
        (by simpa only [permColsOf_map_toAny, CopyEndpoint.PermutationColumnRegistered]
          using hColumns.2)]

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
  have hsite := (mem_operationConstSites_iff_declaredCopy ops cell value).mpr hcopy
  rw [← List.map_fst_zip hfit, List.mem_map] at hsite
  obtain ⟨⟨_, entry⟩, hallocation, rfl⟩ := hsite
  refine ⟨entry, (List.of_mem_zip hallocation).2, hvalues _ _ hallocation, ?_⟩
  have hgo := (V1_go_snd_eq columns starts ops constants).1
  rw [V1.copyList, List.mem_append]
  right
  rw [hgo]
  exact List.mem_map.mpr ⟨((cell, value), entry), hallocation, rfl⟩

/-- Raw pair equality and reads of allocated constants suffice for all declared
copies. Registration is the only address requirement; this also covers an empty
permutation-column layout. -/
theorem copy_constraints_of_rawPairValues
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs ops)
    (starts : List ℕ) (env : Environment Fp)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites ops).length ≤ constants.length)
    (hvalues : ∀ site entry, (site, entry) ∈ (operationConstSites ops).zip constants →
      entry.1 = site.2.val)
    (hcolumns : ∀ entry ∈ constants,
      AnyColumn.mk .fixed entry.2.1 ∈ cs.permutationColumns)
    (pairValues : ∀ pair ∈ V1.copyList (Halo2.Layout.permColsOf cs) starts ops constants,
      rawCopyValue (Halo2.Layout.permColsOf cs) env (pair.1, pair.2.1) =
        rawCopyValue (Halo2.Layout.permColsOf cs) env (pair.2.2.1, pair.2.2.2))
    (constantValues : ∀ entry ∈ constants,
      env.get (AnyColumn.mk .fixed entry.2.1) (entry.2.2 : ℤ) = (entry.1 : Fp))
    (i : RegionIndex) :
    CircuitConstraintFamily.constraints .copy
      (fun region => starts.getD region 0) env ops i := by
  apply (CircuitConstraintFamily.copy_constraints_iff_declaredCopies _ env ops i).mpr
  apply List.forall_iff_forall_mem.mpr
  intro copy hcopy
  have hregisteredCopy := operationDeclaredCopies_permutationColumns cs ops hregistered copy hcopy
  rcases declared_shape ops (permColsOf cs) starts copy hcopy with
    ⟨tuple, hResolve⟩ | ⟨cell, value, rfl⟩
  · exact (resolveDeclared_satisfied_iff cs starts env copy tuple hResolve hregisteredCopy).mpr
      (pairValues tuple (mem_V1_copyList_of_declared (permColsOf cs) starts ops constants
        copy tuple hResolve hcopy))
  · obtain ⟨entry, hEntry, hValue, hMem⟩ :=
      constantPair_mem_copyList (permColsOf cs) starts ops constants hfit hvalues hcopy
    have hColumn : AnyColumn.mk .fixed entry.2.1 ∈ (permColsOf cs).map ColRef.toAny := by
      rw [permColsOf_map_toAny]
      exact hcolumns entry hEntry
    have hRead := rawCopyValue_permIndex (permColsOf cs) env
      (AnyColumn.mk .fixed entry.2.1) entry.2.2 hColumn
    have hEqual := (pairValues _ hMem).symm.trans (hRead.trans (constantValues entry hEntry))
    simpa only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env cell hregisteredCopy.1, hValue,
      ZMod.natCast_zmod_val] using hEqual

end Halo2
