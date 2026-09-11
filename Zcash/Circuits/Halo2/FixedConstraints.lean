import Clean.Halo2.Keygen.Layout
import Zcash.Circuits.Halo2.FixedOperations

/-!
# Fixed-layout compiler bridge

The keygen layout compiler emits sparse fixed-column entries from table loads and
region-local fixed assignments.  This module proves, generically, that realizing
those emitted entries supplies the `fixed` operation family used by circuit
soundness.  Selector entries and constant-copy allocation are separate compiler
products; they are not needed for the explicit fixed requirements extracted here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace FixedLayout

/-- Every explicit row of a loaded table occurs in `Layout.tableAssignments`. -/
theorem mem_tableAssignments_of_loadTable_of_lt
    (usable : ℕ) (ops : Operations Fp)
    (table : TableColumn) (values : List Fp)
    (hload : Operation.loadTable table values ∈ ops)
    (row : ℕ) (hrow : row < values.length) :
    (table.inner.index, row, values[row]!) ∈
      Layout.tableAssignments usable ops := by
  induction ops with
  | nil => simp at hload
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          exact ih (by simpa using hload)
      | constrainInstance cell column instanceRow =>
          exact ih (by simpa using hload)
      | loadTable loadedTable loadedValues =>
          simp only [List.mem_cons] at hload
          rcases hload with hhead | htail
          · cases hhead
            unfold Layout.tableAssignments
            apply List.mem_append_left
            unfold Layout.tableColumnAssignments
            apply List.mem_append_left
            apply List.mem_map.mpr
            exact ⟨(values[row]!, row), by
              apply List.mk_mem_zipIdx_iff_getElem?.mpr
              simp [List.getElem!_eq_getElem?_getD,
                List.getElem?_eq_getElem hrow], rfl⟩
          · unfold Layout.tableAssignments
            apply List.mem_append_right
            exact ih htail

/--
Every default-fill row of a nonempty loaded table occurs in
`Layout.tableAssignments`.
-/
theorem mem_tableAssignments_of_loadTable_of_fill
    (usable : ℕ) (ops : Operations Fp)
    (table : TableColumn) (values : List Fp)
    (hload : Operation.loadTable table values ∈ ops)
    (hne : values ≠ [])
    (row : ℕ) (hlower : values.length ≤ row)
    (hupper : row < usable) :
    (table.inner.index, row, values[0]!) ∈
      Layout.tableAssignments usable ops := by
  induction ops with
  | nil => simp at hload
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          exact ih (by simpa using hload)
      | constrainInstance cell column instanceRow =>
          exact ih (by simpa using hload)
      | loadTable loadedTable loadedValues =>
          simp only [List.mem_cons] at hload
          rcases hload with hhead | htail
          · cases hhead
            unfold Layout.tableAssignments
            apply List.mem_append_left
            unfold Layout.tableColumnAssignments
            apply List.mem_append_right
            rcases values with _ | ⟨first, rest⟩
            · contradiction
            apply List.mem_map.mpr
            refine ⟨row - (first :: rest).length, ?_, ?_⟩
            · apply List.mem_range.mpr
              omega
            · simp only [List.getElem!_eq_getElem?_getD,
                List.getElem?_cons_zero, Option.getD_some]
              congr
              omega
          · unfold Layout.tableAssignments
            apply List.mem_append_right
            exact ih htail

/-- Region fixed requirements never contain a table load. -/
private theorem table_not_mem_regionFixedRequirements
    (self : RegionIndex) (body : RegionOperations Fp)
    (table : TableColumn) (values : List Fp) :
    FixedRequirement.table table values ∉
      regionFixedRequirements self body := by
  induction body with
  | nil => simp [regionFixedRequirements]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [regionFixedRequirements]

/-- A table fixed requirement comes from the corresponding layouter operation. -/
theorem loadTable_mem_of_requirement
    (ops : Operations Fp) (i : RegionIndex)
    (table : TableColumn) (values : List Fp)
    (hrequirement :
      FixedRequirement.table table values ∈
        operationFixedRequirements ops i) :
    Operation.loadTable table values ∈ ops := by
  induction ops generalizing i with
  | nil => simp [operationFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationFixedRequirements, List.mem_append] at hrequirement
          rcases hrequirement with hbody | hrest
          · exact absurd hbody
              (table_not_mem_regionFixedRequirements i body table values)
          · exact List.mem_cons_of_mem _
              (ih (i := i + 1) hrest)
      | constrainInstance cell column row =>
          exact List.mem_cons_of_mem _
            (ih (i := i) (by simpa [operationFixedRequirements] using hrequirement))
      | loadTable loadedTable loadedValues =>
          simp only [operationFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih (i := i) htail)

/-- A region requirement remembers the corresponding `assignFixed` operation. -/
private theorem assignFixed_mem_of_region_requirement
    (self : RegionIndex) (body : RegionOperations Fp)
    (column : Column .fixed) (row : ℕ) (value : Fp)
    (hrequirement :
      FixedRequirement.assignment self column row value ∈
        regionFixedRequirements self body) :
    RegionOperation.assignFixed column row value ∈ body := by
  induction body with
  | nil => simp [regionFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | assignFixed assignedColumn assignedRow assignedValue =>
          simp only [regionFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih htail)
      | _ =>
          exact List.mem_cons_of_mem _
            (ih (by simpa [regionFixedRequirements] using hrequirement))

/-- A region-local assignment requirement retains its enclosing region index. -/
private theorem region_eq_of_assignment_requirement
    (self region : RegionIndex) (body : RegionOperations Fp)
    (column : Column .fixed) (row : ℕ) (value : Fp)
    (hrequirement :
      FixedRequirement.assignment region column row value ∈
        regionFixedRequirements self body) :
    region = self := by
  induction body with
  | nil => simp [regionFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | assignFixed assignedColumn assignedRow assignedValue =>
          simp only [regionFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            rfl
          · exact ih htail
      | _ =>
          exact ih (by simpa [regionFixedRequirements] using hrequirement)

/--
Every extracted region fixed requirement occurs in the sparse
`Layout.regionAssignments` output at its V1 absolute row.
-/
theorem mem_regionAssignments_of_requirement
    (starts : List ℕ) (ops : Operations Fp) (i : RegionIndex)
    (region : RegionIndex) (column : Column .fixed)
    (row : ℕ) (value : Fp)
    (hrequirement :
      FixedRequirement.assignment region column row value ∈
        operationFixedRequirements ops i) :
    (column.index, Layout.place starts region + row, value) ∈
      Layout.regionAssignments starts
        (indexedRegions ops i).1 := by
  induction ops generalizing i with
  | nil => simp [operationFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationFixedRequirements, List.mem_append] at hrequirement
          rcases hrequirement with hbody | hrest
          · have hregion : region = i :=
              region_eq_of_assignment_requirement
                i region body column row value hbody
            subst region
            have hassign :
                RegionOperation.assignFixed column row value ∈ body := by
              apply assignFixed_mem_of_region_requirement
                i body column row value
              exact hbody
            simp only [indexedRegions]
            apply List.mem_flatMap.mpr
            refine ⟨(i, body), List.mem_cons_self, ?_⟩
            apply List.mem_filterMap.mpr
            exact ⟨.assignFixed column row value, hassign, rfl⟩
          · simp only [indexedRegions]
            apply List.mem_flatMap.mpr
            obtain ⟨indexed, hindexed, hentry⟩ :=
              List.mem_flatMap.mp
                (ih (i := i + 1) hrest)
            exact ⟨indexed, List.mem_cons_of_mem _ hindexed, hentry⟩
      | constrainInstance cell instanceColumn instanceRow =>
          exact ih (i := i)
            (by simpa [operationFixedRequirements] using hrequirement)
      | loadTable table values =>
          simp only [operationFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hfalse | hrest
          · contradiction
          · exact ih (i := i) hrest

/--
Realizing the raw sparse table and region-assignment entries realizes every explicit
fixed requirement in the operation stream.
-/
theorem requirement_satisfied_of_entries
    (starts : List ℕ) (usable : ℕ)
    (ops : Operations Fp) (i : RegionIndex)
    (env : Environment Fp)
    (husable : env.usableRows = usable)
    (hentries : ∀ column row value,
      (column, row, value) ∈
        (Layout.tableAssignments usable ops ++
          Layout.regionAssignments starts
            (indexedRegions ops i).1) →
      env.fixed ⟨column⟩ (row : ℤ) = value)
    (requirement : FixedRequirement Fp)
    (hrequirement :
      requirement ∈ operationFixedRequirements ops i) :
    requirement.Satisfied (Layout.place starts) env := by
  cases requirement with
  | assignment region column row value =>
      simp only [FixedRequirement.Satisfied]
      have hentry := hentries column.index
        (Layout.place starts region + row) value
        (List.mem_append_right _
          (mem_regionAssignments_of_requirement
            starts ops i region column row value hrequirement))
      simpa using hentry
  | table column values =>
      simp only [FixedRequirement.Satisfied]
      have hload :=
        loadTable_mem_of_requirement ops i column values hrequirement
      constructor
      · intro row hrow
        have hentry := hentries column.inner.index row
          values[row]!
          (List.mem_append_left _
            (mem_tableAssignments_of_loadTable_of_lt
              usable ops column values hload row hrow))
        simpa using hentry
      · intro hne row hlower hupper
        have hrow : row < usable := by
          simpa [husable] using hupper
        have hentry := hentries column.inner.index row
          values[0]!
          (List.mem_append_left _
            (mem_tableAssignments_of_loadTable_of_fill
              usable ops column values hload hne row hlower hrow))
        simpa using hentry

/-- The entry-realization premise supplies the complete fixed constraint family. -/
theorem constraints_of_entries
    (starts : List ℕ) (usable : ℕ)
    (ops : Operations Fp) (i : RegionIndex)
    (env : Environment Fp)
    (husable : env.usableRows = usable)
    (hentries : ∀ column row value,
      (column, row, value) ∈
        (Layout.tableAssignments usable ops ++
          Layout.regionAssignments starts
            (indexedRegions ops i).1) →
      env.fixed ⟨column⟩ (row : ℤ) = value) :
    CircuitConstraintFamily.constraints .fixed
      (Layout.place starts) env ops i := by
  apply fixed_constraints_of_requirements
  intro requirement hrequirement
  exact requirement_satisfied_of_entries
    starts usable ops i env husable hentries requirement hrequirement

end FixedLayout

end Zcash.Snark
