import Zcash.Circuits.Halo2.CopyCells
import Zcash.Circuits.Halo2.CopyOperations
import Zcash.Circuits.Halo2.CopyLayout
import Clean.Halo2.Keygen.Domain

/-!
# Declared copies resolve into the keygen copy list

The copy-replay witness needs, per declared Clean copy, a value-agreement fact; for the
cell/cell and cell/instance kinds that fact transports through the keygen permutation,
whose copy list is the floor planner's. This module proves the membership half: every
non-constant declared copy, resolved to absolute permutation-column coordinates, is a
member of the V1 copy list. (Constant copies consume the positional constants
allocation; their membership couples to the allocation walk and lives with the
constants instantiation.)
-/

namespace Halo2

open Zcash
open Halo2.Layout

/-- Resolve a non-constant declared copy to the keygen copy tuple: region cells through
the placement, instance endpoints at their absolute rows. Constant endpoints resolve to
`none` — their cells are the planner's positional constants allocation. -/
def resolveDeclared (permCols : List ColRef) (starts : List ℕ) :
    CopyEndpoint Fp × CopyEndpoint Fp → Option (ℕ × ℕ × ℕ × ℕ)
  | (.cell l, .cell r) =>
      some ((resolveCell permCols starts l).1, (resolveCell permCols starts l).2,
        (resolveCell permCols starts r).1, (resolveCell permCols starts r).2)
  | (.cell c, .instance col row) =>
      some ((resolveCell permCols starts c).1, (resolveCell permCols starts c).2,
        permIndex permCols col.toAny, row)
  | _ => none

/-- A column present in the permutation layout resolves to an in-range index. -/
theorem permIndex_lt_length_of_mem
    (permCols : List ColRef) {column : AnyColumn}
    (hcolumn : column ∈ permCols.map ColRef.toAny) :
    permIndex permCols column < permCols.length := by
  have hexists : ∃ candidate ∈ permCols.map ColRef.toAny,
      decide (candidate = column) = true :=
    ⟨column, hcolumn, by simp⟩
  rw [permIndex, List.findIdx?_eq_some_of_exists hexists,
    Option.getD_some]
  simpa only [List.length_map] using
    List.findIdx_lt_length_of_exists hexists

/-- Looking up the index of a registered permutation column recovers that column. -/
theorem permCols_getD_permIndex
    (permCols : List ColRef) (column : AnyColumn) (fallback : ColRef)
    (hcolumn : column ∈ permCols.map ColRef.toAny) :
    ColRef.toAny (permCols.getD (permIndex permCols column) fallback) = column := by
  let columns := permCols.map ColRef.toAny
  have hexists : ∃ candidate ∈ columns,
      decide (candidate = column) = true :=
    ⟨column, hcolumn, by simp⟩
  have hindex : columns.findIdx (fun candidate => decide (candidate = column)) <
      columns.length :=
    List.findIdx_lt_length_of_exists hexists
  have hfound :=
    List.findIdx_getElem
      (p := fun candidate => decide (candidate = column))
      (xs := columns) (w := hindex)
  have hvalue :
      columns[columns.findIdx (fun candidate => decide (candidate = column))] =
        column := by
    exact of_decide_eq_true hfound
  have hpermIndex :
      permIndex permCols column =
        columns.findIdx (fun candidate => decide (candidate = column)) := by
    rw [permIndex, List.findIdx?_eq_some_of_exists hexists,
      Option.getD_some]
  have hpermIndexLt : permIndex permCols column < permCols.length := by
    rw [hpermIndex]
    simpa only [columns, List.length_map] using hindex
  have hvalue' :
      ColRef.toAny
          permCols[columns.findIdx (fun candidate => decide (candidate = column))] =
        column := by
    simpa only [columns, List.getElem_map] using hvalue
  rw [List.getD_eq_getElem _ _ hpermIndexLt]
  simpa only [hpermIndex] using hvalue'

/-- The column requirement carried by a declared copy endpoint. Constants acquire
their concrete column later from the floor planner's allocation. -/
def CopyEndpoint.PermutationColumnRegistered
    (cs : ConstraintSystem Fp) : CopyEndpoint Fp → Prop
  | CopyEndpoint.cell c => c.column ∈ cs.permutationColumns
  | CopyEndpoint.instance column _ => column.toAny ∈ cs.permutationColumns
  | CopyEndpoint.constant _ => True

/-- The row requirement carried by a declared copy endpoint. Constants acquire
their concrete row later from the floor planner's allocation. -/
def CopyEndpoint.WithinRows
    (starts : List ℕ) (bound : ℕ) : CopyEndpoint Fp → Prop
  | CopyEndpoint.cell c =>
      starts.getD c.regionIndex 0 + c.rowOffset < bound
  | CopyEndpoint.instance _ row => row < bound
  | CopyEndpoint.constant _ => True

/-- Both endpoints of a coherent region copy use registered permutation columns. -/
theorem regionDeclaredCopies_permutationColumns
    (cs : ConstraintSystem Fp) (body : RegionOperations Fp)
    (hcoherent : body.Forall (RegionOperation.KeygenCoherent cs))
    (copy : DeclaredCopy Fp) (hcopy : copy ∈ regionDeclaredCopies body) :
    copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs := by
  induction body with
  | nil => simp [regionDeclaredCopies] at hcopy
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | constrainEqual left right =>
          simp only [regionDeclaredCopies, regionOperationDeclaredCopy?,
            List.mem_cons] at hcopy
          rcases hcopy with rfl | hcopy
          · simpa [CopyEndpoint.PermutationColumnRegistered,
              RegionOperation.KeygenCoherent] using hcoherent.1
          · exact inductionHypothesis hcoherent.2 hcopy
      | constrainConstant cell value =>
          simp only [regionDeclaredCopies, regionOperationDeclaredCopy?,
            List.mem_cons] at hcopy
          rcases hcopy with rfl | hcopy
          · simpa [CopyEndpoint.PermutationColumnRegistered,
              RegionOperation.KeygenCoherent] using hcoherent.1
          · exact inductionHypothesis hcoherent.2 hcopy
      | constrainInstance cell column row =>
          simp only [regionDeclaredCopies, regionOperationDeclaredCopy?,
            List.mem_cons] at hcopy
          rcases hcopy with rfl | hcopy
          · simpa [CopyEndpoint.PermutationColumnRegistered,
              RegionOperation.KeygenCoherent] using hcoherent.1
          · exact inductionHypothesis hcoherent.2 hcopy
      | assignAdvice column row witness =>
          exact inductionHypothesis hcoherent.2 hcopy
      | assignFixed column row value =>
          exact inductionHypothesis hcoherent.2 hcopy
      | enableGate gate row =>
          exact inductionHypothesis hcoherent.2 hcopy
      | enableLookup argument selectors row =>
          exact inductionHypothesis hcoherent.2 hcopy

/-- Both endpoints of every coherent layouter copy use registered permutation
columns. -/
theorem operationDeclaredCopies_permutationColumns
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hcoherent : OperationsKeygenCoherent cs operations)
    (copy : DeclaredCopy Fp) (hcopy : copy ∈ operationDeclaredCopies operations) :
    copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs := by
  induction operations with
  | nil => simp [operationDeclaredCopies] at hcopy
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          obtain ⟨hbody, hrest⟩ :=
            (OperationsKeygenCoherent.region_cons cs name body rest).mp hcoherent
          rw [operationDeclaredCopies, List.mem_append] at hcopy
          rcases hcopy with hcopy | hcopy
          · exact regionDeclaredCopies_permutationColumns cs body hbody copy hcopy
          · exact inductionHypothesis hrest hcopy
      | constrainInstance cell column row =>
          obtain ⟨hcell, hcolumn, hrest⟩ :=
            (OperationsKeygenCoherent.constrainInstance_cons
              cs cell column row rest).mp hcoherent
          rw [operationDeclaredCopies, List.mem_cons] at hcopy
          rcases hcopy with rfl | hcopy
          · exact ⟨hcell, hcolumn⟩
          · exact inductionHypothesis hrest hcopy
      | loadTable table values =>
          have hrest :=
            (OperationsKeygenCoherent.loadTable_cons
              cs table values rest).mp hcoherent
          exact inductionHypothesis hrest.2 hcopy

/-- Every endpoint extracted from a coherent copy stream carries its registered
permutation-column fact. -/
theorem declaredEndpoint_permutationColumnRegistered
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hcoherent : OperationsKeygenCoherent cs operations)
    (endpoint : CopyEndpoint Fp)
    (hendpoint : endpoint ∈
      (operationDeclaredCopies operations).flatMap fun copy => [copy.1, copy.2]) :
    endpoint.PermutationColumnRegistered cs := by
  rw [List.mem_flatMap] at hendpoint
  obtain ⟨copy, hcopy, hendpoint⟩ := hendpoint
  have hcolumns := operationDeclaredCopies_permutationColumns
    cs operations hcoherent copy hcopy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with rfl | rfl
  · exact hcolumns.1
  · exact hcolumns.2

/-- Every equality/instance copy emitted by a registered region uses in-range
permutation columns. -/
theorem regionCopiesSplit_fst_columns_lt
    (cs : ConstraintSystem Fp) (body : RegionOperations Fp)
    (hregistered : body.Forall (RegionOperation.KeygenCoherent cs))
    (starts : List ℕ) (consts : List (ℕ × ℕ × ℕ))
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ (regionCopiesSplit
      (Halo2.Layout.permColsOf cs) starts body consts).1) :
    tuple.1 < (Halo2.Layout.permColsOf cs).length ∧
      tuple.2.2.1 < (Halo2.Layout.permColsOf cs).length := by
  simp only [regionCopiesSplit] at htuple
  rw [List.mem_filterMap] at htuple
  obtain ⟨operation, hoperation, htuple⟩ := htuple
  have hoperationRegistered :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | constrainEqual left right =>
      simp only at htuple
      obtain rfl := Option.some.inj htuple
      constructor <;>
        apply permIndex_lt_length_of_mem <;>
        rw [Halo2.Layout.permColsOf_map_toAny]
      · exact hoperationRegistered.1
      · exact hoperationRegistered.2
  | constrainInstance cell column row =>
      simp only at htuple
      obtain rfl := Option.some.inj htuple
      constructor <;>
        apply permIndex_lt_length_of_mem <;>
        rw [Halo2.Layout.permColsOf_map_toAny]
      · exact hoperationRegistered.1
      · exact hoperationRegistered.2
  | constrainConstant cell value => simp at htuple
  | assignAdvice column row value => simp at htuple
  | assignFixed column row value => simp at htuple
  | enableGate gate row => simp at htuple
  | enableLookup argument enabled row => simp at htuple

/-- The equality/instance half of V1's copy walk is column-safe for every keygen-lawful
operation stream. -/
theorem V1_go_fst_columns_lt
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs ops)
    (starts : List ℕ) (consts : List (ℕ × ℕ × ℕ))
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ (V1.go
      (Halo2.Layout.permColsOf cs) starts ops consts).1.1) :
    tuple.1 < (Halo2.Layout.permColsOf cs).length ∧
      tuple.2.2.1 < (Halo2.Layout.permColsOf cs).length := by
  induction ops generalizing consts with
  | nil => simp [V1.go] at htuple
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          obtain ⟨hbody, hrest⟩ :=
            (OperationsKeygenCoherent.region_cons cs name body rest).mp
              hregistered
          rcases hsplit : regionCopiesSplit (Halo2.Layout.permColsOf cs)
              starts body consts with
            ⟨equalities, constants, remainingConstants⟩
          rcases hgo : V1.go (Halo2.Layout.permColsOf cs) starts
              rest remainingConstants with
            ⟨⟨restEqualities, restConstants⟩, finalConstants⟩
          simp only [V1.go, hsplit, hgo] at htuple
          rcases List.mem_append.mp htuple with htuple | htuple
          · apply regionCopiesSplit_fst_columns_lt cs body hbody
              starts consts tuple
            rwa [hsplit]
          · exact inductionHypothesis hrest remainingConstants (by
              rwa [hgo])
      | constrainInstance cell column row =>
          obtain ⟨hcell, hcolumn, hrest⟩ :=
            (OperationsKeygenCoherent.constrainInstance_cons
              cs cell column row rest).mp hregistered
          rcases hgo : V1.go (Halo2.Layout.permColsOf cs) starts rest consts with
            ⟨⟨restEqualities, restConstants⟩, finalConstants⟩
          simp only [V1.go, hgo, List.mem_cons] at htuple
          rcases htuple with rfl | htuple
          · constructor <;>
              apply permIndex_lt_length_of_mem <;>
              rw [Halo2.Layout.permColsOf_map_toAny]
            · exact hcell
            · exact hcolumn
          · exact inductionHypothesis hrest consts (by rwa [hgo])
      | loadTable table values =>
          have hrest :=
            (OperationsKeygenCoherent.loadTable_cons
              cs table values rest).mp hregistered
          exact inductionHypothesis hrest.2 consts (by
            simpa only [V1.go] using htuple)

/-- The declared-copy extraction is a `filterMap`. -/
theorem regionDeclaredCopies_eq_filterMap (body : RegionOperations Fp) :
    regionDeclaredCopies body = body.filterMap regionOperationDeclaredCopy? := by
  induction body with
  | nil => rfl
  | cons op rest ih =>
      rw [regionDeclaredCopies, List.filterMap_cons]
      cases hop : regionOperationDeclaredCopy? (F := Fp) op with
      | none => simpa [hop] using ih
      | some copy => simpa [hop] using ih

/-- Both endpoints of a region copy lie inside the complete operation footprint. -/
theorem regionDeclaredCopies_rows
    (root : Operations Fp) (name : String) (body : RegionOperations Fp)
    (hregion : Operation.region name body ∈ root)
    (copy : DeclaredCopy Fp) (hcopy : copy ∈ regionDeclaredCopies body) :
    copy.1.WithinRows (FloorPlanner.V1.starts root) (Halo2.usedRows root) ∧
      copy.2.WithinRows (FloorPlanner.V1.starts root) (Halo2.usedRows root) := by
  rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hcopy
  obtain ⟨operation, hoperation, hcopy⟩ := hcopy
  cases operation with
  | constrainEqual left right =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact cells_row_lt_usedRows_of_constrainEqual_mem
        root name body hregion left right hoperation
  | constrainConstant cell value =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact ⟨cell_row_lt_usedRows_of_constrainConstant_mem
        root name body hregion cell value hoperation, trivial⟩
  | constrainInstance cell column row =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact rows_lt_usedRows_of_region_constrainInstance_mem
        root name body hregion cell column row hoperation
  | assignAdvice column row witness => simp [regionOperationDeclaredCopy?] at hcopy
  | assignFixed column row value => simp [regionOperationDeclaredCopy?] at hcopy
  | enableGate gate row => simp [regionOperationDeclaredCopy?] at hcopy
  | enableLookup argument selectors row => simp [regionOperationDeclaredCopy?] at hcopy

/-- Both endpoints of every layouter copy lie inside the complete operation
footprint. -/
theorem operationDeclaredCopies_rows
    (operations : Operations Fp) (copy : DeclaredCopy Fp)
    (hcopy : copy ∈ operationDeclaredCopies operations) :
    copy.1.WithinRows (FloorPlanner.V1.starts operations) (Halo2.usedRows operations) ∧
      copy.2.WithinRows (FloorPlanner.V1.starts operations) (Halo2.usedRows operations) := by
  have auxiliary : ∀ current : Operations Fp,
      (∀ operation ∈ current, operation ∈ operations) →
      copy ∈ operationDeclaredCopies current →
      copy.1.WithinRows (FloorPlanner.V1.starts operations) (Halo2.usedRows operations) ∧
        copy.2.WithinRows (FloorPlanner.V1.starts operations) (Halo2.usedRows operations) := by
    intro current hcurrent hcopy
    induction current with
    | nil => simp [operationDeclaredCopies] at hcopy
    | cons operation rest inductionHypothesis =>
        have hrest : ∀ next ∈ rest, next ∈ operations := by
          intro next hnext
          exact hcurrent next (List.mem_cons_of_mem operation hnext)
        cases operation with
        | region name body =>
            rw [operationDeclaredCopies, List.mem_append] at hcopy
            rcases hcopy with hbody | hcopy
            · exact regionDeclaredCopies_rows operations name body
                (hcurrent (.region name body) (by simp)) copy hbody
            · exact inductionHypothesis hrest hcopy
        | constrainInstance cell column row =>
            rw [operationDeclaredCopies, List.mem_cons] at hcopy
            rcases hcopy with rfl | hcopy
            · exact rows_lt_usedRows_of_constrainInstance_mem
                operations cell column row
                (hcurrent (.constrainInstance cell column row) (by simp))
            · exact inductionHypothesis hrest hcopy
        | loadTable table values =>
            exact inductionHypothesis hrest hcopy
  exact auxiliary operations (fun _ hoperation => hoperation) hcopy

/-- Every endpoint extracted from a copy stream lies inside the complete operation
footprint. -/
theorem declaredEndpoint_rows
    (operations : Operations Fp) (endpoint : CopyEndpoint Fp)
    (hendpoint : endpoint ∈
      (operationDeclaredCopies operations).flatMap fun copy => [copy.1, copy.2]) :
    endpoint.WithinRows
      (FloorPlanner.V1.starts operations) (Halo2.usedRows operations) := by
  rw [List.mem_flatMap] at hendpoint
  obtain ⟨copy, hcopy, hendpoint⟩ := hendpoint
  have hrows := operationDeclaredCopies_rows operations copy hcopy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with rfl | rfl
  · exact hrows.1
  · exact hrows.2

/-- A resolvable declared copy of a region body is among the region's extracted
equality/instance copies. -/
theorem mem_regionCopiesSplit_fst_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ regionDeclaredCopies body) :
    tuple ∈ (regionCopiesSplit permCols starts body consts).1 := by
  rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hmem
  obtain ⟨op, hop, hcopy⟩ := hmem
  simp only [regionCopiesSplit]
  rw [List.mem_filterMap]
  refine ⟨op, hop, ?_⟩
  cases op with
  | constrainEqual a b =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainInstance cell col row =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainConstant cell value =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp [resolveDeclared] at hres
  | assignAdvice col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | assignFixed col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | enableGate gate off => simp [regionOperationDeclaredCopy?] at hcopy
  | enableLookup arg enabled off => simp [regionOperationDeclaredCopy?] at hcopy

/-- **Every resolvable declared copy is in the V1 copy list**: region-local copies land
in their region's extracted stream, layouter-level instance copies inline, and the
whole equality/instance stream prefixes the copy list. -/
theorem mem_V1_copyList_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ operationDeclaredCopies ops) :
    tuple ∈ V1.copyList permCols starts ops consts := by
  suffices h : tuple ∈ (V1.go permCols starts ops consts).1.1 by
    rw [V1.copyList]
    exact List.mem_append_left _ h
  induction ops generalizing consts with
  | nil => simp [operationDeclaredCopies] at hmem
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [operationDeclaredCopies] at hmem
          rcases hsplit : regionCopiesSplit permCols starts body consts with
            ⟨eqs, cnsts, cs'⟩
          rcases hgo : V1.go permCols starts rest cs' with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hsplit, hgo]
          rcases List.mem_append.mp hmem with hcopy | hcopy
          · refine List.mem_append_left _ ?_
            have := mem_regionCopiesSplit_fst_of_declared permCols starts body consts
              copy tuple hres hcopy
            rwa [hsplit] at this
          · refine List.mem_append_right _ ?_
            have := ih cs' hcopy
            rwa [hgo] at this
      | constrainInstance cell col row =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          rcases List.mem_cons.mp hmem with hcopy | hcopy
          · subst hcopy
            simp only [resolveDeclared] at hres
            obtain rfl := Option.some.inj hres
            exact List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ ?_
            have := ih consts hcopy
            rwa [hgo] at this
      | loadTable tbl values =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          have := ih consts hmem
          rwa [hgo] at this

/-- The equality/instance half of one region's keygen copy stream stays within the
complete operation footprint. -/
theorem regionCopiesSplit_fst_rows_lt_usedRows
    (root : Operations Fp) (name : String) (body : RegionOperations Fp)
    (hregion : Operation.region name body ∈ root)
    (permCols : List ColRef) (consts : List (ℕ × ℕ × ℕ))
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈
      (regionCopiesSplit permCols (FloorPlanner.V1.starts root)
        body consts).1) :
    tuple.2.1 < Halo2.usedRows root ∧
      tuple.2.2.2 < Halo2.usedRows root := by
  simp only [regionCopiesSplit] at htuple
  rw [List.mem_filterMap] at htuple
  obtain ⟨operation, hoperation, htuple⟩ := htuple
  cases operation with
  | constrainEqual left right =>
      simp only at htuple
      obtain rfl := Option.some.inj htuple
      simpa only [resolveCell, place] using
        cells_row_lt_usedRows_of_constrainEqual_mem
          root name body hregion left right hoperation
  | constrainInstance cell column row =>
      simp only at htuple
      obtain rfl := Option.some.inj htuple
      simpa only [resolveCell, place] using
        rows_lt_usedRows_of_region_constrainInstance_mem
          root name body hregion cell column row hoperation
  | constrainConstant cell value => simp at htuple
  | assignAdvice column row value => simp at htuple
  | assignFixed column row value => simp at htuple
  | enableGate gate row => simp at htuple
  | enableLookup argument enabled row => simp at htuple

/-- Every tuple in V1's equality/instance stream stays within the complete operation
footprint. This is structural: the stream contains only the corresponding declared
copy operations. -/
theorem V1_go_fst_rows_lt_usedRows
    (root current : Operations Fp)
    (hcurrent : ∀ operation ∈ current, operation ∈ root)
    (permCols : List ColRef) (consts : List (ℕ × ℕ × ℕ))
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈
      (V1.go permCols (FloorPlanner.V1.starts root) current consts).1.1) :
    tuple.2.1 < Halo2.usedRows root ∧
      tuple.2.2.2 < Halo2.usedRows root := by
  induction current generalizing consts with
  | nil => simp [V1.go] at htuple
  | cons operation rest inductionHypothesis =>
      have hrest : ∀ next ∈ rest, next ∈ root := by
        intro next hnext
        exact hcurrent next (List.mem_cons_of_mem operation hnext)
      cases operation with
      | region name body =>
          rcases hsplit : regionCopiesSplit permCols
              (FloorPlanner.V1.starts root) body consts with
            ⟨equalities, constants, remainingConstants⟩
          rcases hgo : V1.go permCols (FloorPlanner.V1.starts root)
              rest remainingConstants with
            ⟨⟨restEqualities, restConstants⟩, finalConstants⟩
          simp only [V1.go, hsplit, hgo] at htuple
          rcases List.mem_append.mp htuple with htuple | htuple
          · apply regionCopiesSplit_fst_rows_lt_usedRows
              root name body (hcurrent (.region name body) (by simp))
              permCols consts tuple
            rwa [hsplit]
          · exact inductionHypothesis hrest remainingConstants (by
              rwa [hgo])
      | constrainInstance cell column row =>
          rcases hgo : V1.go permCols (FloorPlanner.V1.starts root)
              rest consts with
            ⟨⟨restEqualities, restConstants⟩, finalConstants⟩
          simp only [V1.go, hgo, List.mem_cons] at htuple
          rcases htuple with rfl | htuple
          · simpa only [resolveCell, place] using
              rows_lt_usedRows_of_constrainInstance_mem
                root cell column row
                (hcurrent (.constrainInstance cell column row) (by simp))
          · exact inductionHypothesis hrest consts (by rwa [hgo])
      | loadTable table values =>
          rcases hgo : V1.go permCols (FloorPlanner.V1.starts root)
              rest consts with
            ⟨⟨restEqualities, restConstants⟩, finalConstants⟩
          exact inductionHypothesis hrest consts (by
            simpa only [V1.go, hgo] using htuple)

/-- Decode raw copy tuples into typed cells under a bounds certificate. -/
def decodeCopies (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    List (FlatCell numCols n × FlatCell numCols n) :=
  raw.attach.map fun t =>
    ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
      (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))

/-- Decoding then re-encoding is the identity: the bounds certificate is the whole
content of the `hcopies` hypothesis. -/
theorem decodeCopies_map (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    (decodeCopies numCols n raw h).map
        (fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) = raw := by
  rw [decodeCopies, List.map_map]
  have : (fun (t : { x // x ∈ raw }) => t.1) =
      ((fun p : (FlatCell numCols n × FlatCell numCols n) =>
          (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) ∘
        fun t : { x // x ∈ raw } =>
          ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
            (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))) := by
    funext t
    rfl
  rw [← this]
  exact List.attach_map_subtype_val raw

/-- The constant-declaration sites of a region body, in body order. -/
def constSites : RegionOperations Fp → List (Cell × Fp)
  | [] => []
  | .constrainConstant cell value :: rest => (cell, value) :: constSites rest
  | _ :: rest => constSites rest

/-- The value contribution of one region operation to V1's constant stream. -/
def regionConstantValue? : RegionOperation Fp → Option Fp
  | .constrainConstant _ value => some value
  | _ => none

/-- The constants half of a region's copy extraction, in closed zipped form: each
constant site pairs with the next allocation-map entry — the constants cell on the
left, the site's resolved cell on the right — and the tail of the map is returned. -/
theorem regionCopiesSplit_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ))
    (hlen : (constSites body).length ≤ consts.length) :
    (regionCopiesSplit permCols starts body consts).2.1 =
      ((constSites body).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (regionCopiesSplit permCols starts body consts).2.2 =
        consts.drop (constSites body).length := by
  induction body generalizing consts with
  | nil => exact ⟨rfl, rfl⟩
  | cons op rest ih =>
      cases op with
      | constrainConstant cell value =>
          cases consts with
          | nil => simp [constSites] at hlen
          | cons entry cs =>
              have hlen' : (constSites rest).length ≤ cs.length := by
                simpa [constSites] using hlen
              obtain ⟨ih1, ih2⟩ := ih cs hlen'
              constructor
              · show (permIndex permCols (ColRef.toAny (.fixed entry.2.1)), entry.2.2,
                    (resolveCell permCols starts cell).1,
                    (resolveCell permCols starts cell).2) ::
                    (regionCopiesSplit permCols starts rest cs).2.1 = _
                rw [ih1]
                rfl
              · show (regionCopiesSplit permCols starts rest cs).2.2 = _
                rw [ih2]
                rfl
      | constrainEqual a b =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | constrainInstance cell col row =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | assignAdvice col off val =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | assignFixed col off val =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | enableGate gate off =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩
      | enableLookup arg enabled off =>
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [constSites] using hlen)
          exact ⟨ih1, ih2⟩

/-- Zipping ignores the second list beyond the first's length. -/
theorem zip_take_length {α β : Type*} (a : List α) (c : List β) :
    a.zip (c.take a.length) = a.zip c := by
  induction a generalizing c with
  | nil => rfl
  | cons x xs ih =>
      cases c with
      | nil => rfl
      | cons y ys => simp [ih]

/-- The constant-declaration sites of a whole operation stream: region sites in region
order (V1 defers them all to the end of synthesis, in this order). -/
def operationConstSites : Operations Fp → List (Cell × Fp)
  | [] => []
  | .region _ body :: rest => constSites body ++ operationConstSites rest
  | .constrainInstance _ _ _ :: rest => operationConstSites rest
  | .loadTable _ _ :: rest => operationConstSites rest

/-- A region constant site comes from the corresponding `constrainConstant`
operation. -/
theorem constrainConstant_mem_of_mem_constSites
    (body : RegionOperations Fp) (cell : Cell) (value : Fp)
    (hsite : (cell, value) ∈ constSites body) :
    RegionOperation.constrainConstant cell value ∈ body := by
  induction body with
  | nil => simp [constSites] at hsite
  | cons operation rest inductionHypothesis =>
      cases operation with
      | constrainConstant foundCell foundValue =>
          simp only [constSites, List.mem_cons] at hsite ⊢
          rcases hsite with hsite | hsite
          · obtain ⟨rfl, rfl⟩ := hsite
            exact Or.inl rfl
          · exact Or.inr (inductionHypothesis hsite)
      | constrainEqual
      | constrainInstance
      | assignAdvice
      | assignFixed
      | enableGate
      | enableLookup =>
          exact List.mem_cons_of_mem _
            (inductionHypothesis (by simpa [constSites] using hsite))

/-- A registered region's constant sites lie on equality-enabled columns. -/
theorem constantSite_column_mem_permutationColumns
    (cs : ConstraintSystem Fp) (body : RegionOperations Fp)
    (hregistered : body.Forall (RegionOperation.KeygenCoherent cs))
    {cell : Cell} {value : Fp}
    (hsite : (cell, value) ∈ constSites body) :
    cell.column ∈ cs.permutationColumns := by
  have hoperation := constrainConstant_mem_of_mem_constSites
    body cell value hsite
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered
      (.constrainConstant cell value) hoperation
  exact hregisteredOperation

/-- Every constant site in a keygen-lawful operation stream lies on an
equality-enabled column. -/
theorem operationConstSite_column_mem_permutationColumns
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs operations)
    {cell : Cell} {value : Fp}
    (hsite : (cell, value) ∈ operationConstSites operations) :
    cell.column ∈ cs.permutationColumns := by
  induction operations with
  | nil => simp [operationConstSites] at hsite
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          obtain ⟨hbody, hrest⟩ :=
            (OperationsKeygenCoherent.region_cons cs name body rest).mp
              hregistered
          rcases List.mem_append.mp hsite with hbodySite | hrestSite
          · exact constantSite_column_mem_permutationColumns
              cs body hbody hbodySite
          · exact inductionHypothesis hrest hrestSite
      | constrainInstance cell column row =>
          have hrest :=
            (OperationsKeygenCoherent.constrainInstance_cons
              cs cell column row rest).mp hregistered |>.2.2
          exact inductionHypothesis hrest hsite
      | loadTable table values =>
          have hrest :=
            (OperationsKeygenCoherent.loadTable_cons
              cs table values rest).mp hregistered
          exact inductionHypothesis hrest.2 hsite

/-- A whole-stream constant site lies below the compiler-derived operation
footprint. -/
theorem constantSite_row_lt_usedRows
    (operations : Operations Fp) (cell : Cell) (value : Fp)
    (hsite : (cell, value) ∈ operationConstSites operations) :
    (FloorPlanner.V1.starts operations).getD cell.regionIndex 0 +
        cell.rowOffset <
      Halo2.usedRows operations := by
  have auxiliary :
      ∀ current : Operations Fp,
        (∀ operation ∈ current, operation ∈ operations) →
        (cell, value) ∈ operationConstSites current →
        (FloorPlanner.V1.starts operations).getD cell.regionIndex 0 +
            cell.rowOffset <
          Halo2.usedRows operations := by
    intro current hcurrent hcurrentSite
    induction current with
    | nil => simp [operationConstSites] at hcurrentSite
    | cons operation rest inductionHypothesis =>
        have hrest : ∀ next ∈ rest, next ∈ operations := by
          intro next hnext
          exact hcurrent next (List.mem_cons_of_mem operation hnext)
        cases operation with
        | region name body =>
            rw [operationConstSites, List.mem_append] at hcurrentSite
            rcases hcurrentSite with hbody | hrestSite
            · apply cell_row_lt_usedRows_of_constrainConstant_mem
                operations name body
                (hcurrent (.region name body) (by simp)) cell value
              exact constrainConstant_mem_of_mem_constSites
                body cell value hbody
            · exact inductionHypothesis hrest hrestSite
        | constrainInstance copyCell column row =>
            exact inductionHypothesis hrest (by
              simpa [operationConstSites] using hcurrentSite)
        | loadTable table values =>
            exact inductionHypothesis hrest (by
              simpa [operationConstSites] using hcurrentSite)
  exact auxiliary operations (fun _ hoperation => hoperation) hsite

/-- The values retained by `constSites` are exactly the region operations'
`constrainConstant` values, in the same order. -/
theorem constSites_map_snd (body : RegionOperations Fp) :
    (constSites body).map Prod.snd =
      FloorPlanner.V1.regionConstantValues body := by
  induction body with
  | nil => rfl
  | cons operation rest ih =>
      cases operation <;>
        simp [constSites, FloorPlanner.V1.regionConstantValues, ih]

/-- Walking indexed regions and walking the operation stream directly collect the
same constant values in the same order. Region indices do not affect this stream. -/
theorem indexedRegions_constantValues
    (ops : Operations Fp) (nextRegion : ℕ) :
    ((indexedRegions ops nextRegion).1.flatMap fun (_, body) =>
      FloorPlanner.V1.regionConstantValues body) =
      (operationConstSites ops).map Prod.snd := by
  induction ops generalizing nextRegion with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, operationConstSites, List.map_append,
            List.flatMap_cons]
          rw [ih, constSites_map_snd]
      | constrainInstance cell column row =>
          simpa only [indexedRegions, operationConstSites] using ih nextRegion
      | loadTable table values =>
          simpa only [indexedRegions, operationConstSites] using ih nextRegion

/-- V1's planner value stream is the value projection of the semantic bridge's
constant-site stream. This is an algorithmic identity, independent of any circuit. -/
theorem operationConstSites_map_snd (ops : Operations Fp) :
    (operationConstSites ops).map Prod.snd =
      FloorPlanner.V1.constantValues ops := by
  unfold FloorPlanner.V1.constantValues
  symm
  exact indexedRegions_constantValues ops 0

theorem operationConstSites_length (ops : Operations Fp) :
    (operationConstSites ops).length =
      (FloorPlanner.V1.constantValues ops).length := by
  rw [← operationConstSites_map_snd, List.length_map]

/-- Positional V1 allocation preserves each constant site's value. The only premise
is allocation completeness; no concrete circuit computation is involved. -/
theorem constantAllocation_value
    (ops : Operations Fp) (constantColumns : List ℕ)
    {site : Cell × Fp} {entry : ℕ × ℕ × ℕ}
    (hfit :
      (operationConstSites ops).length ≤
        (FloorPlanner.V1.constantAssignments ops constantColumns).length)
    (hallocation :
      (site, entry) ∈
        (operationConstSites ops).zip
          ((FloorPlanner.V1.constantAssignments ops constantColumns).map
            fun (value, column, row) => (value.val, column, row))) :
    entry.1 = site.2.val := by
  have hvalues := operationConstSites_map_snd ops
  have hfull :
      (FloorPlanner.V1.constantValues ops).length ≤
        (FloorPlanner.V1.constantAssignments ops constantColumns).length := by
    rw [← hvalues]
    simpa only [List.length_map] using hfit
  have hallocations :=
    FloorPlanner.V1.constantAssignments_map_fst ops constantColumns hfull
  have hallocationValues :
      ((FloorPlanner.V1.constantAssignments ops constantColumns).map
        fun (value, column, row) => (value.val, column, row)).map Prod.fst =
          (FloorPlanner.V1.constantValues ops).map ZMod.val := by
    simpa only [List.map_map, Function.comp_apply] using
      congrArg (List.map ZMod.val) hallocations
  have hmapped :
      (site.2, entry.1) ∈
        ((operationConstSites ops).zip
          ((FloorPlanner.V1.constantAssignments ops constantColumns).map
            fun (value, column, row) => (value.val, column, row))).map
            (fun allocation => (allocation.1.2, allocation.2.1)) :=
    List.mem_map.mpr ⟨(site, entry), hallocation, rfl⟩
  have hmapped' :
      (site.2, entry.1) ∈
        ((operationConstSites ops).map Prod.snd).zip
          (((FloorPlanner.V1.constantAssignments ops constantColumns).map
            fun (value, column, row) => (value.val, column, row)).map
              Prod.fst) := by
    simpa only [List.zip_map] using hmapped
  rw [hvalues, hallocationValues] at hmapped'
  have hzipped :
      (FloorPlanner.V1.constantValues ops).zip
          ((FloorPlanner.V1.constantValues ops).map ZMod.val) =
        (FloorPlanner.V1.constantValues ops).map fun value =>
          (value, ZMod.val value) := by
    have hmap :
        ((FloorPlanner.V1.constantValues ops).map id).zip
            ((FloorPlanner.V1.constantValues ops).map ZMod.val) =
          (FloorPlanner.V1.constantValues ops).map fun value =>
            (id value, ZMod.val value) :=
      List.zip_map'
    simpa only [List.map_id, id_eq] using hmap
  rw [hzipped] at hmapped'
  rcases List.mem_map.mp hmapped' with ⟨value, -, hvalue⟩
  have hsite : value = site.2 :=
    congrArg Prod.fst hvalue
  have hentry : value.val = entry.1 :=
    congrArg Prod.snd hvalue
  rw [← hsite]
  exact hentry.symm

/-- A declared region constant copy occurs in the region's positional constants stream. -/
theorem mem_constSites_of_declared_constant
    (body : RegionOperations Fp) (cell : Cell) (value : Fp)
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        regionDeclaredCopies body) :
    (cell, value) ∈ constSites body := by
  induction body with
  | nil =>
      simp [regionDeclaredCopies] at hcopy
  | cons operation rest ih =>
      cases operation with
      | constrainConstant assignedCell assignedValue =>
          rw [regionDeclaredCopies, constSites] at *
          simp only [regionOperationDeclaredCopy?, List.mem_cons] at hcopy
          rcases hcopy with heq | hrest
          · obtain ⟨rfl, rfl⟩ := heq
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hrest)
      | constrainEqual left right =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | constrainInstance copyCell column row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | assignAdvice column row value =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | assignFixed column row value =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | enableGate gate row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)
      | enableLookup argument enabled row =>
          exact ih (by
            simpa [regionDeclaredCopies, regionOperationDeclaredCopy?] using hcopy)

/-- A declared constant copy occurs in V1's whole-synthesis positional stream. -/
theorem mem_operationConstSites_of_declared_constant
    (ops : Operations Fp) (cell : Cell) (value : Fp)
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        operationDeclaredCopies ops) :
    (cell, value) ∈ operationConstSites ops := by
  induction ops with
  | nil =>
      simp [operationDeclaredCopies] at hcopy
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites, List.mem_append]
          rcases List.mem_append.mp hcopy with hbody | hrest
          · exact Or.inl
              (mem_constSites_of_declared_constant body cell value hbody)
          · exact Or.inr (ih hrest)
      | constrainInstance copyCell column row =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites]
          rcases List.mem_cons.mp hcopy with heq | hrest
          · cases heq
          · exact ih hrest
      | loadTable table values =>
          rw [operationDeclaredCopies] at hcopy
          rw [operationConstSites]
          exact ih hcopy

/-- Every member of the left list occurs in its zip when the right list is long enough. -/
theorem exists_mem_zip_of_mem_left
    {α β : Type} (left : List α) (right : List β)
    (hlen : left.length ≤ right.length)
    {value : α} (hvalue : value ∈ left) :
    ∃ paired, (value, paired) ∈ left.zip right := by
  induction left generalizing right with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      cases right with
      | nil =>
          simp at hlen
      | cons paired rest =>
          rw [List.mem_cons] at hvalue
          rcases hvalue with rfl | htail
          · exact ⟨paired, List.mem_cons_self⟩
          · have hlen' : tail.length ≤ rest.length := by
              simpa using hlen
            obtain ⟨other, hother⟩ := ih rest hlen' htail
            exact ⟨other, List.mem_cons_of_mem _ hother⟩

/-- The V1 constants stream in closed zipped form: every constant site across the
stream pairs with its allocation-map entry, in region-then-body order. -/
theorem V1_go_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ))
    (hlen : (operationConstSites ops).length ≤ consts.length) :
    (V1.go permCols starts ops consts).1.2 =
      ((operationConstSites ops).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (V1.go permCols starts ops consts).2 =
        consts.drop (operationConstSites ops).length := by
  induction ops generalizing consts with
  | nil => exact ⟨rfl, rfl⟩
  | cons op rest ih =>
      cases op with
      | region name body =>
          have hbody : (constSites body).length ≤ consts.length := by
            refine le_trans ?_ hlen
            simp [operationConstSites]
          obtain ⟨hsplit1, hsplit2⟩ :=
            regionCopiesSplit_snd_eq permCols starts body consts hbody
          have hrest : (operationConstSites rest).length ≤
              (consts.drop (constSites body).length).length := by
            rw [List.length_drop]
            have := hlen
            simp only [operationConstSites, List.length_append] at this
            omega
          rcases hsplitEq : regionCopiesSplit permCols starts body consts with
            ⟨eqs, cnsts, cs'⟩
          rcases hgoEq : V1.go permCols starts rest cs' with ⟨⟨r1, r2⟩, cs''⟩
          have hcs' : cs' = consts.drop (constSites body).length := by
            rw [hsplitEq] at hsplit2
            exact hsplit2
          obtain ⟨ih1, ih2⟩ := ih (consts.drop (constSites body).length)
            hrest
          constructor
          · show (V1.go permCols starts (.region name body :: rest) consts).1.2 = _
            simp only [V1.go, hsplitEq, hgoEq]
            have hcnsts : cnsts = ((constSites body).zip consts).map (fun se =>
                (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
                  (resolveCell permCols starts se.1.1).1,
                  (resolveCell permCols starts se.1.1).2)) := by
              rw [hsplitEq] at hsplit1
              exact hsplit1
            rw [hcnsts]
            have hr2 : r2 = ((operationConstSites rest).zip
                (consts.drop (constSites body).length)).map (fun se =>
                (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
                  (resolveCell permCols starts se.1.1).1,
                  (resolveCell permCols starts se.1.1).2)) := by
              rw [hcs'] at hgoEq
              rw [hgoEq] at ih1
              exact ih1
            rw [hr2]
            conv_rhs =>
              rw [show operationConstSites (.region name body :: rest) =
                constSites body ++ operationConstSites rest from rfl,
                show consts = consts.take (constSites body).length ++
                  consts.drop (constSites body).length from
                  (List.take_append_drop _ _).symm]
            rw [List.zip_append (by rw [List.length_take]; omega),
              List.map_append, zip_take_length]
          · show (V1.go permCols starts (.region name body :: rest) consts).2 = _
            simp only [V1.go, hsplitEq, hgoEq]
            have : cs'' = (consts.drop (constSites body).length).drop
                (operationConstSites rest).length := by
              rw [hcs'] at hgoEq
              rw [hgoEq] at ih2
              exact ih2
            rw [this, List.drop_drop]
            rw [show operationConstSites (.region name body :: rest) =
              constSites body ++ operationConstSites rest from rfl]
            rw [List.length_append]
      | constrainInstance cell col row =>
          rcases hgoEq : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [operationConstSites] using hlen)
          rw [hgoEq] at ih1 ih2
          exact ⟨by simp only [V1.go, hgoEq]; exact ih1,
            by simp only [V1.go, hgoEq]; exact ih2⟩
      | loadTable tbl values =>
          rcases hgoEq : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          obtain ⟨ih1, ih2⟩ := ih consts (by simpa [operationConstSites] using hlen)
          rw [hgoEq] at ih1 ih2
          exact ⟨by simp only [V1.go, hgoEq]; exact ih1,
            by simp only [V1.go, hgoEq]; exact ih2⟩

/-- Every tuple in the V1 copy list lies below the compiler-derived operation
footprint. Constant allocations need only be present positionally and carry their
generic planner row bound; no concrete circuit computation is involved. -/
theorem V1_copyList_rows_lt_usedRows
    (operations : Operations Fp) (permCols : List ColRef)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit :
      (operationConstSites operations).length ≤ constants.length)
    (hconstantRows :
      ∀ entry ∈ constants, entry.2.2 < Halo2.usedRows operations)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈
      V1.copyList permCols (FloorPlanner.V1.starts operations)
        operations constants) :
    tuple.2.1 < Halo2.usedRows operations ∧
      tuple.2.2.2 < Halo2.usedRows operations := by
  rw [V1.copyList, List.mem_append] at htuple
  rcases htuple with hequality | hconstant
  · exact V1_go_fst_rows_lt_usedRows operations operations
      (fun _ hoperation => hoperation) permCols constants tuple hequality
  · have hconstants :=
      (V1_go_snd_eq permCols (FloorPlanner.V1.starts operations)
        operations constants hfit).1
    rw [hconstants, List.mem_map] at hconstant
    obtain ⟨⟨⟨cell, value⟩, entry⟩, hallocation, htuple⟩ := hconstant
    have hsite : (cell, value) ∈ operationConstSites operations :=
      (List.of_mem_zip hallocation).1
    have hentry : entry ∈ constants :=
      (List.of_mem_zip hallocation).2
    obtain rfl := htuple
    exact ⟨hconstantRows entry hentry,
      constantSite_row_lt_usedRows operations cell value hsite⟩

/-- Every tuple in V1's copy list uses in-range permutation columns whenever synthesis
is keygen-lawful and the planner's constants allocation uses configured constant
columns. -/
theorem V1_copyList_columns_lt
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs operations)
    (starts : List ℕ) (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites operations).length ≤ constants.length)
    (hconstantColumns : ∀ entry ∈ constants,
      (AnyColumn.mk .fixed entry.2.1) ∈ cs.permutationColumns)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ V1.copyList
      (Halo2.Layout.permColsOf cs) starts operations constants) :
    tuple.1 < (Halo2.Layout.permColsOf cs).length ∧
      tuple.2.2.1 < (Halo2.Layout.permColsOf cs).length := by
  rw [V1.copyList, List.mem_append] at htuple
  rcases htuple with hequality | hconstant
  · exact V1_go_fst_columns_lt cs operations hregistered
      starts constants tuple hequality
  · have hconstants :=
      (V1_go_snd_eq (Halo2.Layout.permColsOf cs) starts
        operations constants hfit).1
    rw [hconstants, List.mem_map] at hconstant
    obtain ⟨⟨⟨cell, value⟩, entry⟩, hallocation, htuple⟩ := hconstant
    have hsite : (cell, value) ∈ operationConstSites operations :=
      (List.of_mem_zip hallocation).1
    have hentry : entry ∈ constants :=
      (List.of_mem_zip hallocation).2
    obtain rfl := htuple
    constructor <;>
      apply permIndex_lt_length_of_mem <;>
      rw [Halo2.Layout.permColsOf_map_toAny]
    · exact hconstantColumns entry hentry
    · exact operationConstSite_column_mem_permutationColumns
        cs operations hregistered hsite

/-- Every declared copy has a `Cell` left endpoint, and its right endpoint is a cell,
an instance read, or a constant — so every declared copy either resolves or is a
constant declaration. -/
theorem declared_shape (ops : Operations Fp) (permCols : List ColRef)
    (starts : List ℕ) :
    ∀ copy ∈ operationDeclaredCopies ops,
      (∃ tuple, resolveDeclared permCols starts copy = some tuple) ∨
        ∃ c v, copy = (.cell c, .constant v) := by
  intro copy hmem
  induction ops with
  | nil => simp [operationDeclaredCopies] at hmem
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [operationDeclaredCopies] at hmem
          rcases List.mem_append.mp hmem with hcopy | hcopy
          · rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hcopy
            obtain ⟨rop, _, hop⟩ := hcopy
            cases rop with
            | constrainEqual a b =>
                obtain rfl := Option.some.inj hop
                exact Or.inl ⟨_, rfl⟩
            | constrainConstant cell value =>
                obtain rfl := Option.some.inj hop
                exact Or.inr ⟨cell, value, rfl⟩
            | constrainInstance cell col row =>
                obtain rfl := Option.some.inj hop
                exact Or.inl ⟨_, rfl⟩
            | assignAdvice col off val => simp [regionOperationDeclaredCopy?] at hop
            | assignFixed col off val => simp [regionOperationDeclaredCopy?] at hop
            | enableGate gate off => simp [regionOperationDeclaredCopy?] at hop
            | enableLookup arg enabled off => simp [regionOperationDeclaredCopy?] at hop
          · exact ih hcopy
      | constrainInstance cell col row =>
          rw [operationDeclaredCopies] at hmem
          rcases List.mem_cons.mp hmem with hcopy | hcopy
          · subst hcopy
            exact Or.inl ⟨_, rfl⟩
          · exact ih hcopy
      | loadTable tbl values =>
          rw [operationDeclaredCopies] at hmem
          exact ih hmem

/-- A constant occurring among the declared copy endpoints comes from a concrete
`constrainConstant` site in the operation stream. -/
theorem exists_constantSite_of_mem_declaredEndpoints
    (ops : Operations Fp) {value : Fp}
    (hendpoint : CopyEndpoint.constant value ∈
      (operationDeclaredCopies ops).flatMap fun copy => [copy.1, copy.2]) :
    ∃ cell, (cell, value) ∈ operationConstSites ops := by
  rw [List.mem_flatMap] at hendpoint
  obtain ⟨copy, hcopy, hendpoint⟩ := hendpoint
  rcases declared_shape ops [] [] copy hcopy with hres | hconstant
  · obtain ⟨tuple, htuple⟩ := hres
    rcases copy with ⟨left, right⟩
    cases left <;> cases right <;>
      simp [resolveDeclared] at htuple hendpoint
  · obtain ⟨cell, foundValue, rfl⟩ := hconstant
    simp only [List.mem_cons] at hendpoint
    rcases hendpoint with hendpoint | hendpoint
    · simp at hendpoint
    · rcases hendpoint with hendpoint | hnil
      · have hvalue : value = foundValue :=
          CopyEndpoint.constant.inj hendpoint
        subst value
        exact ⟨cell,
          mem_operationConstSites_of_declared_constant ops cell foundValue hcopy⟩
      · simp at hnil

end Halo2
