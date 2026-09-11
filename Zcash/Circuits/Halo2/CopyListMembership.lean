import Zcash.Circuits.Halo2.CopyCells
import Zcash.Circuits.Halo2.CopyOperations
import Zcash.Circuits.Halo2.CopyLayout
import Clean.Halo2.Keygen.Domain
import Mathlib.Data.List.Forall2
import Zcash.Common.ListZip

/-!
# Declared copies resolve into the keygen copy list

The compiler's ordinary copy stream is the resolved source-copy list; its constant
stream pairs source requests with positional allocations. These exact list
characterizations transfer source registration and row bounds to the compiled copy
list, and connect each declared copy to its compiled entry.
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
  rw [regionDeclaredCopies, List.mem_filterMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  have hRegistered := List.forall_iff_forall_mem.mp hcoherent op hOp
  cases op <;> simp only [regionOperationDeclaredCopy?, reduceCtorEq] at hCopy
  all_goals obtain rfl := Option.some.inj hCopy
  all_goals simpa [CopyEndpoint.PermutationColumnRegistered,
    RegionOperation.KeygenCoherent] using hRegistered

/-- Both endpoints of every coherent layouter copy use registered permutation
columns. -/
theorem operationDeclaredCopies_permutationColumns
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hcoherent : OperationsKeygenCoherent cs operations)
    (copy : DeclaredCopy Fp) (hcopy : copy ∈ operationDeclaredCopies operations) :
    copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs := by
  rw [operationDeclaredCopies, List.mem_flatMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  have hRegistered := List.forall_iff_forall_mem.mp hcoherent op hOp
  cases op with
  | region name body => exact regionDeclaredCopies_permutationColumns cs body hRegistered copy hCopy
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      exact hRegistered
  | loadTable table values => simp at hCopy

/-- Both endpoints of a region copy lie inside the complete operation footprint. -/
theorem regionDeclaredCopies_rows
    (root : Operations Fp) (name : String) (body : RegionOperations Fp)
    (hregion : Operation.region name body ∈ root)
    (copy : DeclaredCopy Fp) (hcopy : copy ∈ regionDeclaredCopies body) :
    copy.1.WithinRows (FloorPlanner.V1.starts root) (Halo2.usedRows root) ∧
      copy.2.WithinRows (FloorPlanner.V1.starts root) (Halo2.usedRows root) := by
  rw [regionDeclaredCopies, List.mem_filterMap] at hcopy
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
  rw [operationDeclaredCopies, List.mem_flatMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  cases op with
  | region name body => exact regionDeclaredCopies_rows operations name body hOp copy hCopy
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      exact rows_lt_usedRows_of_constrainInstance_mem operations cell column row hOp
  | loadTable table values => simp at hCopy

/-- Copy compilation resolves precisely the non-constant source copies. -/
theorem regionCopiesSplit_fst_eq (columns : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (constants : List (ℕ × ℕ × ℕ)) :
    (regionCopiesSplit columns starts body constants).1 =
      (regionDeclaredCopies body).filterMap (resolveDeclared columns starts) := by
  simp only [regionCopiesSplit, regionDeclaredCopies, List.filterMap_filterMap]
  congr 1
  funext op
  cases op <;> rfl

/-- The complete equality stream is a pointwise resolution of the source copies;
the positional constants walk does not affect it. -/
theorem V1_go_fst_eq (columns : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (constants : List (ℕ × ℕ × ℕ)) :
    (V1.go columns starts ops constants).1.1 =
      (operationDeclaredCopies ops).filterMap (resolveDeclared columns starts) := by
  induction ops generalizing constants with
  | nil => simp [V1.go, operationDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp [V1.go, operationDeclaredCopies, List.filterMap_append,
        regionCopiesSplit_fst_eq, resolveDeclared, ih]

/-- Resolving registered endpoints produces in-range permutation columns. -/
theorem resolveDeclared_columns_lt (cs : ConstraintSystem Fp) (starts : List ℕ)
    (copy : DeclaredCopy Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared (permColsOf cs) starts copy = some tuple)
    (hColumns : copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs) :
    tuple.1 < (permColsOf cs).length ∧ tuple.2.2.1 < (permColsOf cs).length := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  all_goals constructor <;> apply permIndex_lt_length_of_mem <;> rw [permColsOf_map_toAny]
  all_goals first | exact hColumns.1 | exact hColumns.2

/-- Address resolution preserves the row bounds of source endpoints. -/
theorem resolveDeclared_rows_lt (columns : List ColRef) (starts : List ℕ)
    (bound : ℕ) (copy : DeclaredCopy Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared columns starts copy = some tuple)
    (hRows : copy.1.WithinRows starts bound ∧ copy.2.WithinRows starts bound) :
    tuple.2.1 < bound ∧ tuple.2.2.2 < bound := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  all_goals simpa only [CopyEndpoint.WithinRows, resolveCell, place] using hRows

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
  rw [V1.copyList, List.mem_append]
  exact Or.inl (by
    rw [V1_go_fst_eq, List.mem_filterMap]
    exact ⟨copy, hmem, hres⟩)

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

/-- The constants half of a region's copy extraction, in closed zipped form: each
constant site pairs with the next allocation-map entry — the constants cell on the
left, the site's resolved cell on the right — and the tail of the map is returned. -/
theorem regionCopiesSplit_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ)) :
    (regionCopiesSplit permCols starts body consts).2.1 =
      ((constSites body).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (regionCopiesSplit permCols starts body consts).2.2 =
        consts.drop (constSites body).length := by
  induction body generalizing consts with
  | nil => simp [regionCopiesSplit, regionCopiesSplit.go, constSites]
  | cons op rest ih =>
      cases op with
      | constrainConstant cell value =>
          cases consts with
          | nil =>
              simpa [regionCopiesSplit, regionCopiesSplit.go, constSites] using ih []
          | cons entry cs =>
              simpa [regionCopiesSplit, regionCopiesSplit.go, constSites] using ih cs
      | constrainEqual | constrainInstance | assignAdvice | assignFixed | enableGate | enableLookup =>
          exact ih consts

/-- The constant-declaration sites of a whole operation stream: region sites in region
order (V1 defers them all to the end of synthesis, in this order). -/
def operationConstSites : Operations Fp → List (Cell × Fp)
  | [] => []
  | .region _ body :: rest => constSites body ++ operationConstSites rest
  | .constrainInstance _ _ _ :: rest => operationConstSites rest
  | .loadTable _ _ :: rest => operationConstSites rest

/-- A region's constant sites are exactly its declared constant copies. -/
theorem mem_constSites_iff_declaredCopy (body : RegionOperations Fp) (cell : Cell) (value : Fp) :
    (cell, value) ∈ constSites body ↔
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈ regionDeclaredCopies body := by
  induction body with
  | nil => simp [constSites, regionDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp_all [constSites, regionDeclaredCopies, regionOperationDeclaredCopy?]

/-- The positional constant-site stream retains precisely the source constant copies. -/
theorem mem_operationConstSites_iff_declaredCopy (ops : Operations Fp) (cell : Cell) (value : Fp) :
    (cell, value) ∈ operationConstSites ops ↔
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈ operationDeclaredCopies ops := by
  induction ops with
  | nil => simp [operationConstSites, operationDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp_all [operationConstSites, operationDeclaredCopies,
        mem_constSites_iff_declaredCopy]

/-- Every constant site in a keygen-lawful operation stream lies on an
equality-enabled column. -/
theorem operationConstSite_column_mem_permutationColumns
    (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hregistered : OperationsKeygenCoherent cs operations)
    {cell : Cell} {value : Fp}
    (hsite : (cell, value) ∈ operationConstSites operations) :
    cell.column ∈ cs.permutationColumns := by
  exact (operationDeclaredCopies_permutationColumns cs operations hregistered _
    ((mem_operationConstSites_iff_declaredCopy operations cell value).mp hsite)).1

/-- A whole-stream constant site lies below the compiler-derived operation
footprint. -/
theorem constantSite_row_lt_usedRows
    (operations : Operations Fp) (cell : Cell) (value : Fp)
    (hsite : (cell, value) ∈ operationConstSites operations) :
    (FloorPlanner.V1.starts operations).getD cell.regionIndex 0 +
        cell.rowOffset <
      Halo2.usedRows operations := by
  exact (operationDeclaredCopies_rows operations _
    ((mem_operationConstSites_iff_declaredCopy operations cell value).mp hsite)).1

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
  have hFull := hfit
  rw [operationConstSites_length] at hFull
  have hValues := congrArg (List.map ZMod.val)
    (FloorPlanner.V1.constantAssignments_map_fst ops constantColumns hFull)
  have hPairs : List.Forall₂ (fun site entry => site.2.val = entry.1)
      (operationConstSites ops)
      ((FloorPlanner.V1.constantAssignments ops constantColumns).map
        fun (value, column, row) => (value.val, column, row)) := by
    rw [← List.forall₂_map_left_iff
        (R := fun value (entry : ℕ × ℕ × ℕ) => value = entry.1)
        (f := fun site : Cell × Fp => site.2.val),
      ← List.forall₂_map_right_iff (R := Eq) (f := Prod.fst), List.forall₂_eq_eq_eq]
    simpa only [List.map_map, Function.comp_def, ← operationConstSites_map_snd] using
      hValues.symm
  exact (List.forall₂_zip hPairs hallocation).symm

/-- The V1 constants stream in closed zipped form: every constant site across the
stream pairs with its allocation-map entry, in region-then-body order. -/
theorem V1_go_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ)) :
    (V1.go permCols starts ops consts).1.2 =
      ((operationConstSites ops).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (V1.go permCols starts ops consts).2 =
        consts.drop (operationConstSites ops).length := by
  induction ops generalizing consts with
  | nil => simp [V1.go, operationConstSites]
  | cons op rest ih =>
      cases op with
      | region name body =>
          obtain ⟨hCopies, hRemaining⟩ := regionCopiesSplit_snd_eq permCols starts body consts
          obtain ⟨hTail, hFinal⟩ := ih (consts.drop (constSites body).length)
          simp only [V1.go, hRemaining, hCopies, hTail, hFinal, operationConstSites,
            List.zip_append_drop, List.map_append, List.length_append, List.drop_drop, and_self]
      | constrainInstance cell col row =>
          simpa only [V1.go, operationConstSites] using ih consts
      | loadTable table values =>
          simpa only [V1.go, operationConstSites] using ih consts

/-- Every tuple in the V1 copy list lies below the compiler-derived operation
footprint. Constant allocations need only be present positionally and carry their
generic planner row bound; no concrete circuit computation is involved. -/
theorem V1_copyList_rows_lt_usedRows
    (operations : Operations Fp) (permCols : List ColRef)
    (constants : List (ℕ × ℕ × ℕ))
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
  · rw [V1_go_fst_eq, List.mem_filterMap] at hequality
    obtain ⟨copy, hCopy, hResolve⟩ := hequality
    exact resolveDeclared_rows_lt _ _ _ copy tuple hResolve
      (operationDeclaredCopies_rows operations copy hCopy)
  · have hconstants :=
      (V1_go_snd_eq permCols (FloorPlanner.V1.starts operations)
        operations constants).1
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
    (hconstantColumns : ∀ entry ∈ constants,
      (AnyColumn.mk .fixed entry.2.1) ∈ cs.permutationColumns)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ V1.copyList
      (Halo2.Layout.permColsOf cs) starts operations constants) :
    tuple.1 < (Halo2.Layout.permColsOf cs).length ∧
      tuple.2.2.1 < (Halo2.Layout.permColsOf cs).length := by
  rw [V1.copyList, List.mem_append] at htuple
  rcases htuple with hequality | hconstant
  · rw [V1_go_fst_eq, List.mem_filterMap] at hequality
    obtain ⟨copy, hCopy, hResolve⟩ := hequality
    exact resolveDeclared_columns_lt cs starts copy tuple hResolve
      (operationDeclaredCopies_permutationColumns cs operations hregistered copy hCopy)
  · have hconstants :=
      (V1_go_snd_eq (Halo2.Layout.permColsOf cs) starts
        operations constants).1
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
  intro copy hCopy
  rw [operationDeclaredCopies, List.mem_flatMap] at hCopy
  obtain ⟨op, _, hCopy⟩ := hCopy
  cases op with
  | region name body =>
      simp only [regionDeclaredCopies, List.mem_filterMap] at hCopy
      obtain ⟨op, _, hCopy⟩ := hCopy
      cases op <;> simp only [regionOperationDeclaredCopy?, reduceCtorEq] at hCopy
      all_goals obtain rfl := Option.some.inj hCopy
      all_goals simp [resolveDeclared]
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      simp [resolveDeclared]
  | loadTable table values => simp at hCopy

end Halo2
