import Clean.Halo2.Keygen.Semantics
import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation
import Zcash.Circuits.Integration.PolynomialEnvironment

/-!
# Resolver query feeds and Clean environments

Verifier expressions index query-layout entries.  Clean expressions name the same
queries as `(column, rotation)` pairs.  This module proves that the resolver-backed
rotated polynomial feeds and the canonical row environment interpret those two
representations identically on every evaluation-domain row.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

/-- Decode a verifier permutation query reference back to the concrete Clean
column selected by its query-layout entry. -/
def permutationColumnAddress
    {shape : CircuitShape} {F G : Type*}
    (vk : VerifyingKey shape F G) : ColumnRef → AnyColumn
  | .advice query =>
      ⟨.advice, (vk.adviceQueryLayout.getD query (0, 0)).1⟩
  | .fixed query =>
      ⟨.fixed, (vk.fixedQueryLayout.getD query (0, 0)).1⟩
  | .instance query =>
      ⟨.instance, (vk.instanceQueryLayout.getD query (0, 0)).1⟩

/--
The value polynomial selected by a coherent permutation query reference reads
the same natural-numbered row as its decoded Clean column.
-/
theorem permutationColumnPolynomial_eval_environment
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin numProofs)
    (usableRows row : ℕ) (reference : ColumnRef)
    (hcoherent : PermutationColumnRef.Coherent vk reference) :
    (permutationColumnPolynomialOfResolver
        vk poly proofIndex reference).eval (vk.omega ^ row) =
      (resolverEnvironment vk poly proofIndex usableRows).get
        (permutationColumnAddress vk reference) (row : ℤ) := by
  cases reference with
  | advice query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]
  | fixed query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]
  | «instance» query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]

/--
One resolver permutation chunk value is the canonical environment read at the
concrete column decoded from that chunk's query reference.
-/
theorem chunkRowValue_eq_resolverEnvironment
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin numProofs)
    (usableRows chunk row column : ℕ)
    (hcolumn :
      column < (vk.permutationChunks.getD chunk []).length)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        ((vk.permutationChunks.getD chunk []).getD
          column ((.advice 0), 0)).1) :
    chunkRowValue vk.omega
        (permutationChunkPairsOfResolver vk poly proofIndex)
        chunk row column =
      (resolverEnvironment vk poly proofIndex usableRows).get
        (permutationColumnAddress vk
          ((vk.permutationChunks.getD chunk []).getD
            column ((.advice 0), 0)).1)
        (row : ℤ) := by
  rw [chunkRowValue, rowValue]
  have hpairs :
      column <
        (permutationChunkPairsOfResolver
          vk poly proofIndex chunk).length := by
    simpa [permutationChunkPairsOfResolver] using hcolumn
  rw [List.getD_eq_getElem _ _ hpairs]
  simp only [permutationChunkPairsOfResolver, List.getElem_map]
  rw [List.getD_eq_getElem _ _ hcolumn] at hcoherent ⊢
  exact permutationColumnPolynomial_eval_environment
    vk poly proofIndex usableRows row
      ((vk.permutationChunks.getD chunk [])[column]).1 hcoherent

/-- Repackage a pinned constraint system's three query layouts as a query state. -/
def pinnedQueryState
    {F : Type} (pinned : PinnedConstraintSystem F) : QueryState where
  advice := pinned.adviceQueryLayout.toArray
  fixed := pinned.fixedQueryLayout.toArray
  inst := pinned.instanceQueryLayout.toArray

/--
The pinned query layouts are exactly the authoritative query state used by the
read-only expression projection.
-/
theorem PinnedConstraintSystem.derive_queryState_eq
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap) :
    pinnedQueryState (PinnedConstraintSystem.derive cs map) =
      queryWalkInit map cs := by
  apply QueryState.ext
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, PinnedConstraintSystem.derive, projectCS]
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, PinnedConstraintSystem.derive, projectCS]
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, PinnedConstraintSystem.derive, projectCS]

/-- Every configure-registered fixed query remains present in the derived pinned
fixed-query layout. -/
theorem PinnedConstraintSystem.mem_fixedQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .fixed) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.fixedQueries) :
    (column.index, rotation) ∈
      (PinnedConstraintSystem.derive cs map).fixedQueryLayout := by
  have hresolved := queryWalkInit_resolves_fixed_of_mem map hquery
  have hstate := PinnedConstraintSystem.derive_queryState_eq cs map
  rw [← hstate] at hresolved
  simpa [QueryState.ResolvesQuery, pinnedQueryState] using hresolved

/-- Every configure-registered instance query remains present in the derived pinned
instance-query layout. -/
theorem PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .instance) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.instanceQueries) :
    (column.index, rotation) ∈
      (PinnedConstraintSystem.derive cs map).instanceQueryLayout := by
  have hregistered :
      (column.index, rotation) ∈
        cs.instanceQueries.map fun query => (query.1.index, query.2) :=
    List.mem_map.mpr ⟨(column, rotation), hquery, by simp⟩
  rw [← queryWalkInit_instance cs map] at hregistered
  have hstate := PinnedConstraintSystem.derive_queryState_eq cs map
  rw [← hstate] at hregistered
  simpa [pinnedQueryState] using hregistered

/-- The circuit-owned pinned layouts are its authoritative query state. -/
theorem _root_.Halo2.TopLevelCircuit.pinnedQueryState_eq_gateQueryState
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top] :
    pinnedQueryState top.pinnedCS = top.gateQueryState := by
  simpa only [TopLevelCircuit.pinnedCS, TopLevelCircuit.gateQueryState] using
    PinnedConstraintSystem.derive_queryState_eq
      top.constraintSystem top.selectorMap

/-- Every top-level configured instance query remains in its circuit-owned layout. -/
theorem _root_.Halo2.TopLevelCircuit.mem_instanceQueryLayout_of_mem_constraintSystem
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top]
    (column : Column .instance) (rotation : Rotation)
    (hquery : (column, rotation) ∈ top.constraintSystem.instanceQueries) :
    (column.index, rotation) ∈ top.instanceQueryLayout := by
  exact PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
    top.constraintSystem top.selectorMap column rotation hquery

/-- Rotating a domain point is addition of its row and query rotation. -/
theorem rotateOmega_domainPoint
    (omega : Fp) (homega : omega ≠ 0) (row : ℕ) (rotation : ℤ) :
    rotateOmega omega (omega ^ row) rotation =
      omega ^ ((row : ℤ) + rotation) := by
  rw [zpow_add₀ homega]
  simp [rotateOmega, _root_.mul_comm]

/-- A fixed query feed reads the same row as the canonical resolver environment. -/
theorem fixedQueryFeedOfResolver_eval_environment
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numFixedQueries)
    (hentry : vk.fixedQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (fixedQueryFeedOfResolver vk poly query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.fixed ⟨column⟩ rotation) := by
  rw [fixedQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.fixedQueryLayout
      (fun column => poly (.fixedCol column)) hquery]
  have hget :
      vk.fixedQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_fixed]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/-- An advice query feed reads the same row as the canonical resolver environment. -/
theorem adviceQueryFeedOfResolver_eval_environment
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numAdviceQueries)
    (hentry : vk.adviceQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (adviceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.advice ⟨column⟩ rotation) := by
  rw [adviceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.adviceQueryLayout
      (fun column => poly (.adviceCol p column)) hquery]
  have hget :
      vk.adviceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_advice]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/-- An instance query feed reads the same row as the canonical resolver environment. -/
theorem instanceQueryFeedOfResolver_eval_environment
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numInstanceQueries)
    (hentry : vk.instanceQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (instanceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.instance ⟨column⟩ rotation) := by
  rw [instanceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.instanceQueryLayout
      (fun column => poly (.instanceCol p column)) hquery]
  have hget :
      vk.instanceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_instance]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/--
The three resolver query feeds interpret an arbitrary keygen query state whenever
the state layouts are the VK layouts and the shape counts those layouts exactly.
-/
theorem resolverQueryFeeds_interpret
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp) (row : ℕ)
    (homega : vk.omega ≠ 0)
    (state : QueryState)
    (hadviceLayout :
      state.advice.toList = vk.adviceQueryLayout)
    (hfixedLayout :
      state.fixed.toList = vk.fixedQueryLayout)
    (hinstanceLayout :
      state.inst.toList = vk.instanceQueryLayout)
    (hadviceCount :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hfixedCount :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hinstanceCount :
      vk.instanceQueryLayout.length = shape.numInstanceQueries) :
    Interprets state
      (fun query =>
        (fixedQueryFeedOfResolver vk poly query).eval (vk.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row))
      (Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row) where
  advice query column rotation hentry := by
    have hentryList :
        state.advice.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hadviceLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply adviceQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega
  fixed query column rotation hentry := by
    have hentryList :
        state.fixed.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hfixedLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply fixedQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega
  inst query column rotation hentry := by
    have hentryList :
        state.inst.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hinstanceLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply instanceQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega

end Zcash.Snark
