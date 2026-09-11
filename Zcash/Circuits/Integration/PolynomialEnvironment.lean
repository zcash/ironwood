import Zcash.Snark.Soundness.Canonical.PolynomialEnvironment
import Zcash.Circuits.Halo2.ConstraintFamilies
import Clean.Halo2.TopLevel
import Zcash.Circuits.Halo2.QueryLayout
import Clean.Halo2.Keygen.Semantics
import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation

/-!
# Canonical polynomial-to-row Clean environments

Decoded member columns are polynomials.  Clean circuit semantics reads columns by integer row.
This file supplies the canonical adapter: row `r` of a column polynomial is its evaluation at
`ω^r`.  Integer rows make rotations definitionally uniform, including negative rotations.
The underlying row polynomials and their algebra are verifier-native and live in
`Zcash.Snark.Soundness.Canonical.PolynomialEnvironment`.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

/-- Reduce an integer domain-row exponent to its canonical natural representative. -/
theorem zpow_eq_pow_natMod
    (omega : Fp) (n : ℕ) (hn : 0 < n)
    (hroot : omega ^ n = 1) (row : ℤ) :
    omega ^ row = omega ^ row.natMod n := by
  have homega : omega ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn.ne'] at hroot
    exact zero_ne_one hroot
  calc
    omega ^ row =
        omega ^ (row % (n : ℤ) + (n : ℤ) * (row / (n : ℤ))) := by
      rw [Int.emod_add_mul_ediv]
    _ = omega ^ (row % (n : ℤ)) := by
      rw [zpow_add₀ homega, zpow_mul, show omega ^ (n : ℤ) = 1 by
        simpa using hroot, one_zpow, _root_.mul_one]
    _ = omega ^ row.natMod n := by
      rw [← zpow_natCast]
      congr 1
      simp only [Int.natMod]
      exact (Int.toNat_of_nonneg
        (Int.emod_nonneg row
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)))).symm

/-- Read fixed, advice, and instance column polynomials on the multiplicative `ω` row domain. -/
def polynomialEnvironment
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    Environment Fp where
  get column row :=
    match column.kind with
    | .fixed => (fixedCols column.index).eval (omega ^ row)
    | .advice => (adviceCols column.index).eval (omega ^ row)
    | .instance => (instanceCols column.index).eval (omega ^ row)
  usableRows := usableRows

/--
Read the proof-varying columns of a Clean top-level environment from polynomials.

Fixed columns and usable rows intentionally do not appear here: the
`TopLevelCircuit` compiler supplies them when constructing its environment.
-/
def polynomialAssignment
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) : ProofAssignment Fp where
  advice := fun column row =>
    (poly (.adviceCol proofIndex column.index)).eval (omega ^ row)
  inst := fun column row =>
    (poly (.instanceCol proofIndex column.index)).eval (omega ^ row)

@[simp] theorem polynomialAssignment_advice
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) (column : Column .advice) (row : ℤ) :
    (polynomialAssignment omega poly proofIndex).advice column row =
      (poly (.adviceCol proofIndex column.index)).eval (omega ^ row) :=
  rfl

@[simp] theorem polynomialAssignment_instance
    (omega : Fp) (poly : CommitmentId → CPoly)
    (proofIndex : ℕ) (column : Column .instance) (row : ℤ) :
    (polynomialAssignment omega poly proofIndex).inst column row =
      (poly (.instanceCol proofIndex column.index)).eval (omega ^ row) :=
  rfl

@[simp] theorem polynomialEnvironment_usableRows
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).usableRows =
      usableRows := rfl

@[simp] theorem polynomialEnvironment_fixed
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .fixed) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).fixed column row =
      (fixedCols column.index).eval (omega ^ row) := rfl

@[simp] theorem polynomialEnvironment_advice
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .advice) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).advice column row =
      (adviceCols column.index).eval (omega ^ row) := rfl

@[simp] theorem polynomialEnvironment_instance
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .instance) (row : ℤ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).inst column row =
      (instanceCols column.index).eval (omega ^ row) := rfl

/-- Natural row reads agree with the usual evaluation-domain spelling `ω ^ row`. -/
theorem polynomialEnvironment_fixed_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .fixed) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).fixed
        column (row : ℤ) =
      (fixedCols column.index).eval (omega ^ row) := by simp

theorem polynomialEnvironment_advice_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .advice) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).advice
        column (row : ℤ) =
      (adviceCols column.index).eval (omega ^ row) := by simp

theorem polynomialEnvironment_instance_nat
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (column : Column .instance) (row : ℕ) :
    (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols).inst
        column (row : ℤ) =
      (instanceCols column.index).eval (omega ^ row) := by simp

/-- A rotated advice query is evaluation of the standard rotated column polynomial at the base
row point. -/
theorem polynomialEnvironment_query_advice
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .advice) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.advice column rotation) =
      ((adviceCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_advice, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- The fixed-column rotation adapter. -/
theorem polynomialEnvironment_query_fixed
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .fixed) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.fixed column rotation) =
      ((fixedCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_fixed, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- The instance-column rotation adapter. -/
theorem polynomialEnvironment_query_instance
    (omega : Fp) (usableRows : ℕ)
    (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (homega : omega ≠ 0)
    (selectors : ℕ → Fp) (column : Column .instance) (row rotation : ℤ) :
    Query.eval (polynomialEnvironment omega usableRows fixedCols adviceCols instanceCols)
        selectors row (.instance column rotation) =
      ((instanceCols column.index).comp (C (omega ^ rotation) * X)).eval (omega ^ row) := by
  rw [Query.eval, polynomialEnvironment_instance, eval_comp_rotate]
  congr 1
  rw [zpow_add₀ homega, _root_.mul_comm]

/-- Read the column polynomials indexed by commitment ID for one sub-proof. -/
def polynomialEnvironmentOfCommitments
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ) :
    Environment Fp :=
  polynomialEnvironment vk.omega usableRows
    (fun column => poly (.fixedCol column))
    (fun column => poly (.adviceCol p column))
    (fun column => poly (.instanceCol p column))

@[simp] theorem polynomialEnvironmentOfCommitments_fixed
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .fixed) (row : ℤ) :
    (polynomialEnvironmentOfCommitments vk poly p usableRows).fixed column row =
      (poly (.fixedCol column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem polynomialEnvironmentOfCommitments_advice
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .advice) (row : ℤ) :
    (polynomialEnvironmentOfCommitments vk poly p usableRows).advice column row =
      (poly (.adviceCol p column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem polynomialEnvironmentOfCommitments_instance
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .instance) (row : ℤ) :
    (polynomialEnvironmentOfCommitments vk poly p usableRows).inst column row =
      (poly (.instanceCol p column.index)).eval (vk.omega ^ row) := rfl

/--
Once commitment binding identifies a resolved instance column with its canonical
zero-padded row polynomial, the Clean environment reads the supplied public values.
-/
theorem polynomialEnvironmentOfCommitments_instance_of_rowPolynomial
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (usableRows : ℕ)
    (column : Column .instance) (values : List Fp)
    (hpoly : poly (.instanceCol p column.index) =
      instanceRowPolynomial (2 ^ shape.k) vk.omega values)
    (hrows : Function.Injective
      fun i : Fin (2 ^ shape.k) => vk.omega ^ (i : ℕ))
    (row : Fin (2 ^ shape.k)) :
    (polynomialEnvironmentOfCommitments vk poly p usableRows).inst column (row : ℤ) =
      values.getD (row : ℕ) 0 := by
  rw [polynomialEnvironmentOfCommitments_instance, hpoly]
  simpa using instanceRowPolynomial_eval hrows row

/-!
## Polynomial query feeds

Verifier expressions index query-layout entries.  Clean expressions name the same
queries as `(column, rotation)` pairs. This module proves that the
rotated polynomial feeds and the canonical row environment interpret those two
representations identically on every evaluation-domain row.
-/

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
      (polynomialEnvironmentOfCommitments vk poly proofIndex usableRows).get
        (permutationColumnAddress vk reference) (row : ℤ) := by
  cases reference with
  | advice query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        polynomialEnvironmentOfCommitments, polynomialEnvironment, hcount]
  | fixed query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        polynomialEnvironmentOfCommitments, polynomialEnvironment, hcount]
  | «instance» query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        polynomialEnvironmentOfCommitments, polynomialEnvironment, hcount]

/--
One polynomial permutation chunk value is the canonical environment read at the
concrete column decoded from that chunk's query reference.
-/
theorem chunkRowValue_eq_polynomialEnvironment
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
      (polynomialEnvironmentOfCommitments vk poly proofIndex usableRows).get
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

/-- Rotating a domain point is addition of its row and query rotation. -/
theorem rotateOmega_domainPoint
    (omega : Fp) (homega : omega ≠ 0) (row : ℕ) (rotation : ℤ) :
    rotateOmega omega (omega ^ row) rotation =
      omega ^ ((row : ℤ) + rotation) := by
  rw [zpow_add₀ homega]
  simp [rotateOmega, _root_.mul_comm]

/-- A fixed query feed reads the same row as the polynomial environment. -/
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
      Query.eval (polynomialEnvironmentOfCommitments vk poly p usableRows)
        selectors row (.fixed ⟨column⟩ rotation) := by
  rw [fixedQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.fixedQueryLayout (fun column => poly (.fixedCol column)) hquery]
  simp only [List.getD_eq_getElem?_getD, hentry, Option.getD_some,
    Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_fixed,
    rotateOmega_domainPoint vk.omega homega]

/-- An advice query feed reads the same row as the polynomial environment. -/
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
      Query.eval (polynomialEnvironmentOfCommitments vk poly p usableRows)
        selectors row (.advice ⟨column⟩ rotation) := by
  rw [adviceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.adviceQueryLayout (fun column => poly (.adviceCol p column)) hquery]
  simp only [List.getD_eq_getElem?_getD, hentry, Option.getD_some,
    Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_advice,
    rotateOmega_domainPoint vk.omega homega]

/-- An instance query feed reads the same row as the polynomial environment. -/
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
      Query.eval (polynomialEnvironmentOfCommitments vk poly p usableRows)
        selectors row (.instance ⟨column⟩ rotation) := by
  rw [instanceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.instanceQueryLayout (fun column => poly (.instanceCol p column)) hquery]
  simp only [List.getD_eq_getElem?_getD, hentry, Option.getD_some,
    Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_instance,
    rotateOmega_domainPoint vk.omega homega]

/--
The three polynomial query feeds interpret an arbitrary keygen query state whenever
the state layouts are the VK layouts and the shape counts those layouts exactly.
-/
theorem polynomialQueryFeeds_interpret
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
      (Query.eval (polynomialEnvironmentOfCommitments vk poly p usableRows)
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
