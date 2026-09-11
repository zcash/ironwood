import Zcash.Circuits.Halo2.QueryLayout
import Clean.Halo2.Keygen.Semantics
import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation
import Zcash.Circuits.Integration.PolynomialEnvironment

/-!
# Polynomial query feeds and Clean environments

Verifier expressions index query-layout entries.  Clean expressions name the same
queries as `(column, rotation)` pairs. This module proves that the
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
    resolverQueryFeed_eval vk.omega vk.fixedQueryLayout
      (fun column => poly (.fixedCol column)) hquery]
  have hget :
      vk.fixedQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_fixed]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

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
    resolverQueryFeed_eval vk.omega vk.adviceQueryLayout
      (fun column => poly (.adviceCol p column)) hquery]
  have hget :
      vk.adviceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_advice]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

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
    resolverQueryFeed_eval vk.omega vk.instanceQueryLayout
      (fun column => poly (.instanceCol p column)) hquery]
  have hget :
      vk.instanceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, polynomialEnvironmentOfCommitments, polynomialEnvironment_instance]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

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
