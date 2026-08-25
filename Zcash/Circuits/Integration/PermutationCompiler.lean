import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.ListChunks
import Zcash.Snark.Keygen.Pipeline

/-!
# Permutation compiler round trips

The keygen compiler turns equality-enabled Clean columns into verifier query
references, attaches their global σ-column indices, and splits the result into
permutation chunks. This module proves that the transformation loses no column
information: flattening the chunks and decoding coherent query references
recovers the original permutation-column order.

The result follows from the compiler pipeline itself. It does not inspect a
concrete circuit or use a full-circuit computation certificate.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- An in-range `findIdx` decodes to the element it searched for. -/
theorem getD_findIdx_eq_target
    {α : Type} [DecidableEq α]
    (xs : List α) (target fallback : α)
    (hin : xs.findIdx (· = target) < xs.length) :
    xs.getD (xs.findIdx (· = target)) fallback = target := by
  rw [List.getD_eq_getElem _ _ hin]
  have hfound :=
    List.findIdx_getElem
      (xs := xs) (p := fun value => value = target) (w := hin)
  simpa using hfound

/-- Reading one inner list is the same as reading the flattened list after the
complete prefix of earlier inner lists. -/
theorem flatten_getD_at_chunk
    {α : Type*} (fallback : α) (chunks : List (List α))
    (chunk column : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length) :
    chunks.flatten.getD
        ((chunks.take chunk).flatten.length + column) fallback =
      (chunks.getD chunk []).getD column fallback := by
  induction chunks generalizing chunk with
  | nil =>
      simp at hchunk
  | cons head tail ih =>
      cases chunk with
      | zero =>
          simp only [List.take_zero, List.flatten_nil, List.length_nil,
            Nat.zero_add, List.getD_cons_zero, List.flatten_cons]
          exact List.getD_append head tail.flatten fallback column hcolumn
      | succ chunk =>
          have hchunkTail : chunk < tail.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hchunk
          have hcolumnTail :
              column < (tail.getD chunk []).length := by
            simpa only [List.getD_cons_succ] using hcolumn
          simp only [List.take_succ_cons, List.flatten_cons,
            List.length_append, List.getD_cons_succ]
          rw [List.getD_append_right]
          · have hindex :
                head.length +
                    (tail.take chunk).flatten.length + column -
                    head.length =
                  (tail.take chunk).flatten.length + column := by
                omega
            rw [hindex]
            exact ih chunk hchunkTail hcolumnTail
          · omega

/--
If decoding flattened compiler chunks yields the source-column list, a local
`(chunk,column)` reference decodes to the source column at its flattened index.
-/
theorem decodedChunkAddress_eq_sourceColumn
    {Reference Address : Type*}
    (decode : Reference → Address)
    (referenceFallback : Reference) (addressFallback : Address)
    (chunks : List (List Reference)) (columns : List Address)
    (hdecoded : chunks.flatten.map decode = columns)
    (chunk column global : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length)
    (hglobal : global < columns.length)
    (hindex :
      (chunks.take chunk).flatten.length + column = global) :
    decode ((chunks.getD chunk []).getD column referenceFallback) =
      columns.getD global addressFallback := by
  have hflatGlobal : global < chunks.flatten.length := by
    have hlength := congrArg List.length hdecoded
    have : chunks.flatten.length = columns.length := by
      simpa only [List.length_map] using hlength
    omega
  have hmapGlobal : global < (chunks.flatten.map decode).length := by
    simpa only [List.length_map] using hflatGlobal
  have hlocal :=
    flatten_getD_at_chunk referenceFallback chunks chunk column hchunk hcolumn
  calc
    decode ((chunks.getD chunk []).getD column referenceFallback) =
        decode (chunks.flatten.getD global referenceFallback) := by
          rw [hindex] at hlocal
          exact congrArg decode hlocal.symm
    _ = (chunks.flatten.map decode).getD global addressFallback := by
          rw [List.getD_eq_getElem _ _ hflatGlobal,
            List.getD_eq_getElem _ _ hmapGlobal]
          simp only [List.getElem_map]
    _ = columns.getD global addressFallback := by rw [hdecoded]

/-- The verifier query reference assigned by the permutation compiler to one
concrete column. -/
def permutationQueryReference
    (adviceQueryLayout fixedQueryLayout instanceQueryLayout :
      List (ℕ × ℤ)) :
    AnyColumn → ColumnRef
  | ⟨.advice, index⟩ =>
      .advice (adviceQueryLayout.findIdx (· = (index, 0)))
  | ⟨.fixed, index⟩ =>
      .fixed (fixedQueryLayout.findIdx (· = (index, 0)))
  | ⟨.instance, index⟩ =>
      .instance (instanceQueryLayout.findIdx (· = (index, 0)))

/-- The verifier CS's variable-width chunking preserves its indexed reference
stream exactly. -/
theorem verifierCS_permutationChunks_flatten
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.verifierCS.permutationChunks.flatten =
      (top.permutationColumns.map
        (permutationQueryReference top.adviceQueryLayout
          top.fixedQueryLayout top.instanceQueryLayout)).zipIdx := by
  unfold TopLevelCircuit.verifierCS
  rw [listToChunks_flatten]
  congr 2
  funext column
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

/-- The query reference compiled from an equality-enabled column is in range and
selects that column at rotation zero. -/
theorem permutationQueryReference_coherent
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) {column : AnyColumn}
    (hcolumn : column ∈ top.permutationColumns) :
    PermutationColumnRef.Coherent (top.toVerifierKey urs)
      (permutationQueryReference top.adviceQueryLayout
        top.fixedQueryLayout top.instanceQueryLayout column) := by
  have hquery := top.permutationColumn_mem_queryLayout hcolumn
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      have hin :
          top.adviceQueryLayout.findIdx (· = (index, 0)) <
            top.adviceQueryLayout.length :=
        List.findIdx_lt_length_of_exists ⟨(index, 0), hquery, by simp⟩
      simp only [permutationQueryReference,
        PermutationColumnRef.Coherent]
      refine ⟨?_, ?_, ?_⟩
      · have hcount :
            top.adviceQueryLayout.findIdx (· = (index, 0)) <
              top.adviceQueryCount := by
          rw [top.adviceQueryCount_eq_adviceQueryLayout_length]
          exact hin
        exact hcount
      · simpa only [top.toVerifierKey_adviceQueryLayout] using hin
      · rw [top.toVerifierKey_adviceQueryLayout,
          getD_findIdx_eq_target top.adviceQueryLayout
            (index, 0) (0, 0) hin]
  | fixed =>
      have hin :
          top.fixedQueryLayout.findIdx (· = (index, 0)) <
            top.fixedQueryLayout.length :=
        List.findIdx_lt_length_of_exists ⟨(index, 0), hquery, by simp⟩
      simp only [permutationQueryReference,
        PermutationColumnRef.Coherent]
      refine ⟨?_, ?_, ?_⟩
      · have hcount :
            top.fixedQueryLayout.findIdx (· = (index, 0)) <
              top.fixedQueryCount := by
          rw [top.fixedQueryCount_eq_fixedQueryLayout_length]
          exact hin
        exact hcount
      · simpa only [top.toVerifierKey_fixedQueryLayout] using hin
      · rw [top.toVerifierKey_fixedQueryLayout,
          getD_findIdx_eq_target top.fixedQueryLayout
            (index, 0) (0, 0) hin]
  | «instance» =>
      have hin :
          top.instanceQueryLayout.findIdx (· = (index, 0)) <
            top.instanceQueryLayout.length :=
        List.findIdx_lt_length_of_exists ⟨(index, 0), hquery, by simp⟩
      simp only [permutationQueryReference,
        PermutationColumnRef.Coherent]
      refine ⟨?_, ?_, ?_⟩
      · have hcount :
            top.instanceQueryLayout.findIdx (· = (index, 0)) <
              top.instanceQueryCount := by
          rw [top.instanceQueryCount_eq_instanceQueryLayout_length]
          exact hin
        exact hcount
      · simpa only [top.toVerifierKey_instanceQueryLayout] using hin
      · rw [top.toVerifierKey_instanceQueryLayout,
          getD_findIdx_eq_target top.instanceQueryLayout
            (index, 0) (0, 0) hin]

/-- Every permutation reference produced by a top-level circuit's compiler is
well-routed. No concrete-circuit certificate is required. -/
theorem _root_.Halo2.TopLevelCircuit.permutationChunkRoutingCoherent
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) :
    PermutationChunkRoutingCoherent (top.toVerifierKey urs) := by
  intro chunk hchunk ref href
  have hchunkCS : chunk ∈ top.verifierCS.permutationChunks := by
    simpa only [top.toVerifierKey_permutationChunks] using hchunk
  have hflat : ref ∈ top.verifierCS.permutationChunks.flatten :=
    List.mem_flatten.mpr ⟨chunk, hchunkCS, href⟩
  rw [verifierCS_permutationChunks_flatten] at hflat
  obtain ⟨i, hi, hreference⟩ := List.mem_iff_getElem.mp hflat
  have hcolumnIndex : i < top.permutationColumns.length := by
    simpa only [List.length_zipIdx, List.length_map] using hi
  rw [← hreference]
  simp only [List.getElem_zipIdx, Nat.zero_add, List.getElem_map]
  constructor
  · exact permutationQueryReference_coherent top urs
      (List.getElem_mem hcolumnIndex)
  · rw [← top.permutationColumnCount_eq_permutationColumns_length]
      at hcolumnIndex
    exact hcolumnIndex

/-- Halo2's permutation chunk width is positive for every constraint system:
`csDegree` is at least the permutation argument's baseline degree three. -/
theorem constraintSystem_chunkLen_pos (cs : ConstraintSystem Fp) :
    0 < cs.chunkLen := by
  have hdegree : 3 ≤ csDegree cs :=
    three_le_constraintDegree cs.gates cs.lookups
  simp only [ConstraintSystem.chunkLen]
  omega

/-- The verifier CS emits exactly the circuit-owned ceiling number of chunks. -/
theorem verifierCS_permutationChunks_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.verifierCS.permutationChunks.length =
      top.permutationSetCount := by
  simp only [TopLevelCircuit.verifierCS]
  have hchunkLen : 0 < top.chunkLen :=
    constraintSystem_chunkLen_pos top.constraintSystem
  rw [listToChunks_length _ _
    hchunkLen]
  simp only [List.length_zipIdx, List.length_map]
  rw [top.permutationSetCount_eq,
    top.permutationColumnCount_eq_permutationColumns_length]

/-- A circuit-derived verifying key has exactly the circuit-owned number of
permutation sets. -/
@[simp] theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) :
    (top.toVerifierKey urs).permutationChunks.length =
      top.permutationSetCount := by
  rw [top.toVerifierKey_permutationChunks]
  exact verifierCS_permutationChunks_length top

/-- Each compiler chunk has the standard full-or-final-remainder width. -/
theorem verifierCS_permutationChunks_getD_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (i : ℕ) (hi : i < top.verifierCS.permutationChunks.length) :
    (top.verifierCS.permutationChunks.getD i []).length =
      min top.chunkLen
        (top.permutationColumnCount - i * top.chunkLen) := by
  simp only [TopLevelCircuit.verifierCS] at hi ⊢
  have hchunkLen : 0 < top.chunkLen := by
    exact constraintSystem_chunkLen_pos top.constraintSystem
  rw [listToChunks_getD_length top.chunkLen _ hchunkLen i hi]
  simp only [List.length_zipIdx, List.length_map]
  rw [top.permutationColumnCount_eq_permutationColumns_length]

/-- Every circuit-derived verifier chunk has the compiler-prescribed width. -/
theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_getD_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (i : ℕ)
    (hi : i < (top.toVerifierKey urs).permutationChunks.length) :
    ((top.toVerifierKey urs).permutationChunks.getD i []).length =
      min top.chunkLen
        (top.permutationColumnCount - i * top.chunkLen) := by
  rw [top.toVerifierKey_permutationChunks] at hi ⊢
  exact verifierCS_permutationChunks_getD_length top i hi

/-- Every prefix ending before a valid compiler chunk contains `i * chunkLen`
permutation columns. -/
theorem verifierCS_permutationChunks_take_flatten_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (i : ℕ) (hi : i < top.verifierCS.permutationChunks.length) :
    (top.verifierCS.permutationChunks.take i).flatten.length =
      i * top.chunkLen := by
  unfold TopLevelCircuit.verifierCS at hi ⊢
  apply take_flatten_length_of_dropLast_full
  · exact listToChunks_dropLast_full _ _
      (constraintSystem_chunkLen_pos top.constraintSystem)
  · exact hi

/-- Top-level keygen exposes the compiler prefix law without requiring downstream
proofs to unfold a concrete circuit or verifying-key constructor. -/
theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_take_flatten_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (i : ℕ) (hi : i < (top.toVerifierKey urs).permutationChunks.length) :
    (((top.toVerifierKey urs).permutationChunks.take i).flatten.length) =
      i * (top.toVerifierKey urs).chunkLen := by
  rw [top.toVerifierKey_permutationChunks] at hi ⊢
  rw [top.toVerifierKey_chunkLen]
  exact verifierCS_permutationChunks_take_flatten_length top i hi

/-- The compiler's chunk family has enough total slots for every permutation
column, without requiring the family itself to be nonempty. -/
theorem permutationColumns_length_le_chunks_mul
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.permutationColumnCount ≤
      top.verifierCS.permutationChunks.length * top.chunkLen := by
  let source :=
    (top.permutationColumns.map
      (permutationQueryReference top.adviceQueryLayout
        top.fixedQueryLayout top.instanceQueryLayout)).zipIdx
  have hall :
      (source.toChunks top.chunkLen).Forall
        fun chunk => chunk.length ≤ top.chunkLen :=
    listToChunks_all_le top.chunkLen source
      (constraintSystem_chunkLen_pos top.constraintSystem)
  have hbound :=
    flatten_length_le_mul_of_forall
      (source.toChunks top.chunkLen) top.chunkLen hall
  rw [listToChunks_flatten] at hbound
  have hchunks :
      top.verifierCS.permutationChunks =
        source.toChunks top.chunkLen := by
    unfold TopLevelCircuit.verifierCS
    dsimp only
    apply congrArg (List.toChunks top.chunkLen)
    congr 2
    funext column
    rcases column with ⟨kind, index⟩
    cases kind <;> rfl
  rw [hchunks]
  rw [top.permutationColumnCount_eq_permutationColumns_length]
  simpa only [source, List.length_zipIdx, List.length_map] using hbound

/-- A coherent compiled query reference decodes to the concrete column from
which the compiler created it. -/
theorem permutationColumnAddress_queryReference
    {shape : CircuitShape} {F G : Type}
    (vk : VerifyingKey shape F G)
    (adviceQueryLayout fixedQueryLayout instanceQueryLayout :
      List (ℕ × ℤ))
    (hadvice : vk.adviceQueryLayout = adviceQueryLayout)
    (hfixed : vk.fixedQueryLayout = fixedQueryLayout)
    (hinstance : vk.instanceQueryLayout = instanceQueryLayout)
    (column : AnyColumn)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        (permutationQueryReference adviceQueryLayout fixedQueryLayout
          instanceQueryLayout column)) :
    permutationColumnAddress vk
        (permutationQueryReference adviceQueryLayout fixedQueryLayout
          instanceQueryLayout column) = column := by
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hadvice] at hin ⊢
      rw [getD_findIdx_eq_target adviceQueryLayout
        (index, 0) (0, 0) hin]
  | fixed =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hfixed] at hin ⊢
      rw [getD_findIdx_eq_target fixedQueryLayout
        (index, 0) (0, 0) hin]
  | «instance» =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hinstance] at hin ⊢
      rw [getD_findIdx_eq_target instanceQueryLayout
        (index, 0) (0, 0) hin]

/--
For every closed top-level circuit, the permutation compiler's column encoding
is a round trip.
-/
theorem topLevelPermutationColumnAddresses_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) :
    top.verifierCS.permutationChunks.flatten.map
          (fun reference =>
            permutationColumnAddress (top.toVerifierKey urs) reference.1) =
      (Keygen.permColsOf top.constraintSystem).map
        Halo2.Layout.ColRef.toAny := by
  rw [verifierCS_permutationChunks_flatten]
  change
    List.map
        (permutationColumnAddress (top.toVerifierKey urs) ∘ Prod.fst)
        _ =
      _
  rw [← List.map_map, List.zipIdx_map_fst]
  simp only [Keygen.permColsOf, List.map_map]
  apply List.map_congr_left
  intro column hcolumn
  simp only [Function.comp_apply]
  let referenceOf :=
    permutationQueryReference top.adviceQueryLayout
      top.fixedQueryLayout top.instanceQueryLayout
  let reference :=
    referenceOf column
  have hreference :
      reference ∈
        top.permutationColumns.map
          referenceOf :=
    List.mem_map.mpr ⟨column, hcolumn, rfl⟩
  have hindexed :
      ∃ indexed ∈
          (top.permutationColumns.map
            referenceOf).zipIdx,
        indexed.1 = reference := by
    have hfst :
        reference ∈
          ((top.permutationColumns.map
            referenceOf).zipIdx).map Prod.fst := by
      rw [List.zipIdx_map_fst]
      exact hreference
    simpa only using List.mem_map.mp hfst
  obtain ⟨indexed, hindexed, hindexedReference⟩ := hindexed
  have hindexedFlat :
      indexed ∈
        top.verifierCS.permutationChunks.flatten := by
    rw [verifierCS_permutationChunks_flatten]
    simpa only [referenceOf] using hindexed
  obtain ⟨chunk, hchunk, hindexedChunk⟩ :=
    List.mem_flatten.mp hindexedFlat
  have hrouted := top.permutationChunkRoutingCoherent urs chunk (by
    simpa only [top.toVerifierKey_permutationChunks] using hchunk)
    indexed hindexedChunk
  have hreferenceCoherent :
      PermutationColumnRef.Coherent
        (top.toVerifierKey urs) reference := by
    rw [← hindexedReference]
    exact hrouted.1
  have hdecoded :
      permutationColumnAddress (top.toVerifierKey urs) reference =
        column :=
    permutationColumnAddress_queryReference
      (top.toVerifierKey urs)
      top.adviceQueryLayout top.fixedQueryLayout top.instanceQueryLayout
      (top.toVerifierKey_adviceQueryLayout urs)
      (top.toVerifierKey_fixedQueryLayout urs)
      (top.toVerifierKey_instanceQueryLayout urs)
      column hreferenceCoherent
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [reference, referenceOf, permutationQueryReference,
      Halo2.Layout.ColRef.toAny] using hdecoded

end Zcash.Snark
