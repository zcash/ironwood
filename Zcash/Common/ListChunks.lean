import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.NormNum

/-!
# Structural laws for `List.toChunks`

These lemmas expose the count, flattening, and width behavior of the optimized
array-accumulator implementation used by the permutation compiler. They are
generic list facts and never evaluate a concrete circuit.
-/

namespace List

set_option maxHeartbeats 20000

/-- Flattening the accumulator implementation of `List.toChunks` preserves its
processed prefix and unprocessed suffix. -/
theorem toChunksGo_flatten {α : Type} (n : ℕ)
    (xs : List α) (current : Array α) (chunks : Array (List α)) :
    (List.toChunks.go n xs current chunks).flatten =
      chunks.toList.flatten ++ current.toList ++ xs := by
  induction xs generalizing current chunks with
  | nil =>
      simp [List.toChunks.go]
  | cons x xs ih =>
      simp only [List.toChunks.go]
      split
      · rw [ih]
        simp [List.flatten_append, List.append_assoc]
      · rw [ih]
        simp [List.append_assoc]

/-- Splitting a list into chunks and flattening it is the identity, including
the `chunkSize = 0` convention. -/
theorem toChunks_flatten {α : Type} (chunkSize : ℕ) (xs : List α) :
    (xs.toChunks chunkSize).flatten = xs := by
  cases chunkSize with
  | zero =>
      cases xs <;> simp [List.toChunks]
  | succ chunkSize =>
      cases xs with
      | nil => simp [List.toChunks]
      | cons x xs =>
          rw [List.toChunks]
          rw [toChunksGo_flatten]
          simp_all
          all_goals omega

theorem toChunksGo_length {α : Type} (n : ℕ)
    (xs : List α) (current : Array α) (chunks : Array (List α))
    (hn : 0 < n) (hcurrentPos : 0 < current.size)
    (hcurrent : current.size ≤ n) :
    (List.toChunks.go n xs current chunks).length =
      chunks.size + (current.size + xs.length + n - 1) / n := by
  induction xs generalizing current chunks with
  | nil =>
      simp only [List.toChunks.go]
      have hdiv :
          (current.size + n - 1) / n = 1 := by
        apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp
            ((Nat.div_lt_iff_lt_mul hn).2 (by omega))
        · exact (Nat.le_div_iff_mul_le hn).2 (by omega)
      simp [hdiv]
  | cons x xs ih =>
      simp only [List.toChunks.go]
      split
      · next hfull =>
        have hsize : current.size = n := by
          simpa only [beq_iff_eq] using hfull
        rw [ih _ _ (by simp) (by simpa using hn)]
        simp only [Array.size_push]
        change
          chunks.size + 1 + (1 + xs.length + n - 1) / n =
            chunks.size +
              (current.size + (x :: xs).length + n - 1) / n
        rw [hsize]
        have hnum :
            n + (x :: xs).length + n - 1 =
              (1 + xs.length + n - 1) + 1 * n := by
          simp only [List.length_cons]
          omega
        rw [hnum, Nat.add_mul_div_right _ _ hn]
        omega
      · next hnotfull =>
        have hne : current.size ≠ n := by
          simpa only [beq_iff_eq, Bool.not_eq_true] using hnotfull
        have hlt : current.size < n := by omega
        rw [ih _ _ (by simp) (by simpa using hlt)]
        simp only [Array.size_push, List.length_cons]
        congr 1
        congr 1
        omega

theorem toChunks_length {α : Type} (n : ℕ) (xs : List α) (hn : 0 < n) :
    (xs.toChunks n).length = (xs.length + n - 1) / n := by
  cases xs with
  | nil =>
      simp only [List.toChunks, List.length_nil]
      exact (Nat.div_eq_of_lt (by omega)).symm
  | cons x xs =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [List.toChunks]
          rw [toChunksGo_length (n + 1) xs #[x] #[] (by omega)
            (by simp) (by simp)]
          simp only [Array.size_empty]
          norm_num
          change
            (1 + xs.length + (n + 1) - 1) / (n + 1) =
              ((x :: xs).length + (n + 1) - 1) / (n + 1)
          congr 1
          simp only [List.length_cons]
          omega

theorem toChunksGo_dropLast_full {α : Type} (n : ℕ)
    (xs : List α) (current : Array α) (chunks : Array (List α))
    (hn : 0 < n) (hcurrentPos : 0 < current.size)
    (hcurrent : current.size ≤ n)
    (hchunks : chunks.toList.Forall fun chunk => chunk.length = n) :
    (List.toChunks.go n xs current chunks).dropLast.Forall
      fun chunk => chunk.length = n := by
  induction xs generalizing current chunks with
  | nil =>
      simp only [List.toChunks.go]
      simpa using hchunks
  | cons x xs ih =>
      simp only [List.toChunks.go]
      split
      · next hfull =>
        have hsize : current.size = n := by
          simpa only [beq_iff_eq] using hfull
        apply ih
        · simp
        · simpa using hn
        · simpa [hsize] using hchunks
      · next hnotfull =>
        have hne : current.size ≠ n := by
          simpa only [beq_iff_eq, Bool.not_eq_true] using hnotfull
        apply ih
        · simp
        · simpa using (show current.size < n by omega)
        · exact hchunks

theorem toChunksGo_all_le {α : Type} (n : ℕ)
    (xs : List α) (current : Array α) (chunks : Array (List α))
    (hn : 0 < n) (hcurrent : current.size ≤ n)
    (hchunks : chunks.toList.Forall fun chunk => chunk.length ≤ n) :
    (List.toChunks.go n xs current chunks).Forall
      fun chunk => chunk.length ≤ n := by
  induction xs generalizing current chunks with
  | nil =>
      simp only [List.toChunks.go]
      simpa [hcurrent] using hchunks
  | cons x xs ih =>
      simp only [List.toChunks.go]
      split
      · next hfull =>
        have hsize : current.size = n := by
          simpa only [beq_iff_eq] using hfull
        apply ih
        · simpa using hn
        · simpa [hsize] using hchunks
      · next hnotfull =>
        have hne : current.size ≠ n := by
          simpa only [beq_iff_eq, Bool.not_eq_true] using hnotfull
        apply ih
        · simpa using (show current.size < n by omega)
        · exact hchunks

theorem toChunks_all_le {α : Type} (n : ℕ) (xs : List α)
    (hn : 0 < n) :
    (xs.toChunks n).Forall fun chunk => chunk.length ≤ n := by
  cases xs with
  | nil => simp [List.toChunks]
  | cons x xs =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [List.toChunks]
          apply toChunksGo_all_le
          · omega
          · simp
          · change List.Forall (fun chunk : List α => chunk.length ≤ n + 1) []
            simp

theorem toChunks_dropLast_full {α : Type} (n : ℕ) (xs : List α)
    (hn : 0 < n) :
    (xs.toChunks n).dropLast.Forall fun chunk => chunk.length = n := by
  cases xs with
  | nil => simp [List.toChunks]
  | cons x xs =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [List.toChunks]
          apply toChunksGo_dropLast_full
          · omega
          · simp
          · simp
          · change List.Forall (fun chunk : List α => chunk.length = n + 1) []
            simp

theorem take_flatten_length_of_dropLast_full {α : Type}
    (chunks : List (List α)) (n i : ℕ)
    (hfull : chunks.dropLast.Forall fun chunk => chunk.length = n)
    (hi : i < chunks.length) :
    (chunks.take i).flatten.length = i * n := by
  induction chunks generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
      cases rest with
      | nil =>
          have : i = 0 := by simp at hi; omega
          simp [this]
      | cons second rest =>
          simp only [List.dropLast_cons_cons] at hfull
          rw [List.forall_cons] at hfull
          have hfirst : first.length = n := hfull.1
          have hrest :
              (second :: rest).dropLast.Forall
                fun chunk => chunk.length = n := by
            exact hfull.2
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.take_succ_cons, List.flatten_cons,
                List.length_append, hfirst]
              rw [ih i hrest (by simp at hi ⊢; omega)]
              simp [Nat.succ_mul, Nat.add_comm]

theorem getD_length_eq_min_of_chunk_shape {α : Type}
    (chunks : List (List α)) (n total i : ℕ)
    (hflatten : chunks.flatten.length = total)
    (hfull : chunks.dropLast.Forall fun chunk => chunk.length = n)
    (hall : chunks.Forall fun chunk => chunk.length ≤ n)
    (hi : i < chunks.length) :
    (chunks.getD i []).length = min n (total - i * n) := by
  have hgetD :
      chunks.getD i [] = chunks[i] :=
    List.getD_eq_getElem _ _ hi
  rw [hgetD]
  have hprefix :
      (chunks.take i).flatten.length = i * n :=
    take_flatten_length_of_dropLast_full chunks n i hfull hi
  have hstep :
      (chunks.take (i + 1)).flatten.length =
        (chunks.take i).flatten.length + chunks[i].length := by
    rw [List.take_succ_eq_append_getElem hi]
    simp only [List.flatten_append, List.flatten_singleton,
      List.length_append]
  have hchunkLe : chunks[i].length ≤ n := by
    exact (List.forall_iff_forall_mem.mp hall)
      chunks[i] (List.getElem_mem ..)
  by_cases hlast : i + 1 = chunks.length
  · have htake : chunks.take (i + 1) = chunks := by
      rw [hlast, List.take_length]
    rw [htake, hflatten, hprefix] at hstep
    have hremaining : total - i * n = chunks[i].length := by
      omega
    rw [hremaining, min_eq_right hchunkLe]
  · have hnext : i + 1 < chunks.length := by omega
    have hprefixNext :
        (chunks.take (i + 1)).flatten.length = (i + 1) * n :=
      take_flatten_length_of_dropLast_full chunks n (i + 1) hfull hnext
    have hprefixLe :
        (chunks.take (i + 1)).flatten.length ≤ chunks.flatten.length := by
      have hTakeAppendDrop :=
        congrArg List.flatten
          (List.take_append_drop (i + 1) chunks)
      simp only [List.flatten_append] at hTakeAppendDrop
      rw [← hTakeAppendDrop, List.length_append]
      exact Nat.le_add_right _ _
    have hnle : n ≤ total - i * n := by
      rw [hprefixNext, hflatten] at hprefixLe
      simp only [Nat.add_mul, one_mul] at hprefixLe
      omega
    have hchunkFull : chunks[i].length = n := by
      have hiDrop : i < chunks.dropLast.length := by
        simp only [List.length_dropLast]
        omega
      have hmem : chunks[i] ∈ chunks.dropLast := by
        rw [← List.getElem_dropLast hiDrop]
        exact List.getElem_mem ..
      exact (List.forall_iff_forall_mem.mp hfull) chunks[i] hmem
    rw [hchunkFull, min_eq_left hnle]

theorem toChunks_getD_length {α : Type} (n : ℕ) (xs : List α)
    (hn : 0 < n) (i : ℕ) (hi : i < (xs.toChunks n).length) :
    ((xs.toChunks n).getD i []).length =
      min n (xs.length - i * n) := by
  apply getD_length_eq_min_of_chunk_shape
  · simp only [toChunks_flatten]
  · exact toChunks_dropLast_full n xs hn
  · exact toChunks_all_le n xs hn
  · exact hi

/-- A list of at most `n`-wide chunks contains at most `chunks.length * n`
elements after flattening. -/
theorem flatten_length_le_mul_of_forall {α : Type}
    (chunks : List (List α)) (n : ℕ)
    (hall : chunks.Forall fun chunk => chunk.length ≤ n) :
    chunks.flatten.length ≤ chunks.length * n := by
  induction chunks with
  | nil => simp
  | cons chunk chunks ih =>
      rw [List.forall_cons] at hall
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      have hsum :=
        Nat.add_le_add hall.1 (ih hall.2)
      simpa only [Nat.add_mul, one_mul, Nat.add_comm] using hsum

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

end List
