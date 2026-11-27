import Zcash.Common.Hash.Blake2bSimd.Loop
import Zcash.Common.Hash.Blake2b

/-!
# `blake2b_simd`'s compression loop is Ironwood's `hashBlocks`

`compress1Loop` with a `compress_block` that computes Ironwood's `compress` (`Refines`) compresses
its input as `Common/Hash/Blake2b.lean` does, for the serial stride one-stream hashing uses and
with the last-node flag off:

* with the final flag, it is `hashBlocks` (`compress1Loop_final`);
* without it, on one or more whole blocks, it compresses them all as non-final blocks, which is
  `fullBlocks` (`compress1Loop_notFinal`).

Both follow from `compress1LoopFrom_serial`, an induction on the loop's offset. Ironwood counts
bytes with a natural number and the loop with a wrapping 128-bit `Count`; the loop's count is
always `BitVec.ofNat 128` of Ironwood's, and the counter words agree for every count
(`countLow_ofNat`, `countHigh_ofNat`), so no bound on the input length is needed.
-/

namespace Zcash.Common.Blake2bSimd

open Blake2b (wordLE loadBlock compress hashBlocks)

/-- Shifting in zero bytes from zero gives zero. -/
theorem foldl_replicate_zero (n : ℕ) :
    (List.replicate n (0 : UInt8)).foldl
      (fun (acc : UInt64) (b : UInt8) => acc <<< 8 ||| b.toUInt64) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; exact ih

/-- Zero bytes after a word's bytes do not change it: `wordLE` reads missing bytes as zero. -/
theorem wordLE_append_replicate (l : List UInt8) (k : ℕ) :
    wordLE (l ++ List.replicate k 0) = wordLE l := by
  unfold wordLE
  rw [List.take_append, List.take_replicate, List.reverse_append, List.reverse_replicate,
    List.foldl_append, foldl_replicate_zero]

/-- Zero bytes after a block's bytes do not change it: `loadBlock` zero-pads. -/
theorem loadBlock_append_replicate (l : List UInt8) (k : ℕ) :
    loadBlock (l ++ List.replicate k 0) = loadBlock l := by
  apply Vector.ext
  intro i hi
  simp only [loadBlock, Vector.getElem_ofFn]
  rw [List.drop_append, List.drop_replicate, List.take_append, List.take_replicate,
    wordLE_append_replicate]

/-- `final_block` at `offset` with at most one block left: the block reads as the bytes left, and
its length is their count. -/
theorem finalBlock_last(input : List UInt8) (offset : ℕ) (h : input.length - offset ≤ 128) :
    loadBlock (finalBlock input offset (Vector.replicate 128 0)).1.toList =
      loadBlock (input.drop offset) ∧
    (finalBlock input offset (Vector.replicate 128 0)).2 = input.length - offset := by
  have hd : input.drop (min offset input.length) = input.drop offset := by
    rcases Nat.le_total offset input.length with ho | ho
    · rw [Nat.min_eq_left ho]
    · rw [Nat.min_eq_right ho, List.drop_eq_nil_of_le ho, List.drop_eq_nil_of_le (Nat.le_refl _)]
  unfold finalBlock
  simp only [hd]
  split
  · next hlen =>
    refine ⟨?_, ?_⟩
    · refine congrArg loadBlock ?_
      apply List.ext_getElem
      · simp only [Vector.length_toList, BLOCKBYTES, List.length_drop] at hlen ⊢; omega
      · intro i h1 h2; simp
    · simp only [BLOCKBYTES, List.length_drop] at hlen ⊢; omega
  · next hlen =>
    refine ⟨?_, by simp⟩
    rw [← loadBlock_append_replicate (input.drop offset) (128 - (input.drop offset).length)]
    refine congrArg loadBlock ?_
    apply List.ext_getElem
    · simp only [Vector.length_toList, List.length_append, List.length_replicate]
      simp only [BLOCKBYTES, List.length_drop] at hlen ⊢; omega
    · intro i h1 h2
      simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_append,
        List.getElem_replicate]
      split
      · rfl
      · simp [Fin.getElem_fin, Vector.getElem_replicate]

/-- `cb` computes Ironwood's `compress` when the last-node flag is off. -/
def Refines (cb : CompressBlockFn) : Prop :=
  ∀ block h t last, cb block h (BitVec.ofNat 128 t) (flagWord last) (flagWord false) =
    compress h (loadBlock block.toList) t last

/-- Ironwood's `compress` on each whole block of `xs` in turn, none of them final, counting from
`c`; bytes after the last whole block are left out. It is what the loop does before its final
block, and what `update` does to the input it compresses. -/
def fullBlocks (h : Vector UInt64 8) (c : ℕ) (xs : List UInt8) : Vector UInt64 8 :=
  if 128 ≤ xs.length then
    fullBlocks (compress h (loadBlock (xs.take 128)) (c + 128) false) (c + 128) (xs.drop 128)
  else h
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- Adding a block's 128 bytes to a count of `c` gives a count of `c + 128`. -/
theorem ofNat_add_128 (c : ℕ) : BitVec.ofNat 128 c + BitVec.ofNat 128 BLOCKBYTES =
    BitVec.ofNat 128 (c + 128) := by
  simp only [BLOCKBYTES, BitVec.ofNat_add_ofNat]

/-- The loop from `offset`: the full blocks up to `fin_offset`, then the final block. -/
theorem compress1LoopFrom_serial (cb : CompressBlockFn) (hcb : Refines cb) (input : List UInt8)
    (finOffset : ℕ) (finBlock : Vector UInt8 128) (finLen : ℕ) (flb fln : Word)
    (hfinDvd : Stride.serial.paddedBlockBytes ∣ finOffset)
    (hfinLe : finOffset ≤ input.length - 1)
    (offset : ℕ) (hle : offset ≤ finOffset) (hdvd : Stride.serial.paddedBlockBytes ∣ offset)
    (words : Vector Word 8) (c : ℕ) :
    compress1LoopFrom cb input .serial finOffset finBlock finLen flb fln hfinDvd hfinLe offset hle
        hdvd words (BitVec.ofNat 128 c) =
      cb finBlock (fullBlocks words c ((input.drop offset).take (finOffset - offset)))
        (BitVec.ofNat 128 (c + (finOffset - offset) + finLen)) flb fln := by
  obtain ⟨n, hn⟩ : ∃ n, finOffset - offset = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing offset words c with
  | _ n ih =>
    rw [compress1LoopFrom]
    by_cases hfin : offset = finOffset
    · subst hfin
      rw [dif_pos rfl, Nat.sub_self, List.take_zero, fullBlocks, if_neg (by simp), Nat.add_zero,
        BitVec.ofNat_add_ofNat]
    · rw [dif_neg hfin]
      have hstep : offset + 128 ≤ finOffset := by
        have := add_le_of_dvd_of_lt (Nat.lt_of_le_of_ne hle hfin) hdvd hfinDvd
        simpa [Stride.paddedBlockBytes] using this
      simp only [ofNat_add_128]
      rw [hcb]
      have hp : Stride.serial.paddedBlockBytes = 128 := rfl
      rw [ih (n - 128) (by omega) (offset + Stride.serial.paddedBlockBytes)
        (by rw [hp]; omega) (Nat.dvd_add hdvd (Nat.dvd_refl _)) _ _ (by rw [hp]; omega)]
      have hblock : (Vector.ofFn fun i : Fin 128 =>
          input[offset + i.val]'(by omega)).toList =
          (input.drop offset).take 128 := by
        apply List.ext_getElem
        · simp only [Vector.length_toList, List.length_take, List.length_drop]; omega
        · intro i h1 h2; simp
      have hlen : 128 ≤ (List.take (finOffset - offset) (List.drop offset input)).length := by
        simp only [List.length_take, List.length_drop]; omega
      conv => rhs; rw [fullBlocks, if_pos hlen]
      rw [hp, hblock, List.take_take, Nat.min_eq_left (by omega), List.drop_take, List.drop_drop,
        show finOffset - offset - 128 = finOffset - (offset + 128) by omega,
        show c + 128 + (finOffset - (offset + 128)) = c + (finOffset - offset) by omega]

/-- `fullBlocks` on no bytes leaves the state as it was. -/
theorem fullBlocks_nil (h : Vector UInt64 8) (c : ℕ) : fullBlocks h c [] = h := by
  rw [fullBlocks, if_neg (by simp)]

/-- One whole block first: `fullBlocks` compresses it, then goes on. -/
theorem fullBlocks_cons (h : Vector UInt64 8) (c : ℕ) (xs : List UInt8) (hx : 128 ≤ xs.length) :
    fullBlocks h c xs =
      fullBlocks (compress h (loadBlock (xs.take 128)) (c + 128) false) (c + 128)
        (xs.drop 128) := by
  rw [fullBlocks, if_pos hx]

/-- Split `hashBlocks` after `128 * j` bytes, when more than that is left. -/
theorem hashBlocks_split (j : ℕ) (h : Vector UInt64 8) (c : ℕ) (input : List UInt8)
    (hj : 128 * j < input.length ∨ j = 0) :
    hashBlocks h c input =
      hashBlocks (fullBlocks h c (input.take (128 * j))) (c + 128 * j) (input.drop (128 * j)) := by
  induction j generalizing h c input with
  | zero => simp [fullBlocks_nil]
  | succ j ih =>
    have hlen : 128 < input.length := by omega
    have hd : 128 * j < (input.drop 128).length ∨ j = 0 := by
      simp only [List.length_drop]; omega
    rw [hashBlocks, if_neg (by omega), ih (input := input.drop 128) (hj := hd)]
    have ht : 128 ≤ (input.take (128 * (j + 1))).length := by
      simp only [List.length_take]; omega
    conv => rhs; rw [fullBlocks_cons _ _ _ ht]
    rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take, List.drop_drop,
      show 128 * (j + 1) - 128 = 128 * j by omega, show 128 + 128 * j = 128 * (j + 1) by omega,
      show c + 128 + 128 * j = c + 128 * (j + 1) by omega]

/-- Split `fullBlocks` after `128 * j` bytes. -/
theorem fullBlocks_split (j : ℕ) (h : Vector UInt64 8) (c : ℕ) (input : List UInt8)
    (hj : 128 * j ≤ input.length) :
    fullBlocks h c input =
      fullBlocks (fullBlocks h c (input.take (128 * j))) (c + 128 * j) (input.drop (128 * j)) := by
  induction j generalizing h c input with
  | zero => simp [fullBlocks_nil]
  | succ j ih =>
    have hd : 128 * j ≤ (input.drop 128).length := by simp only [List.length_drop]; omega
    rw [fullBlocks_cons _ _ _ (by omega), ih (input := input.drop 128) (hj := hd)]
    have ht : 128 ≤ (input.take (128 * (j + 1))).length := by
      simp only [List.length_take]; omega
    conv => rhs; rw [fullBlocks_cons _ _ _ ht]
    rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take, List.drop_drop,
      show 128 * (j + 1) - 128 = 128 * j by omega, show 128 + 128 * j = 128 * (j + 1) by omega,
      show c + 128 + 128 * j = c + 128 * (j + 1) by omega]

/-- **The final loop is `hashBlocks`.** With the final flag and the last-node flag off, the serial
loop compresses `input` as Ironwood's `hashBlocks` does, from `c` bytes already counted. -/
theorem compress1Loop_final (cb : CompressBlockFn) (hcb : Refines cb) (input : List UInt8)
    (words : Vector Word 8) (c : ℕ) :
    compress1Loop cb input words (BitVec.ofNat 128 c) .no .yes .serial =
      hashBlocks words c input := by
  have hp : Stride.serial.paddedBlockBytes = 128 := rfl
  unfold compress1Loop
  rw [compress1LoopFrom_serial cb hcb]
  simp only [hp, Nat.sub_zero, List.drop_zero, Finalize.isYes, LastNode.isYes, Bool.and_false]
  have hrest : input.length - ((input.length - 1) - (input.length - 1) % 128) ≤ 128 := by omega
  obtain ⟨hload, hlen⟩ := finalBlock_last input _ hrest
  rw [hcb, hload, hlen]
  obtain ⟨j, hj⟩ : 128 ∣ (input.length - 1) - (input.length - 1) % 128 := Nat.dvd_sub_mod _
  rw [hashBlocks_split j words c input (by omega), ← hj, hashBlocks, if_pos (by simp; omega)]
  simp only [List.length_drop]

/-- **The non-final loop is `fullBlocks`.** Without the final flag, on one or more whole blocks,
the serial loop compresses them all as non-final blocks. -/
theorem compress1Loop_notFinal (cb : CompressBlockFn) (hcb : Refines cb) (input : List UInt8)
    (h128 : 128 ∣ input.length) (hpos : 0 < input.length) (words : Vector Word 8) (c : ℕ) :
    compress1Loop cb input words (BitVec.ofNat 128 c) .no .no .serial =
      fullBlocks words c input := by
  have hp : Stride.serial.paddedBlockBytes = 128 := rfl
  unfold compress1Loop
  rw [compress1LoopFrom_serial cb hcb]
  simp only [hp, Nat.sub_zero, List.drop_zero, Finalize.isYes, Bool.false_and]
  have hrest : input.length - ((input.length - 1) - (input.length - 1) % 128) ≤ 128 := by omega
  obtain ⟨hload, hlen⟩ := finalBlock_last input _ hrest
  rw [hcb, hload, hlen]
  have hfo : (input.length - 1) - (input.length - 1) % 128 = input.length - 128 := by
    obtain ⟨k, hk⟩ := h128; omega
  rw [hfo]
  obtain ⟨k, hk⟩ := h128
  rw [fullBlocks_split (k - 1) words c input (by omega),
    show 128 * (k - 1) = input.length - 128 by omega,
    fullBlocks_cons (fullBlocks words c (input.take (input.length - 128)))
      (c + (input.length - 128)) (input.drop (input.length - 128))
      (by simp only [List.length_drop]; omega), List.drop_drop,
    List.drop_eq_nil_of_le (show input.length ≤ input.length - 128 + 128 by omega),
    fullBlocks_nil,
    List.take_of_length_le (show (input.drop (input.length - 128)).length ≤ 128 by
      simp only [List.length_drop]; omega),
    show input.length - (input.length - 128) = 128 by omega]

end Zcash.Common.Blake2bSimd
