import Zcash.Common.Hash.Blake2bSimd.State
import Zcash.Common.Hash.Blake2bSimd.Avx2Spec

/-!
# The `blake2b_simd` transcription computes BLAKE2b in Halo 2's setup

Set up as Halo 2 sets it up, `Params::new().hash_length(64).personal(p).to_state()`, then
updated with any pieces of input in order and finalized, the transcription of `blake2b_simd` gives
`digest64 p` of their concatenation (`halo2_finalize_eq_digest64`). This holds with any
implementation, since each one's compression loop refines Ironwood's
(`Implementation.loop_refines`). That the transcription matches the Rust is not proved here.

The proof is an invariant on the state after input `X` (`Inv`): it has compressed the first `k`
bytes, a multiple of 128, as whole blocks; it buffers the rest; and the buffer is non-empty once
there is input. `update` keeps it (`update_inv`). Because the buffer is never empty at the end,
`finalize` compresses the last block of `X` as the final one, which is what `hashBlocks` does
(`finalize_inv`).

`finalize` does not change the state, so Halo 2's challenges, each a `finalize` of a clone after
the input so far, are each this theorem applied to that input.
-/

namespace Zcash.Common.Blake2bSimd

open Blake2b (hashBlocks finalBytes initialState digest64 wordLE)

/-- `fill_buf` buffers as many bytes as fit. -/
theorem fillBuf_buflen (st : State) (input : List UInt8) :
    (st.fillBuf input).1.buflen.val = st.buflen.val + min (128 - st.buflen.val) input.length := by
  simp only [State.fillBuf, BLOCKBYTES]

/-- `fill_buf` returns the input after the bytes it buffered. -/
theorem fillBuf_rest (st : State) (input : List UInt8) :
    (st.fillBuf input).2 = input.drop (128 - st.buflen.val) := by
  simp only [State.fillBuf, BLOCKBYTES]
  rcases Nat.le_total (128 - st.buflen.val) input.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (Nat.le_refl _)]

/-- `fill_buf` changes only the buffer and its length. -/
theorem fillBuf_fields (st : State) (input : List UInt8) :
    (st.fillBuf input).1.words = st.words ∧ (st.fillBuf input).1.count = st.count ∧
    (st.fillBuf input).1.implementation = st.implementation ∧
    (st.fillBuf input).1.lastNode = st.lastNode ∧
    (st.fillBuf input).1.hashLength = st.hashLength := by
  simp only [State.fillBuf, and_self]

/-- `fill_buf` appends the bytes it takes to the buffered bytes. -/
theorem fillBuf_buf (st : State) (input : List UInt8) :
    (st.fillBuf input).1.buf.toList.take (st.fillBuf input).1.buflen.val =
      st.buf.toList.take st.buflen.val ++ input.take (128 - st.buflen.val) := by
  have hb := st.buflen.isLt
  rw [fillBuf_buflen]
  apply List.ext_getElem
  · simp only [List.length_take, Vector.length_toList, List.length_append]
    omega
  · intro i h1 h2
    simp only [List.length_take, Vector.length_toList] at h1
    simp only [State.fillBuf, BLOCKBYTES, List.getElem_take, Vector.getElem_toList,
      Vector.getElem_ofFn, List.getElem_append]
    have hl : (List.take st.buflen.val st.buf.toList).length = st.buflen.val := by simp; omega
    simp only [hl]
    split
    · next hc => rw [dif_neg (by omega)]
    · next hc =>
      rw [dif_pos (by omega)]
      simp [Fin.getElem_fin]

/-- What `update` keeps true, short of the buffer being non-empty: after input `X`, the state has
compressed the first `k` bytes, a multiple of 128, as whole blocks from `h0`, and buffers the
rest. -/
def InvW (cb : CompressBlockFn) (h0 : Vector Word 8) (st : State) (X : List UInt8) : Prop :=
  (∀ input words count lastNode finalize stride,
    st.implementation.compress1Loop input words count lastNode finalize stride =
      compress1Loop cb input words count lastNode finalize stride) ∧
  st.lastNode = .no ∧
  ∃ k, st.count = BitVec.ofNat 128 k ∧ 128 ∣ k ∧ k + st.buflen.val = X.length ∧
    st.words = fullBlocks h0 0 (X.take k) ∧ st.buf.toList.take st.buflen.val = X.drop k

/-- The invariant: `InvW`, and the buffer is non-empty once there is input, so the last block is
still buffered for `finalize`. -/
def Inv (cb : CompressBlockFn) (h0 : Vector Word 8) (st : State) (X : List UInt8) : Prop :=
  InvW cb h0 st X ∧ (X ≠ [] → 0 < st.buflen.val)

/-- `compress_buffer_if_possible` keeps `InvW`, with the bytes it took appended. If input is left,
the buffer is empty; if none is, the buffer is non-empty once there is input. -/
theorem cbip_spec (cb : CompressBlockFn) (hcb : Refines cb) (h0 : Vector Word 8) (st : State)
    (X input : List UInt8) (hinv : Inv cb h0 st X) :
    ∃ X1, X1 ++ (st.compressBufferIfPossible input).2 = X ++ input ∧
      InvW cb h0 (st.compressBufferIfPossible input).1 X1 ∧
      ((st.compressBufferIfPossible input).2 ≠ [] →
        (st.compressBufferIfPossible input).1.buflen.val = 0) ∧
      ((st.compressBufferIfPossible input).2 = [] → X1 ≠ [] →
        0 < (st.compressBufferIfPossible input).1.buflen.val) := by
  obtain ⟨⟨himpl, hln, k, hcount, hk, hlen, hwords, hbuf⟩, hpos⟩ := hinv
  by_cases hb : st.buflen.val > 0
  · have hbl := fillBuf_buflen st input
    have hrest := fillBuf_rest st input
    have hbuf' := fillBuf_buf st input
    obtain ⟨hw', hc', hi', hl', -⟩ := fillBuf_fields st input
    rcases hr : st.fillBuf input with ⟨st', rest⟩
    rw [hr] at hbl hrest hbuf' hw' hc' hi' hl'
    simp only at hbl hrest hbuf' hw' hc' hi' hl'
    simp only [State.compressBufferIfPossible, if_pos hb, hr]
    have hblt := st.buflen.isLt
    by_cases hre : rest = []
    · simp only [hre, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
      have htake : input.take (128 - st.buflen.val) = input := by
        rw [hre] at hrest
        exact List.take_of_length_le (by
          have := congrArg List.length hrest; simp at this; omega)
      refine ⟨X ++ input, by simp, ⟨?_, ?_, k, ?_, hk, ?_, ?_, ?_⟩, fun h => absurd rfl h,
        fun _ _ => by omega⟩
      · rw [hi']; exact himpl
      · rw [hl']; exact hln
      · rw [hc']; exact hcount
      · simp only [List.length_append]; rw [hbl]
        have := congrArg List.length htake; simp at this; omega
      · rw [hw', hwords, List.take_append_of_le_length (by omega)]
      · rw [hbuf', hbuf, htake, List.drop_append_of_le_length (by omega)]
    · have hne : (!rest.isEmpty) = true := by simp [hre]
      simp only [hne, if_true]
      have hgt : 128 - st.buflen.val < input.length := by
        rw [hrest] at hre
        exact Nat.lt_of_not_le fun hc => hre (List.drop_eq_nil_of_le hc)
      have h128 : st'.buflen.val = 128 := by rw [hbl]; omega
      have hbuflist : st'.buf.toList = X.drop k ++ input.take (128 - st.buflen.val) := by
        rw [← hbuf, ← hbuf', h128, List.take_of_length_le (by simp)]
      have hX1len : (X ++ input.take (128 - st.buflen.val)).length = k + 128 := by
        simp only [List.length_append, List.length_take]; omega
      refine ⟨X ++ input.take (128 - st.buflen.val), ?_,
        ⟨?_, ?_, k + 128, ?_, ?_, ?_, ?_, ?_⟩,
        fun _ => rfl, fun h => absurd h hre⟩
      · rw [hrest, List.append_assoc, List.take_append_drop]
      · rw [hi']; exact himpl
      · rw [hl']; exact hln
      · show st'.count + BitVec.ofNat 128 BLOCKBYTES = _
        rw [hc', hcount, ofNat_add_128]
      · exact Nat.dvd_add hk (Nat.dvd_refl _)
      · show k + 128 + 0 = _
        omega
      · show st'.implementation.compress1Loop st'.buf.toList st'.words st'.count st'.lastNode .no
          .serial = _
        rw [hi', himpl, hl', hln, hc', hcount, compress1Loop_notFinal cb hcb _ (by simp) (by simp),
          hw', hwords, hbuflist,
          List.take_of_length_le (show (X ++ input.take (128 - st.buflen.val)).length ≤ k + 128 by
            omega)]
        obtain ⟨j, hj⟩ := hk
        rw [fullBlocks_split j h0 0 (X ++ input.take (128 - st.buflen.val)) (by omega), ← hj,
          List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
          Nat.zero_add]
      · show List.take 0 _ = _
        rw [List.take_zero, List.drop_eq_nil_of_le (by omega)]
  · have hb0 : st.buflen.val = 0 := by omega
    simp only [State.compressBufferIfPossible, if_neg hb]
    exact ⟨X, rfl, ⟨himpl, hln, k, hcount, hk, hlen, hwords, hbuf⟩, fun _ => hb0,
      fun h hX => by subst h; exact hpos (by simpa using hX)⟩

/-- `fill_buf` with input that fits keeps `InvW`, with the input appended. -/
theorem fill_inv (cb : CompressBlockFn) (h0 : Vector Word 8) (st : State) (X input : List UInt8)
    (hinv : InvW cb h0 st X) (hfit : input.length ≤ 128 - st.buflen.val) :
    InvW cb h0 (st.fillBuf input).1 (X ++ input) ∧
      (st.fillBuf input).1.buflen.val = st.buflen.val + input.length := by
  obtain ⟨himpl, hln, k, hcount, hk, hlen, hwords, hbuf⟩ := hinv
  have hbl := fillBuf_buflen st input
  have hbuf' := fillBuf_buf st input
  obtain ⟨hw', hc', hi', hl', -⟩ := fillBuf_fields st input
  have htake : input.take (128 - st.buflen.val) = input := List.take_of_length_le hfit
  have hbl' : (st.fillBuf input).1.buflen.val = st.buflen.val + input.length := by
    rw [hbl]; omega
  refine ⟨⟨?_, ?_, k, ?_, hk, ?_, ?_, ?_⟩, hbl'⟩
  · rw [hi']; exact himpl
  · rw [hl']; exact hln
  · rw [hc']; exact hcount
  · simp only [List.length_append]; omega
  · rw [hw', hwords, List.take_append_of_le_length (by omega)]
  · rw [hbuf', hbuf, htake, List.drop_append_of_le_length (by omega)]

/-- `update` keeps `Inv`, with the input appended. -/
theorem update_inv (cb : CompressBlockFn) (hcb : Refines cb) (h0 : Vector Word 8) (st : State)
    (X input : List UInt8) (hinv : Inv cb h0 st X) :
    Inv cb h0 (st.update input) (X ++ input) := by
  obtain ⟨X1, hX1, hinv1, hzero, hposc⟩ := cbip_spec cb hcb h0 st X input hinv
  rcases hc : st.compressBufferIfPossible input with ⟨st1, in1⟩
  rw [hc] at hX1 hinv1 hzero hposc
  simp only at hX1 hinv1 hzero hposc
  simp only [State.update, hc, BLOCKBYTES]
  rw [← hX1]
  have hinv1' := hinv1
  obtain ⟨himpl, hln, k, hcount, hk, hlen, hwords, hbuf⟩ := hinv1
  by_cases he : in1.length - 1 - (in1.length - 1) % 128 > 0
  · rw [if_pos he]
    simp only
    have hne : in1 ≠ [] := by intro h; subst h; simp at he
    have hb0 := hzero hne
    have hkX : k = X1.length := by omega
    have hele : in1.length - 1 - (in1.length - 1) % 128 < in1.length := by
      have : 0 < in1.length := List.length_pos_iff.mpr hne; omega
    have hdvd : 128 ∣ in1.length - 1 - (in1.length - 1) % 128 := Nat.dvd_sub_mod _
    have hfit : in1.length - (in1.length - 1 - (in1.length - 1) % 128) ≤ 128 := by omega
    generalize in1.length - 1 - (in1.length - 1) % 128 = e at he hele hdvd hfit ⊢
    have hinv2 : InvW cb h0
        { st1 with
          words := st1.implementation.compress1Loop (in1.take e) st1.words st1.count st1.lastNode
            .no .serial,
          count := st1.count + BitVec.ofNat 128 e } (X1 ++ in1.take e) := by
      refine ⟨himpl, hln, k + e, ?_, Nat.dvd_add hk hdvd, ?_, ?_, ?_⟩
      · show st1.count + BitVec.ofNat 128 e = _
        rw [hcount, BitVec.ofNat_add_ofNat]
      · show k + e + st1.buflen.val = _
        simp only [List.length_append, List.length_take]; omega
      · show st1.implementation.compress1Loop (in1.take e) st1.words st1.count st1.lastNode .no
          .serial = _
        rw [himpl, hln, hcount, compress1Loop_notFinal cb hcb _ (by simp; omega) (by simp; omega),
          hwords, List.take_of_length_le (show (X1 ++ in1.take e).length ≤ k + e by simp; omega)]
        obtain ⟨j, hj⟩ := hk
        rw [fullBlocks_split j h0 0 (X1 ++ in1.take e) (by simp; omega), ← hj, Nat.zero_add,
          List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
          hkX, List.drop_length, List.nil_append]
      · show List.take st1.buflen.val st1.buf.toList = _
        rw [hb0, List.take_zero, List.drop_eq_nil_of_le (by simp; omega)]
    obtain ⟨hinv3, hbl3⟩ := fill_inv cb h0 _ _ (in1.drop e) hinv2 (by simp; omega)
    rw [List.append_assoc, List.take_append_drop] at hinv3
    refine ⟨hinv3, fun _ => ?_⟩
    rw [hbl3]; simp; omega
  · rw [if_neg he]
    simp only
    by_cases hne : in1 = []
    · subst hne
      obtain ⟨hinv3, hbl3⟩ := fill_inv cb h0 st1 X1 [] hinv1' (by simp)
      rw [List.append_nil] at hinv3 ⊢
      refine ⟨hinv3, fun hX => ?_⟩
      rw [hbl3]; simpa using hposc rfl hX
    · have hb0 := hzero hne
      obtain ⟨hinv3, hbl3⟩ := fill_inv cb h0 st1 X1 in1 hinv1' (by omega)
      refine ⟨hinv3, fun _ => ?_⟩
      rw [hbl3]
      have : 0 < in1.length := List.length_pos_iff.mpr hne
      omega

/-- `state_words_to_bytes` is Ironwood's `finalBytes`. -/
theorem stateWordsToBytes_eq (w : Vector Word 8) : stateWordsToBytes w = finalBytes w := by
  apply Vector.ext
  intro i hi
  simp [stateWordsToBytes, wordToLeBytes, finalBytes, Vector.get, Nat.toUInt64_eq]

/-- Under `Inv` for input `X`, `finalize`'s bytes are `finalBytes (hashBlocks h0 0 X)`. -/
theorem finalize_inv (cb : CompressBlockFn) (hcb : Refines cb) (h0 : Vector Word 8) (st : State)
    (X : List UInt8) (hinv : Inv cb h0 st X) :
    st.finalize.bytes = finalBytes (hashBlocks h0 0 X) := by
  obtain ⟨⟨himpl, hln, k, hcount, hk, hlen, hwords, hbuf⟩, hpos⟩ := hinv
  simp only [State.finalize]
  rw [himpl, hln, hcount, hbuf, hwords, compress1Loop_final cb hcb, stateWordsToBytes_eq]
  obtain ⟨j, hj⟩ := hk
  rw [hashBlocks_split j h0 0 X (by
    by_cases hX : X = []
    · right; subst hX; simp at hlen; omega
    · left; have := hpos hX; omega), ← hj, Nat.zero_add]

/-- Every implementation's loop is the loop with a `compress_block` that refines `compress`. -/
theorem Implementation.loop_refines (impl : Implementation) :
    ∃ cb, Refines cb ∧ ∀ input words count lastNode finalize stride,
      impl.compress1Loop input words count lastNode finalize stride =
        Blake2bSimd.compress1Loop cb input words count lastNode finalize stride := by
  rcases impl with ⟨_ | _ | _⟩
  · exact ⟨_, Portable.refines, fun _ _ _ _ _ _ => rfl⟩
  · exact ⟨_, Portable.refines, fun _ _ _ _ _ _ => rfl⟩
  · exact ⟨_, Avx2.refines, fun _ _ _ _ _ _ => rfl⟩

/-- The parameters Halo 2 sets: `Params::new` with a 64-byte digest and personalization `p`. -/
def halo2Params (impl : Implementation) (p : Vector UInt8 16) : Params :=
  { Params.new impl with hashLength := ⟨64, by decide⟩, personal := p }

/-- Halo 2's parameters start from Ironwood's `initialState`. -/
theorem halo2Params_toWords (impl : Implementation) (p : Vector UInt8 16) :
    (halo2Params impl p).toWords = initialState 64 p := by
  apply Vector.ext
  intro i hi
  simp only [halo2Params, Params.toWords, Params.new, initialState, Blake2b.upd, Vector.get, IV]
  interval_cases i <;>
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, Vector.getElem_set, Vector.getElem_toArray, Fin.coe_ofNat_eq_mod,
      Fin.val_cast, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false]
  all_goals first | decide | skip
  · exact UInt64.xor_zero
  · simp
  · simp only [Vector.getElem_replicate, wordFromLeBytes_zero, UInt64.xor_zero]
  · simp only [Vector.getElem_replicate, wordFromLeBytes_zero, UInt64.xor_zero]
  · rw [wordFromLeBytes]
    refine congrArg (Blake2b.IV[6] ^^^ ·) (congrArg wordLE (List.ext_getElem (by simp) ?_))
    intro j h1 h2; simp
  · rw [wordFromLeBytes]
    refine congrArg (Blake2b.IV[7] ^^^ ·) (congrArg wordLE (List.ext_getElem (by simp) ?_))
    intro j h1 h2; simp

/-- Halo 2's setters succeed on a 16-byte personalization, and give `halo2Params`. -/
theorem halo2_setup (impl : Implementation) (p : Vector UInt8 16) :
    ((Params.new impl).hashLength? 64 >>= fun params => params.personal? p.toList) =
      some (halo2Params impl p) := by
  have hp : (Vector.ofFn fun i : Fin 16 =>
      if h : i.val < p.toList.length then p.toList[i.val] else 0) = p := by
    apply Vector.ext; intro i hi; simp
  simp [Params.hashLength?, Params.personal?, OUTBYTES, PERSONALBYTES, halo2Params]

/-- `compress_buffer_if_possible` keeps the digest length. -/
theorem cbip_hashLength (st : State) (input : List UInt8) :
    (st.compressBufferIfPossible input).1.hashLength = st.hashLength := by
  have hf := (fillBuf_fields st input).2.2.2.2
  unfold State.compressBufferIfPossible
  rcases hr : st.fillBuf input with ⟨st', rest⟩
  rw [hr] at hf
  split
  · simp only
    split
    · exact hf
    · exact hf
  · rfl

/-- `update` keeps the digest length. -/
theorem update_hashLength (st : State) (input : List UInt8) :
    (st.update input).hashLength = st.hashLength := by
  have hc := cbip_hashLength st input
  unfold State.update
  rcases hcb : st.compressBufferIfPossible input with ⟨st1, in1⟩
  rw [hcb] at hc
  simp only
  split
  · rw [(fillBuf_fields _ _).2.2.2.2]; exact hc
  · rw [(fillBuf_fields _ _).2.2.2.2]; exact hc

/-- Any number of updates keep the digest length. -/
theorem foldl_update_hashLength (xs : List (List UInt8)) (st : State) :
    (xs.foldl State.update st).hashLength = st.hashLength := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, update_hashLength]

/-- Any number of updates keep the invariant, with their inputs appended. -/
theorem foldl_update_inv (cb : CompressBlockFn) (hcb : Refines cb) (h0 : Vector Word 8)
    (xs : List (List UInt8)) (st : State) (X : List UInt8) (hinv : Inv cb h0 st X) :
    Inv cb h0 (xs.foldl State.update st) (X ++ xs.flatten) := by
  induction xs generalizing st X with
  | nil => simpa using hinv
  | cons x xs ih =>
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    exact ih _ _ (update_inv cb hcb h0 st X x hinv)

/-- **The `blake2b_simd` transcription computes BLAKE2b in Halo 2's setup.** With any
implementation, a 64-byte digest and a 16-byte personalization `p`, updating with the pieces `xs`
in order and finalizing gives `digest64 p` of their concatenation. -/
theorem halo2_finalize_eq_digest64 (impl : Implementation) (p : Vector UInt8 16)
    (xs : List (List UInt8)) :
    ((Params.new impl).hashLength? 64 >>= fun params => params.personal? p.toList).map
        (fun params => (xs.foldl State.update params.toState).finalize.asBytes) =
      some (digest64 p xs.flatten).toList := by
  rw [halo2_setup, Option.map_some]
  refine congrArg some ?_
  obtain ⟨cb, hcb, hloop⟩ := impl.loop_refines
  have h0 := halo2Params_toWords impl p
  have hinv0 : Inv cb (initialState 64 p) (halo2Params impl p).toState [] := by
    refine ⟨⟨hloop, rfl, 0, rfl, Nat.dvd_zero _, rfl, ?_, rfl⟩, fun h => absurd rfl h⟩
    rw [List.take_nil, fullBlocks_nil, ← h0]
    rfl
  have hinv := foldl_update_inv cb hcb _ xs _ [] hinv0
  rw [List.nil_append] at hinv
  have hfin := finalize_inv cb hcb _ _ _ hinv
  simp only [Hash.asBytes, hfin, digest64]
  exact List.take_of_length_le (by
    show _ ≤ (xs.foldl State.update _).hashLength.val
    rw [foldl_update_hashLength]
    simp [Params.toState, State.withParams, halo2Params, Params.new])

end Zcash.Common.Blake2bSimd
