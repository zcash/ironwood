import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Soundness.ForkingExtractor

/-!
# Round-by-round Fiat-Shamir transcript ordering (issue #23)

`Verifier.FiatShamir.deriveChallenges` squeezes the IPA round challenges with a `foldl` over the rounds that,
at round `j`, appends the round point `(Lⱼ, Rⱼ)` to the running transcript and *then* squeezes `uⱼ` from it:

    (List.finRange shape.k).foldl (fun (t, us) j =>
        let t := t ++ [.point Lⱼ, .point Rⱼ, .challenge]
        (t, us ++ [squeeze t])) (t₀, [])

This module makes the online ordering that `foldl` enforces explicit and proves it — the transcript-ordering
half of the prover-as-oracle bridge (`Soundness.Forking`, issue #11): the deployed schedule's own derivation
has the dependency structure the `Prover`/rewinding tree (`Soundness.ForkingExtractor.Prover`) assumes.

* `roundTranscript` — the transcript prefix `uⱼ` is squeezed from (the running `t` above, at step `j`).
* `roundTranscript_succ` — round `j+1`'s transcript is round `j`'s extended by exactly `(L_{j+1}, R_{j+1})`
  and the challenge marker: each round point is absorbed *before* that round's challenge and *after* every
  earlier round's challenge.
* `roundPoint_mem_roundTranscript` — `(Lⱼ, Rⱼ)` lies in the prefix `uⱼ` is squeezed from, so `uⱼ` is a
  function of a transcript containing `(Lⱼ, Rⱼ)`: the round point is fixed before its challenge and cannot
  depend on it (while later points, appended after, may depend on `uⱼ`).
* `roundTranscript_prefix_mono` — the base transcript `t₀` (through `z`) is a prefix of every round's
  transcript, and round transcripts grow monotonically, so no round's squeeze can see a *later* round's point.

`(L, R)` and the challenge marker not depending on `uⱼ` is a *structural* fact of the derivation
(`roundTranscript` is a function of `t₀` and the round points only — the squeezed `uⱼ` never re-enters it,
matching halo2's no-self-absorption). Tying the round points themselves to a challenge-prefix-respecting
`Prover` strategy — that `Lⱼ, Rⱼ` are chosen from `u₀ … u_{j-1}` but not `uⱼ` — is `Prover`/`proverAccept`'s
node/continuation shape; this module supplies the transcript side that shape mirrors.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- The transcript prefix from which the round-`j` IPA challenge `uⱼ` is squeezed, given the base transcript
`t₀` (everything absorbed through `z`) and the round points `rounds i = (Lᵢ, Rᵢ)`. Structurally the running
`t` in `deriveChallenges`'s IPA `foldl` at step `j`: `t₀` followed by `[.point Lᵢ, .point Rᵢ, .challenge]`
for every `i ≤ j`. -/
def roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) :
    ℕ → List (TranscriptElt F G)
  | 0 => t₀ ++ [.point (rounds 0).1, .point (rounds 0).2, .challenge]
  | j + 1 =>
      roundTranscript t₀ rounds j ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge]

/-- **Each round point is absorbed before its challenge, after all earlier challenges.** Round `j+1`'s
transcript is round `j`'s extended by exactly `(L_{j+1}, R_{j+1})` and the challenge marker — so `(Lⱼ, Rⱼ)`
enters the transcript strictly between `u_{j-1}`'s squeeze and `uⱼ`'s. -/
theorem roundTranscript_succ (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds (j + 1)
      = roundTranscript t₀ rounds j
        ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge] :=
  rfl

/-- **Monotone growth from the base transcript.** `t₀` (everything through `z`) is a prefix of every round's
transcript, and round `j`'s transcript is a prefix of round `j+1`'s — so no round's squeeze can see a later
round's point. -/
theorem roundTranscript_prefix_mono (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    t₀ <+: roundTranscript t₀ rounds j
      ∧ roundTranscript t₀ rounds j <+: roundTranscript t₀ rounds (j + 1) := by
  constructor
  · induction j with
    | zero => exact ⟨_, rfl⟩
    | succ j ih => exact ih.trans ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩
  · exact ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩

/-- **The round point is fixed before its challenge.** `(Lⱼ, Rⱼ)` occurs in `roundTranscript t₀ rounds j`,
the prefix `uⱼ = squeeze (roundTranscript t₀ rounds j)` is squeezed from. So `uⱼ` is a function of a
transcript containing the round point: `(Lⱼ, Rⱼ)` is determined before `uⱼ` and cannot depend on it. -/
theorem roundPoint_mem_roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    TranscriptElt.point (rounds j).1 ∈ roundTranscript t₀ rounds j ∧
      TranscriptElt.point (rounds j).2 ∈ roundTranscript t₀ rounds j := by
  cases j <;> exact ⟨by simp [roundTranscript], by simp [roundTranscript]⟩

/-- The round-`j` IPA challenge as the deployed schedule squeezes it: from the round-`j` transcript, which
contains `(Lⱼ, Rⱼ)` (`roundPoint_mem_roundTranscript`) and never the challenge `uⱼ` itself. -/
def roundChallenge (fs : FiatShamir F G) (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) : F :=
  fs.squeeze (roundTranscript t₀ rounds j)

/-- **The deployed schedule's IPA `foldl` builds the round-by-round transcript.** Folding the round points in
`L` — at each `i`, appending `[.point Lᵢ, .point Rᵢ, .challenge]` to the running transcript and squeezing —
the final transcript is the base `t₀` followed by every round's point-pair and challenge marker, in order.

This lambda is *exactly* the IPA `foldl` of `Verifier.FiatShamir.deriveChallenges` (with `rp = ps.ipaRounds`
and `L = List.finRange shape.k`). So it proves, for the actual derivation, that the deployed verifier absorbs
the round points sequentially — each `(Lᵢ, Rᵢ)` before its own challenge is squeezed and after every earlier
round's — with the squeezed challenges never re-entering the transcript (halo2's no-self-absorption). -/
theorem ipaFold_transcript {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).1
      = t₀ ++ (L.map (fun i =>
          [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge])).flatten := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih => simp only [List.foldl_cons, ih, List.map_cons, List.flatten_cons, List.append_assoc]

/-! ## The Prover-tree side: each round point is prefix-determined (issue #23, bullet 4)

`Soundness.ForkingExtractor.Prover` is `node (L R : G) (cont : F → Prover d)`: the round point `(L, R)` is a
field of the node — fixed — while `cont` takes the round challenge. So the *type* already forbids `(Lⱼ, Rⱼ)`
depending on `uⱼ`; below we read that off as a theorem, matching the transcript ordering above.
-/

/-- The round point `(Lⱼ, Rⱼ)` the prover strategy `P` commits at depth `j` down the challenge path `χ`:
descend `j` nodes following the earlier challenges `χ 0, …, χ (j-1)`, then read the reached node's fixed
`(L, R)` (`none` past the leaf). -/
def proverRoundPoint : {d : ℕ} → Prover F G d → (Fin d → F) → ℕ → Option (G × G)
  | 0, _, _, _ => none
  | _ + 1, .node L R _, _, 0 => some (L, R)
  | _ + 1, .node _ _ cont, χ, j + 1 => proverRoundPoint (cont (χ 0)) (Fin.tail χ) j

/-- **The Prover tree fixes each round point before its challenge (issue #23, bullet 4).** The depth-`j` round
point depends only on the earlier challenges `χ 0, …, χ (j-1)` — the path descended to reach the node — not on
that round's own challenge `χ j` or any later one: two paths agreeing on their first `j` entries yield the same
depth-`j` round point. This is the tree side of the transcript ordering (`roundPoint_mem_roundTranscript`):
`(Lⱼ, Rⱼ)` is prefix-determined, so the modeled prover commits it before seeing `uⱼ`, exactly as the deployed
transcript absorbs `(Lⱼ, Rⱼ)` before squeezing `uⱼ`. -/
theorem proverRoundPoint_prefix : {d : ℕ} → (P : Prover F G d) → (χ χ' : Fin d → F) → (j : ℕ) →
    (∀ i : Fin d, (i : ℕ) < j → χ i = χ' i) →
    proverRoundPoint P χ j = proverRoundPoint P χ' j
  | 0, .leaf _ _, _, _, _, _ => rfl
  | _ + 1, .node _ _ _, _, _, 0, _ => rfl
  | _ + 1, .node _ _ cont, χ, χ', j + 1, h => by
      have h0 : χ 0 = χ' 0 := h 0 (Nat.succ_pos j)
      show proverRoundPoint (cont (χ 0)) (Fin.tail χ) j = proverRoundPoint (cont (χ' 0)) (Fin.tail χ') j
      rw [h0]
      exact proverRoundPoint_prefix (cont (χ' 0)) (Fin.tail χ) (Fin.tail χ') j
        (fun i hi => h i.succ (by simp only [Fin.val_succ]; omega))

/-! ## Sealing the module to the deployed derivation

The lemmas above are stated over `roundTranscript`, a *reconstruction* of `deriveChallenges`'s IPA fold. To
rule out drift between the reconstruction and the deployed schedule, `deriveChallenges_ipaRound_eq` proves
the deployed round challenges *are* the round-by-round squeezes: `(deriveChallenges fs init ps).ipaRound j`
is `fs.squeeze` of the round-`j` transcript over the named base `preIpaTranscript init ps` and the proof's
own round points. Any refactor of `deriveChallenges` that changes the IPA absorb order breaks this theorem,
so the ordering facts hold of the deployed derivation itself, not of a mirror. -/

/-- The transcript `deriveChallenges` has absorbed when its IPA fold starts: `init`, then every pre-IPA
absorb block with its challenge markers, through the `z` marker. The chain never re-absorbs a squeezed
challenge (halo2's no-self-absorption), so it is a function of `init` and the proof string alone — no
`FiatShamir` argument. `deriveChallenges_ipaRound_eq` pins this to the deployed derivation. -/
def preIpaTranscript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]
  let t := t ++ [.challenge]
  t

/-- The challenge side of the IPA `foldl` (companion of `ipaFold_transcript`, which characterizes the
transcript side): the accumulated challenge list is `us₀` extended by, for each round position `m`, the
squeeze of the base extended by the first `m + 1` rounds' absorb blocks. -/
theorem ipaFold_challenges {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).2
      = us₀ ++ (List.range L.length).map (fun m =>
          fs.squeeze (t₀ ++ ((L.take (m + 1)).map (fun i =>
            [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
              TranscriptElt.challenge])).flatten)) := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih =>
      rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.take_succ_cons, List.take_zero, List.map_nil,
        List.flatten_cons, List.flatten_nil, Function.comp_def, List.append_assoc,
        List.cons_append, List.nil_append]

/-- `roundTranscript` in take-and-flatten form: the base followed by the first `j + 1` rounds' absorb
blocks. -/
theorem roundTranscript_eq_take (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds j
      = t₀ ++ ((List.range (j + 1)).map (fun i =>
          [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
            TranscriptElt.challenge])).flatten := by
  induction j with
  | zero => simp [roundTranscript]
  | succ j ih =>
      rw [roundTranscript_succ, ih, List.range_succ (n := j + 1), List.map_append,
        List.flatten_append, List.append_assoc]
      simp

/-- The round-`j` transcript over `Fin`-indexed round points — the form the deployed schedule's
`Fin shape.k → G × G` rounds produce directly. -/
def roundTranscriptFin {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G) (j : Fin k) :
    List (TranscriptElt F G) :=
  t₀ ++ (((List.finRange k).take (j.val + 1)).map (fun i =>
    [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
      TranscriptElt.challenge])).flatten

/-- The `Fin`-indexed round transcript is `roundTranscript` at (any `ℕ`-extension of) the same round
points: below `j` the wrap-around never fires. -/
theorem roundTranscriptFin_eq_roundTranscript {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    roundTranscriptFin t₀ rounds j
      = roundTranscript t₀ (fun i => rounds ⟨i % k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [roundTranscript_eq_take, roundTranscriptFin]
  congr 2
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_finRange, List.length_range]
    have := j.isLt
    omega
  · intro n h1 h2
    simp only [List.length_map, List.length_take, List.length_finRange, List.length_range] at h1 h2
    have hn : n < k := lt_of_lt_of_le (lt_min_iff.mp h1).1 (Nat.succ_le_of_lt j.isLt)
    simp only [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_range]
    refine congrArg (fun x => [TranscriptElt.point (rounds x).1, TranscriptElt.point (rounds x).2,
      TranscriptElt.challenge]) (Fin.ext ?_)
    simp [Nat.mod_eq_of_lt hn]

/-- **The anti-drift seal: the deployed schedule's IPA challenges are the round-by-round squeezes.**
`(deriveChallenges fs init ps).ipaRound j` is exactly `fs.squeeze` of the round-`j` transcript over the
named base `preIpaTranscript init ps` and the proof's own round points `ps.ipaRounds`. So
`roundTranscript_succ` / `roundPoint_mem_roundTranscript` / `roundTranscript_prefix_mono` hold *of the
deployed derivation itself* (#23, bullets 1–2): each `(Lⱼ, Rⱼ)` is absorbed before `uⱼ` is squeezed, and
`uⱼ` is sampled from the prefix containing it. A refactor of `deriveChallenges` that changes the IPA
absorb order breaks this theorem. -/
theorem deriveChallenges_ipaRound_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = fs.squeeze (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) := by
  simp only [deriveChallenges, preIpaTranscript, roundTranscriptFin]
  rw [ipaFold_challenges, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp)]
  rfl

/-- The seal in `roundChallenge` form: the deployed round-`j` challenge is `roundChallenge` at the deployed
base `preIpaTranscript` and (any `ℕ`-extension of) the proof's round points. -/
theorem deriveChallenges_ipaRound_eq_roundChallenge {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = roundChallenge fs (preIpaTranscript init ps)
          (fun i => ps.ipaRounds ⟨i % shape.k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [deriveChallenges_ipaRound_eq, roundChallenge, roundTranscriptFin_eq_roundTranscript]

end Zcash.Snark
