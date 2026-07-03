import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Round-by-round Fiat-Shamir transcript ordering (issue #23)

`Verifier.FiatShamir.deriveChallenges` squeezes the IPA round challenges with a `foldl` over the rounds that,
at round `j`, appends the round point `(Lⱼ, Rⱼ)` to the running transcript and *then* squeezes `uⱼ` from it:

    (List.finRange shape.k).foldl (fun (t, us) j =>
        let t := t ++ [.point Lⱼ, .point Rⱼ, .challenge]
        (t, us ++ [squeeze t])) (t₀, [])

This module makes the online ordering that `foldl` enforces explicit and proves it — the transcript-ordering
half of the prover-as-oracle bridge (`Soundness.Forking.Rewind`): the deployed schedule's own derivation
has the dependency structure the `Prover`/rewinding tree (`Soundness.Forking.Extractor.Prover`) assumes.

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
contains `(Lⱼ, Rⱼ)` (`roundPoint_mem_roundTranscript`) and never the challenge `uⱼ` itself.
`deriveChallenges_ipaRound_eq_roundChallenge` pins the deployed derivation to this form. -/
def roundChallenge (fs : FiatShamir F G) (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G)
    (j : ℕ) : F :=
  fs.squeeze (roundTranscript t₀ rounds j)

/-- **The deployed schedule's IPA `foldl` builds the round-by-round transcript.** Folding the round points in
`L` — at each `i`, appending `[.point Lᵢ, .point Rᵢ, .challenge]` to the running transcript and squeezing —
the final transcript is the base `t₀` followed by every round's point-pair and challenge marker, in order.

This lambda matches the IPA `foldl` of `Verifier.FiatShamir.deriveChallenges` (with `rp = ps.ipaRounds` and
`L = List.finRange shape.k`); the *instantiation* against the actual derivation is carried by the
challenge-side companion `ipaFold_challenges` inside the seal `deriveChallenges_ipaRound_eq` — which a
schedule refactor would break — with this transcript-side form documenting the same fold: the deployed
verifier absorbs the round points sequentially, each `(Lᵢ, Rᵢ)` before its own challenge is squeezed and
after every earlier round's, with the squeezed challenges never re-entering the transcript (halo2's
no-self-absorption). -/
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

`Soundness.Forking.Extractor.Prover` is `node (L R : G) (cont : F → Prover d)`: the round point `(L, R)` is a
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
own round points, and `roundTranscriptFin_eq_roundTranscript` / `deriveChallenges_ipaRound_eq_roundChallenge`
identify the sealed object with the reconstruction — so the ordering trio transports to the deployed
derivation rather than holding only of a mirror. Any refactor of `deriveChallenges` that changes the IPA
absorb order breaks the seal. -/

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
blocks — the shape `ipaFold_challenges` produces, bridging the fold to the recursion. -/
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

private theorem length_flatten_map_triple {ι : Type*} (f g h : ι → TranscriptElt F G) :
    ∀ l : List ι, ((l.map (fun i => [f i, g i, h i])).flatten).length = 3 * l.length
  | [] => rfl
  | i :: l => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        List.length_nil, length_flatten_map_triple f g h l]
      omega

/-- Each round's absorb block has three elements, so the round-`j` transcript extends the base by exactly
`3 · (j + 1)` — the length arithmetic behind "distinct rounds have distinct transcripts". -/
theorem roundTranscriptFin_length {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G)
    (j : Fin k) :
    (roundTranscriptFin t₀ rounds j).length = t₀.length + 3 * (j.val + 1) := by
  have hj := j.isLt
  simp only [roundTranscriptFin, List.length_append,
    length_flatten_map_triple (fun i => TranscriptElt.point (rounds i).1)
      (fun i => TranscriptElt.point (rounds i).2) (fun _ => TranscriptElt.challenge),
    List.length_take, List.length_finRange]
  omega

/-- Distinct rounds squeeze from distinct transcripts (their lengths differ by `3 · |j − j'|`) — the fact
that lets the oracle be reprogrammed at one round's prefix without touching any other round's challenge. -/
theorem roundTranscriptFin_injective {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) :
    Function.Injective (roundTranscriptFin t₀ rounds) := by
  intro a b h
  have hlen := congrArg List.length h
  rw [roundTranscriptFin_length, roundTranscriptFin_length] at hlen
  exact Fin.ext (by omega)

/-- **The mirror↔seal identification.** The `Fin`-indexed round transcript — the sealed object — is
`roundTranscript` at (any `ℕ`-extension of) the same round points: below `j` the wrap-around never fires.
This is what transports the ordering lemmas (`roundTranscript_succ` / `roundPoint_mem_roundTranscript` /
`roundTranscript_prefix_mono`) to the deployed derivation through the seal. -/
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
named base `preIpaTranscript init ps` and the proof's own round points `ps.ipaRounds`. Through the
identification `roundTranscriptFin_eq_roundTranscript` (and the `roundChallenge` form below),
`roundTranscript_succ` / `roundPoint_mem_roundTranscript` / `roundTranscript_prefix_mono` then hold *of the
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
base `preIpaTranscript` and (any `ℕ`-extension of) the proof's round points — so the ordering trio above
holds verbatim of the transcripts the deployed schedule actually squeezes. -/
theorem deriveChallenges_ipaRound_eq_roundChallenge {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = roundChallenge fs (preIpaTranscript init ps)
          (fun i => ps.ipaRounds ⟨i % shape.k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [deriveChallenges_ipaRound_eq, roundChallenge, roundTranscriptFin_eq_roundTranscript]

/-! ## Sealing the multiopen squeeze points (issue #18's rewinding note)

The multiopen rewinding (`Soundness.MultiopenDecode`) forks on the batching challenge `x₄`; the
analogue of the round-by-round treatment above needs the same two ingredients at the multiopen
squeeze points: the commit-before-challenge ordering (`q′` is absorbed before `x₃` is squeezed, the
`u` family before `x₄`), and named squeeze prefixes so the oracle can be reprogrammed there
(`Soundness.Forking.reprogramX4`). Mirroring `preIpaTranscript`, `preX3Transcript`/`preX4Transcript`
are fully inlined (not a chain of `++`), so `deriveChallenges_x3_eq`/`_x4_eq` hold by `rfl` and a
single `simp only [preX4Transcript, …]` unfolds the squeeze input in one step — the shape the
reprogramming length proofs use. A refactor of the absorb order breaks the seals. -/

/-- The transcript `deriveChallenges` has absorbed when `x₃` is squeezed: everything through the
`x₂` marker, then the multiopen `q′` commitment and the `x₃` challenge marker. -/
def preX3Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
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
  t

/-- The transcript at the `x₄` squeeze: the `x₃` prefix extended by the multiopen `u` evaluations
and the `x₄` marker (inlined for `rfl` seals and one-step `simp`). -/
def preX4Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
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
  t

/-- The deployed `x₃` *is* the squeeze of the named `x₃` prefix — the multiopen analogue of
`deriveChallenges_ipaRound_eq`. -/
theorem deriveChallenges_x3_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x3 = fs.squeeze (preX3Transcript init ps) := rfl

/-- The deployed `x₄` *is* the squeeze of the named `x₄` prefix. -/
theorem deriveChallenges_x4_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x4 = fs.squeeze (preX4Transcript init ps) := rfl

/-- Commit-before-challenge at `x₃`: the multiopen `q′` commitment is inside the `x₃` squeeze input,
fixed before the challenge. -/
theorem qPrime_mem_preX3Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    TranscriptElt.point ps.multiopenQPrime ∈ preX3Transcript init ps := by
  simp [preX3Transcript]

/-- Commit-before-challenge at `x₄`: every multiopen `u` evaluation is inside the `x₄` squeeze
input, fixed before the challenge. -/
theorem multiopenU_mem_preX4Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (i : Fin shape.numPointSets) :
    TranscriptElt.scalar (ps.multiopenU i) ∈ preX4Transcript init ps := by
  simp only [preX4Transcript, absorbScalars, List.mem_append, List.mem_ofFn]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

/-- The pre-IPA base is the `x₄` prefix extended by the IPA `S` commitment and the `ξ`/`z` markers,
so the multiopen squeezes sit strictly inside it. -/
theorem preIpaTranscript_length_eq {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preIpaTranscript init ps).length = (preX4Transcript init ps).length + 3 := by
  simp only [preIpaTranscript, preX4Transcript, List.length_append, List.length_cons,
    List.length_nil]

/-! ## Sealing the compression squeeze points `x₁`/`x₂`

The within-set (`x₁`) rewinding forks one squeeze earlier than the `x₄` collapse: redraw `x₁` and the
rewound prover re-sends the *post-`x₁`* proof fields (`q′`, `u`, the IPA opening), so `x₃`/`x₄`
re-randomize through their squeeze inputs while everything absorbed before `x₁` — the column
commitments and every claimed evaluation — is shared across runs. The seals here supply that ordering:
`preX1Transcript`/`preX2Transcript` name the squeeze inputs (inlined for `rfl` seals, like
`preX3Transcript`), the membership lemmas pin the claimed evaluations before `x₁`, and the length chain
places the compression squeezes strictly inside the multiopen ones. `Soundness.Forking.reprogramX1` is
the reprogramming at this prefix. -/

/-- The transcript `deriveChallenges` has absorbed when `x₁` is squeezed: everything through the `x`
marker, then all claimed evaluations and the `x₁` challenge marker. -/
def preX1Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
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
  t

/-- The transcript at the `x₂` squeeze: the `x₁` prefix extended by the `x₂` marker alone — nothing is
absorbed between the two compression squeezes. -/
def preX2Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
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
  t

/-- The deployed `x₁` *is* the squeeze of the named `x₁` prefix. -/
theorem deriveChallenges_x1_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x1 = fs.squeeze (preX1Transcript init ps) := rfl

/-- The deployed `x₂` *is* the squeeze of the named `x₂` prefix — completing the compression pair;
consumed at doc level by the `x₂`-stays-honest argument (`preX2Transcript_length_eq`), no in-tree
proof consumer yet. -/
theorem deriveChallenges_x2_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x2 = fs.squeeze (preX2Transcript init ps) := rfl

/-- Commit-before-challenge at `x₁`: every claimed advice evaluation is inside the `x₁` squeeze input,
fixed before the compression challenge — so it is shared across `x₁` rewinds. -/
theorem adviceEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (p : Fin shape.numProofs) (i : Fin shape.numAdviceQueries) :
    TranscriptElt.scalar (ps.adviceEvals p i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.adviceEvals p i)
      ∈ absorbScalars2 (F := F) (G := G) ps.adviceEvals := by
    simp only [absorbScalars2, absorbScalars, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem)))))))

/-- Commit-before-challenge at `x₁`: every claimed instance evaluation is inside the `x₁` squeeze
input. -/
theorem instanceEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (p : Fin shape.numProofs) (i : Fin shape.numInstanceQueries) :
    TranscriptElt.scalar (ps.instanceEvals p i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.instanceEvals p i)
      ∈ absorbScalars2 (F := F) (G := G) ps.instanceEvals := by
    simp only [absorbScalars2, absorbScalars, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem)))))))

/-- Commit-before-challenge at `x₁`: every claimed fixed evaluation is inside the `x₁` squeeze
input. -/
theorem fixedEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (i : Fin shape.numFixedQueries) :
    TranscriptElt.scalar (ps.fixedEvals i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.fixedEvals i)
      ∈ absorbScalars (F := F) (G := G) ps.fixedEvals := by
    simp only [absorbScalars, List.mem_ofFn]
    exact ⟨i, rfl⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hmem))))))

/-- The `x₂` prefix is the `x₁` prefix plus its marker: nothing is absorbed between the compression
squeezes, so an `x₁` reprogram leaves the `x₂` input at a different length (and every later squeeze
longer still). -/
theorem preX2Transcript_length_eq {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preX2Transcript init ps).length = (preX1Transcript init ps).length + 1 := by
  simp only [preX2Transcript, preX1Transcript, List.length_append, List.length_cons,
    List.length_nil]

/-- The `x₃` prefix is the `x₂` prefix extended by the `q′` commitment and the `x₃` marker — the
rewound prover's fresh `q′` is exactly what re-randomizes `x₃` across `x₁` rewinds. -/
theorem preX3Transcript_length_eq {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preX3Transcript init ps).length = (preX2Transcript init ps).length + 2 := by
  simp only [preX3Transcript, preX2Transcript, List.length_append, List.length_cons,
    List.length_nil]

end Zcash.Snark
