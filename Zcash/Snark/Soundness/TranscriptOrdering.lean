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

end Zcash.Snark
