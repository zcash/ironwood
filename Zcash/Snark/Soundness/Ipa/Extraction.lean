import Mathlib
import Zcash.Snark.Soundness.Ipa.InnerProduct

/-!
# The full IPA extractor: composing the round extractor over all `k` rounds

`Zcash.Snark.roundExtract_correct` gives 2-special-soundness of one IPA round. This module composes it
over the `k` rounds to recover the whole witness from a tree of accepting transcripts: at each internal
node the two distinct round challenges let the round extractor fold the two sub-witnesses back into one,
and the leaves carry the fully-folded scalars.

* `loHalf` / `hiHalf` / `append` — split a length-`2^{k+1}` vector into its two halves and reassemble.
* `roundFold` — one round's fold of a vector (`loHalf + u • hiHalf`), as in `foldVec`.
* `Tree` — a depth-`k` tree of transcripts: each node carries the two round challenges and two subtrees.
* `Consistent` — the tree's leaves are the witness folded down each challenge path.
* `extract` / `extract_correct` — the extractor recovers the witness exactly, by induction on `k`, using
  `roundExtract_correct` at every node. This is the IPA's special soundness over all rounds, and it is
  binding-free — it takes `Consistent` as a hypothesis. (Deriving that consistency from acceptance is what
  the explicit `Zcash.Snark.CommitmentBinding` later supplies, in `Zcash.Snark.Soundness.Ipa.CommitFold`.)
-/

namespace Zcash.Snark

variable {F : Type*} [Field F]

private theorem two_pow_succ (k : ℕ) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [pow_succ, Nat.mul_two]

/-- The lower half of a length-`2^{k+1}` vector. Generic over the codomain `α`, so it halves both
witness vectors (`α = F`) and generator vectors (`α = G`). -/
def loHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => a ⟨i.val, by have h := i.isLt; have e := two_pow_succ k; omega⟩

/-- The upper half of a length-`2^{k+1}` vector. -/
def hiHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => a ⟨2 ^ k + i.val, by have h := i.isLt; have e := two_pow_succ k; omega⟩

/-- Reassemble a length-`2^{k+1}` vector from its two halves. -/
def append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : Fin (2 ^ (k + 1)) → α :=
  fun i => if h : i.val < 2 ^ k then lo ⟨i.val, h⟩
           else hi ⟨i.val - 2 ^ k, by have h2 := i.isLt; have e := two_pow_succ k; omega⟩

/-- Reassembling the two halves recovers the original vector. -/
theorem append_loHalf_hiHalf {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) :
    append (loHalf a) (hiHalf a) = a := by
  funext i
  rcases lt_or_ge i.val (2 ^ k) with h | h
  · simp only [append, dif_pos h, loHalf]
  · simp only [append, dif_neg (not_lt.mpr h), hiHalf]
    refine congrArg a (Fin.ext ?_)
    show 2 ^ k + (i.val - 2 ^ k) = i.val
    omega

/-- One IPA round folds a length-`2^{k+1}` vector to its lower half plus `u` times its upper half. -/
def roundFold {k : ℕ} (a : Fin (2 ^ (k + 1)) → F) (u : F) : Fin (2 ^ k) → F :=
  foldVec (loHalf a) (hiHalf a) u

/-- A depth-`k` tree of accepting transcripts: each internal node carries the round's two challenges
and the two subtrees (one per challenge); a leaf carries the fully-folded scalar. -/
inductive Tree (F : Type*) : ℕ → Type _ where
  | leaf : F → Tree F 0
  | node {k : ℕ} : F → F → Tree F k → Tree F k → Tree F (k + 1)

/-- The extractor: fold the two sub-extractions back through the round extractor at every node. -/
def extract [Field F] : {k : ℕ} → Tree F k → (Fin (2 ^ k) → F)
  | _, .leaf c => fun _ => c
  | _, .node u₁ u₂ t₁ t₂ =>
      let p := roundExtract (extract t₁) (extract t₂) u₁ u₂
      append p.1 p.2

/-- The tree is consistent with a witness `a`: the leaf is `a` itself (length 1), and each node's
subtrees are consistent with `a` folded by that node's two (distinct) challenges. -/
def Consistent [Field F] : {k : ℕ} → Tree F k → (Fin (2 ^ k) → F) → Prop
  | _, .leaf c, a => c = a 0
  | _, .node u₁ u₂ t₁ t₂, a =>
      u₁ ≠ u₂ ∧ Consistent t₁ (roundFold a u₁) ∧ Consistent t₂ (roundFold a u₂)

/-- Full IPA special soundness. From a tree of accepting transcripts consistent with a witness `a`
(distinct challenges at every node), the extractor recovers exactly `a`. The per-node step is the
2-special-soundness `roundExtract_correct`; composing over the `k` rounds is this induction. -/
theorem extract_correct {k : ℕ} (t : Tree F k) (a : Fin (2 ^ k) → F) (h : Consistent t a) :
    extract t = a := by
  induction t with
  | leaf c => funext i; fin_cases i; exact h
  | node u₁ u₂ t₁ t₂ ih₁ ih₂ =>
      simp only [Consistent] at h
      obtain ⟨hne, h₁, h₂⟩ := h
      have e₁ := ih₁ _ h₁
      have e₂ := ih₂ _ h₂
      simp only [extract, e₁, e₂, roundFold, roundExtract_correct (loHalf a) (hiHalf a) u₁ u₂ hne]
      exact append_loHalf_hiHalf a

end Zcash.Snark
