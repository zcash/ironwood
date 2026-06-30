import Mathlib

/-!
# Multi-round tree extraction (the Fiat-Shamir forking compounding)

This module establishes, by a counting/averaging induction over the `d` rounds, that if the prover's
accepting set of challenge vectors is large enough — more than the threshold count `kerr` — then a full
`(3,…,3)`-tree of accepting challenge vectors exists (`Extractable`). It is self-contained: the multi-round
existence *is* the `kerr` count below, not an iteration of the per-round cubic bound in
`Soundness.ForkingProbability`.

`kerr (card α) d` is a tree-existence threshold as a count out of `(card α)^d`; as a fraction it is `3d/N`
(`N = card α`), a **conservative upper bound** on that threshold (the tight value is `1 − (1 − 3/N)^d`). The
`3` is the price of requiring **nonzero** challenges — the IPA's `u⁻¹` fold needs each `uⱼ ≠ 0` — not vanilla
3-special-soundness (error `≈ 2d/N`). This is the *tree-existence* threshold, not the end-to-end Fiat-Shamir
knowledge error (which additionally carries the random-oracle query-count factor). `Extractable` holds
whenever the accept probability exceeds `3d/N`.

This is the abstract combinatorial core; the deployed verifier instantiates `acc` with its own accept
predicate, and the per-node `(g,U,W)` decomposition is recovered separately (special-soundness / Vandermonde).
-/

namespace Zcash.Snark

variable {α : Type*}

/-- A conservative tree-existence-threshold count for the nonzero-challenge `(3,…,3)`-tree over a size-`N`
challenge set and `d` rounds: `kerr N (d+1) = 3·N^d + N·kerr N d`, `kerr N 0 = 0`. As a fraction of `N^d` it
is `3d/N` — an upper bound; the tight threshold is `1 − (1 − 3/N)^d`. -/
def kerr (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => 3 * N ^ d + N * kerr N d

/-- A `(3,…,3)`-tree of accepting challenge vectors exists for `acc`: at each of the `d` rounds, three
pairwise-distinct nonzero challenges, each extending to an accepting subtree. The forking output's challenge
skeleton — what rewinding must produce, here shown to exist from a large enough accepting set. -/
def Extractable [Zero α] : {d : ℕ} → ((Fin d → α) → Prop) → Prop
  | 0, acc => acc Fin.elim0
  | _ + 1, acc => ∃ u₁ u₂ u₃ : α, u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
      Extractable (fun rest => acc (Fin.cons u₁ rest)) ∧
      Extractable (fun rest => acc (Fin.cons u₂ rest)) ∧
      Extractable (fun rest => acc (Fin.cons u₃ rest))

/-- The accepting count splits over the first challenge: the number of accepting `(d+1)`-vectors is the sum,
over each first challenge `u`, of the accepting `d`-vectors extending `u`. -/
theorem card_filter_eq_sum_slice [Fintype α] [DecidableEq α] {d : ℕ}
    (acc : (Fin (d + 1) → α) → Prop) [DecidablePred acc] :
    (Finset.univ.filter acc).card
      = ∑ u : α, (Finset.univ.filter (fun rest => acc (Fin.cons u rest))).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => α)).sum_comp (fun i => if acc i then 1 else 0),
    Fintype.sum_prod_type]
  rfl

/-- **Multi-round tree extraction.** If the prover's accepting set of `d`-round challenge vectors exceeds the
knowledge-error count `kerr N d` (`N = card α`), a full `(3,…,3)`-tree of accepting challenge vectors exists.
By induction on rounds: at each round the accepting count splits over the first challenge (`card_filter_eq_sum_slice`),
and an averaging argument forces at least four first challenges whose continuations are themselves above the
`d`-round threshold — three of them nonzero, recursed by the induction hypothesis. This is the deterministic
core of the Fiat-Shamir forking: the rewinding produces this tree whenever the accept probability beats the
knowledge error `3d/N`. -/
theorem extractable_of_kerr_lt [Fintype α] [DecidableEq α] [Zero α] :
    ∀ {d : ℕ} (acc : (Fin d → α) → Prop) [DecidablePred acc],
      kerr (Fintype.card α) d < (Finset.univ.filter acc).card → Extractable acc
  | 0, acc, _, h => by
      simp only [kerr] at h
      rw [Finset.card_pos] at h
      obtain ⟨x, hx⟩ := h
      rw [Finset.mem_filter] at hx
      show acc Fin.elim0
      rw [Subsingleton.elim Fin.elim0 x]
      exact hx.2
  | d + 1, acc, _, h => by
      classical
      have hslice : (Finset.univ.filter acc).card
          = ∑ u : α, (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card :=
        card_filter_eq_sum_slice acc
      have hNd : ∀ u : α, (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card
          ≤ Fintype.card α ^ d := fun u =>
        le_trans (Finset.card_filter_le _ _)
          (by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin])
      have hgood4 : 4 ≤ (Finset.univ.filter (fun u : α =>
          kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card := by
        by_contra hcon
        push_neg at hcon
        have hgc : (Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card ≤ 3 := by
          omega
        have hbc : (Finset.univ.filter (fun u : α => ¬ kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card
            ≤ Fintype.card α :=
          le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
        have h1 := Finset.sum_le_sum (s := Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card))
            (f := fun u => (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)
            (g := fun _ => Fintype.card α ^ d) (fun u _ => hNd u)
        have h2 := Finset.sum_le_sum (s := Finset.univ.filter (fun u : α => ¬ kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card))
            (f := fun u => (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)
            (g := fun _ => kerr (Fintype.card α) d)
            (fun u hu => not_lt.mp (Finset.mem_filter.mp hu).2)
        rw [Finset.sum_const, smul_eq_mul] at h1 h2
        have hb : (Finset.univ.filter acc).card
            ≤ 3 * Fintype.card α ^ d + Fintype.card α * kerr (Fintype.card α) d := by
          rw [hslice, ← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun u => kerr (Fintype.card α) d
              < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)]
          calc _ ≤ _ + _ := add_le_add h1 h2
            _ ≤ 3 * Fintype.card α ^ d + Fintype.card α * kerr (Fintype.card α) d := by
                gcongr
        simp only [kerr] at h
        omega
      set g := Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
          < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card) with hg
      have hg4 : 4 ≤ g.card := hgood4
      have hg0 : 2 < (g.erase 0).card := by
        by_cases h0 : (0 : α) ∈ g
        · have he := Finset.card_erase_add_one h0
          omega
        · rw [Finset.erase_eq_of_notMem h0]; omega
      obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hg0
      have key : ∀ u, u ∈ g.erase 0 → u ≠ 0 ∧ kerr (Fintype.card α) d
          < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card := by
        intro u hu
        refine ⟨Finset.ne_of_mem_erase hu, ?_⟩
        have hm := Finset.mem_of_mem_erase hu
        rw [hg, Finset.mem_filter] at hm
        exact hm.2
      exact ⟨u₁, u₂, u₃, h12, h13, h23, (key u₁ hu₁).1, (key u₂ hu₂).1, (key u₃ hu₃).1,
        extractable_of_kerr_lt _ (key u₁ hu₁).2,
        extractable_of_kerr_lt _ (key u₂ hu₂).2,
        extractable_of_kerr_lt _ (key u₃ hu₃).2⟩

end Zcash.Snark
