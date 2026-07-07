import Mathlib
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree

/-!
# The forking lemma's probabilistic core (random-oracle model)

The deterministic tree assembly (`Soundness.Forking.Assembly.forkAccept_to_acceptV`) turns the *forking
output* — three accepting continuations per IPA round at distinct nonzero challenges — into the deployed
accept predicate. What is *not* deterministic is producing that output: a single non-interactive proof gives
one challenge path, not the three the 3-special-soundness tree needs. The honest statement is probabilistic
(a rewinding/forking reduction): if the prover makes the verifier accept with probability `ε` over a random
oracle, beating the knowledge error forces the full `(3,…,3)` forking tree to exist.

This module supplies that probabilistic step over the uniform challenge of the random-oracle model
(`Forking.Oracle.uniformChallenge`):

* `uniformOfFintype_toOuterMeasure_finset` — a finite event has uniform probability `|E| / |domain|`
  (the general form of `uniformChallenge_badSet`): under the random-oracle model the challenge is uniform, so
  any "good"/"bad" set's probability is its size over the field size.
* `extractable_of_prob` — **the multi-round forking lemma.** If, over the random-oracle-uniform challenge
  *vector* `Fin d → α`, the prover's accept probability exceeds the knowledge error
  `kerr (card α) d / (card α)^d` (`= 3d/N` as a fraction), a full `(3,…,3)` forking tree of accepting challenge
  vectors exists (`Extractable`). It composes the uniform-measure identity with the deterministic counting core
  `Soundness.Forking.Tree.extractable_of_kerr_lt`: beating the error in *probability* is beating the
  knowledge-error *count*, which forces the tree.

The tree existence goes **directly** through the `kerr` count — it does not iterate a per-round `ε³` bound, so
the catastrophic `ε^{3ᵈ}` composition never arises. What stays the random-oracle floor is the
prover-as-oracle-function model that pins each round's accepting set (and the adaptive RO-query loss), plus the
idealization that Blake2b is a random oracle.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {α : Type*}

/-- A finite event `E` has uniform probability `|E| / |α|` (the general form of `uniformChallenge_badSet`:
the per-round challenge is uniform under the random-oracle model, so any "bad"/"good" set's probability is
its size over the field size). -/
theorem uniformOfFintype_toOuterMeasure_finset [Fintype α] [Nonempty α] (E : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure E = (E.card : ℝ≥0∞) / Fintype.card α := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **The multi-round forking lemma (probabilistic form).** If, over the random-oracle-uniform challenge
*vector* `Fin d → α`, the prover's accept probability exceeds the knowledge error
`kerr (card α) d / (card α)^d` (`= 3d/N` as a fraction), then a full `(3,…,3)` forking tree of accepting
challenge vectors exists (`Extractable acc`). Composing the uniform-measure identity
(`uniformOfFintype_toOuterMeasure_finset`) with the deterministic counting core (`extractable_of_kerr_lt`):
beating the error in *probability* is beating the knowledge-error *count*, which forces the tree. This is the
`acc ⇒ frk` reduction across all `d` rounds — what the random oracle's uniformity buys, once Blake2b is
modeled as that oracle. The remaining floor is the prover-as-oracle-function model pinning `acc` to the
deployed verifier, and Blake2b-as-random-oracle itself. -/
theorem extractable_of_prob [Fintype α] [DecidableEq α] [Zero α] [Nonempty α] {d : ℕ}
    (acc : (Fin d → α) → Prop) [DecidablePred acc]
    (h : (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α)
       < (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)) :
    Extractable acc := by
  apply extractable_of_kerr_lt
  by_contra hle
  push_neg at hle
  have hmono : (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)
      ≤ (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α) := by
    rw [uniformOfFintype_toOuterMeasure_finset]
    gcongr
  exact absurd h (not_lt.mpr hmono)

/-- **The single-squeeze forking count.** If one accepting challenge is in hand and the accept event's
uniform measure beats `n / |α|`, then `n + 1` pairwise-distinct accepting challenges exist, with the given
one in slot `0`. The one-challenge analogue of `extractable_of_prob` (there the event is a whole round
*vector* and beating `kerr` forces the `(3,…,3)` tree; here beating `n/|α|` forces `n` rewound accepting
values beside the current one) — the counting core of the multiopen `x₄` rewinding
(`Soundness.Multiopen.Deployed`). -/
theorem exists_injective_accepting_of_measure [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {acc : α → Prop} [DecidablePred acc] {x₀ : α} (hx₀ : acc x₀)
    (hprob : (n : ℝ≥0∞) / Fintype.card α
      < (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)) :
    ∃ ξ : Fin (n + 1) → α, Function.Injective ξ ∧ ξ 0 = x₀ ∧ ∀ r, acc (ξ r) := by
  have hcard : n < (Finset.univ.filter acc).card := by
    by_contra hle
    push_neg at hle
    have hmono : (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)
        ≤ (n : ℝ≥0∞) / Fintype.card α := by
      rw [uniformOfFintype_toOuterMeasure_finset]
      exact ENNReal.div_le_div_right (by exact_mod_cast hle) _
    exact absurd hprob (not_lt.mpr hmono)
  have hx₀mem : x₀ ∈ Finset.univ.filter acc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩
  have herase : n ≤ ((Finset.univ.filter acc).erase x₀).card := by
    rw [Finset.card_erase_of_mem hx₀mem]
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq herase
  let f : Fin n → α := fun i => (S.equivFin.symm (Fin.cast hScard.symm i) : α)
  have hfinj : Function.Injective f := fun i j hij => by
    have h1 := S.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.val_injective (by simpa using congrArg Fin.val h1)
  have hfS : ∀ i, f i ∈ S := fun i => (S.equivFin.symm (Fin.cast hScard.symm i)).2
  refine ⟨Fin.cons x₀ f, ?_, rfl, ?_⟩
  · refine (Fin.cons_injective_iff).mpr ⟨?_, hfinj⟩
    rintro ⟨i, hfi⟩
    exact Finset.ne_of_mem_erase (hS (hfS i)) hfi
  · intro r
    cases r using Fin.cases with
    | zero => simpa using hx₀
    | succ i =>
        have hmem := hS (hfS i)
        have := Finset.mem_of_mem_erase hmem
        simpa using (Finset.mem_filter.mp this).2

end Zcash.Snark
