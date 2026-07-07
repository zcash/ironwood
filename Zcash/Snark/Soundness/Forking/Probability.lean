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

end Zcash.Snark
