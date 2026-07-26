import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Core.Field

/-!
# Random-oracle model for Fiat–Shamir

`Verifier.FiatShamir` derives challenges with an abstract `squeeze`. The deployed verifier uses
Blake2b. The soundness proof models it as a random function with uniform answers that can be changed
at one query.

This module supplies the random-oracle primitives the forking development is framed with:

* `reprogram` changes the answer at one transcript prefix. Rewinding reruns the prover with that
  changed answer.
* `uniformChallenge` and `uniformChallenge_badSet` model a fresh field challenge and its probability
  of landing in a finite bad set.

## Challenge-vector distribution

The forking proof uses the uniform distribution on IPA challenge vectors.
`Soundness.Forking.Rewind.roChallenges_ipaRound_uniform` derives that distribution for a fixed proof
from one assumption:

> **Random oracle.** The Blake2b squeeze is idealized as a *uniform random function* `O` over its query domain.

Each round reads `O` at a distinct transcript prefix, so the answers are independent and uniform.
This also assumes that transcript encoding is injective and that halo2's `Challenge255 → Fp`
conversion is exactly uniform.

Thus the challenge distribution is proved inside the random-oracle model, while the model itself
remains an assumption about Blake2b.

## The `Challenge255 → Fp` conversion bias

`uniformChallenge` is *defined* as `PMF.uniformOfFintype Fp`. The deployed conversion is not exactly
uniform: halo2 squeezes a fixed-width byte string and reduces it modulo `p`, and reduction of a
uniform `w`-bit integer modulo `p` leaves each residue with probability `⌊2^w/p⌋/2^w` or
`⌈2^w/p⌉/2^w` rather than `1/p`. Summed over `Fp` this is a total-variation distance of at most
`|Fp| / 2^w` per squeeze, and a `q`-squeeze run loses at most `q · |Fp| / 2^w` by the usual hybrid
over squeezes — the *same* `q` that `Soundness.Forking.Adversary.OracleComp` already charges query
loss against.

`badSet_measure_le_of_bias` below is where that term attaches: it carries any bad-set bound proved
against `uniformChallenge` over to a biased conversion law at an additive `ε`. Instantiating `ε`
requires pinning `w` for the deployed transcript, which is a fact about halo2's transcript code and
not about this development — it belongs on the same side of the boundary as Blake2b itself, and is
recorded in the trust boundary rather than proved here. What this module no longer does is call the
bias "negligible" without saying what it is or where it would be charged.

## Remaining adversary model

The querying-adversary experiment this module's floor used to defer is now present:
`Soundness.Forking.Adversary.OracleComp` models a bounded-query adversary (`OracleComp`,
`QueryBound`), `Soundness.Forking.Adversary.Algebraic` runs the recursive extractor against it, and
`ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL` and `.binding_under_DL` price extraction
failure from the adversary's own advantage. Query loss is charged explicitly — `(Q + k) · (3/p)` for
the extractor's escape slice plus `(Q + 1) · (1/p)` for the adaptive `z = 0` slice — rather than
assumed away. The Fiat–Shamir layer also produces `DeployedAlgebraicForkingInstance` values and
relates its acceptance event to the relation event, which was the gap tracked by issue #15; that
issue's scope (binding ⟶ plain DL in the AGM) is discharged by `Soundness.AGM.Adapter` and
`.Probability`.

What is left of the floor is therefore *not* "there is no adversary experiment". It is:

* **Efficiency.** The endpoints are gated on `ComputedAlgebraicFSFamily.ReductionEfficient R`.
  `reductionEfficient_exponential` discharges it unconditionally at `(2·|F|+1)^k`;
  `reductionEfficient_of_forkSpread` discharges it at the polynomial `(6/δ)^k` but only under
  `FamilyForkSpread`. PPT-ness of the adversary family itself is external to Lean.
* **The idealizations.** Blake2b as a random function, the conversion bias above, the AGM, plain-DL
  hardness, and the generator random-oracle model.
* **The legacy fixed-proof rungs.** `legacy_deployed_forking_soundness` and the
  `legacy_orchard_verifier_vesta_*` ladder still take `hprob` as a hypothesis: they measure one
  proof over all challenge vectors, not a querying attack. The computed endpoints above supersede
  them; the ladder is retained because `orchard_verifier_vesta_forking_constraint_deployed_x4`
  still routes through it.

`uniformChallenge_badSet` is used directly for the `1/p` blinding budget.

One scope note, part of that floor and not of the derived uniformity: the `Fp`-squeeze exclusions —
the Schwartz–Zippel `d / p`, the `z ≠ 0` and `ξ`-recovery `1 / p` singletons, and any further point
exclusions — are combined into one subadditive bound by
`Soundness.GoodChallenge.uniformChallenge_szBadSet_union`, whereas the `kerr` tree count lives over
the round-*vector* domain and is charged separately.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Reprogramming — the rewinding primitive -/

open Classical in
/-- Change the oracle's answer at `t` to `c`, leaving all other answers unchanged. -/
noncomputable def reprogram (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    List (TranscriptElt F G) → F :=
  fun t' => if t' = t then c else O t'

@[simp] theorem reprogram_self (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    reprogram O t c t = c := by
  simp [reprogram]

theorem reprogram_ne {O : List (TranscriptElt F G) → F} {t t' : List (TranscriptElt F G)} {c : F}
    (h : t' ≠ t) : reprogram O t c t' = O t' := by
  simp [reprogram, h]

/-! ## The uniform-challenge idealization -/

/-- A fresh random-oracle squeeze, modeled as uniform over `Fp`.

Halo2's real `Challenge255 → Fp` conversion is a modular reduction of a fixed-width byte string and
so is only within total-variation distance `|Fp| / 2^w` of this law, for the conversion width `w`.
`badSet_measure_le_of_bias` charges that deviation; no bound in this development silently assumes
it away. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A uniform challenge lands in `bad` with probability `|bad| / |Fp|`. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Charge the deployed conversion's reduction bias against a bad-set budget.

If the real squeeze law `D` overshoots `uniformChallenge` by at most `ε` on every event — the
`ε = |Fp| / 2^w` of the module doc, for a `w`-bit conversion — then every bad-set bound proved in
the uniform model holds for `D` with `ε` added. The hypothesis is the assumption; the point of
stating it is that the term now has a name and a home instead of living in the word "negligible". -/
theorem badSet_measure_le_of_bias {D : PMF Fp} {ε : ℝ≥0∞}
    (hbias : ∀ S : Set Fp, D.toOuterMeasure S ≤ uniformChallenge.toOuterMeasure S + ε)
    (bad : Finset Fp) :
    D.toOuterMeasure bad ≤ (bad.card : ℝ≥0∞) / Fintype.card Fp + ε := by
  refine le_trans (hbias bad) (le_of_eq ?_)
  rw [uniformChallenge_badSet]

end Zcash.Snark
