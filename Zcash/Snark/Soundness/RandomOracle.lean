import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Core.Field

/-!
# Random-oracle model for the Fiat-Shamir squeeze

`Verifier.FiatShamir` derives challenges through an opaque `squeeze : List (TranscriptElt F G) → F`. The
deployed verifier instantiates it with Blake2b; discharging the Fiat-Shamir assumption (issue #11) models
that hash as a **random oracle** — a function whose answers are uniform and that we can **reprogram** at a
single query (the rewinding primitive the forking argument needs).

This module supplies the random-oracle primitives the forking development is framed with:

* `reprogram` — replace the oracle's answer at one transcript prefix, with `reprogram_self`/`reprogram_ne`.
  Rewinding re-runs the (oracle-deterministic) prover under `reprogram O t c`, diverging exactly at the
  forked query `t`.
* `uniformChallenge` / `uniformChallenge_badSet` — the idealization that a fresh squeeze is uniform over
  `Fp`, hence lands in a finite "bad" set of size `d` with probability `d / p`. This is the Schwartz–Zippel
  exclusion budget (issue #12) and the source of the forking-collision bounds.

## The distributional floor (where mechanization stops)

The forking probability (`Soundness.ForkingProbability`, `Soundness.TreeExtraction`) is stated over the uniform
measure `PMF.uniformOfFintype (Fin k → Fp)` on the IPA round-challenge *vector*. The random-oracle
idealization is what licenses that measure: idealizing the Blake2b squeeze as a random oracle makes each fresh
challenge uniform on `Fp` (`uniformChallenge`) and independent across the `k` distinct round prefixes, so the
vector is uniform on `Fin k → Fp`. `uniformChallenge_badSet` is genuinely consumed — it supplies the `1/p`
`ξ`-randomization budget in `Soundness.Forking` (`blinder_shift_badSet_measure`).

What is **not** mechanized, and is the irreducible floor, is the step from an actual
`deriveChallenges (ofOracle O)` execution to that uniform measure — that Blake2b behaves as a random oracle,
that distinct prefixes squeeze independently, and that rewinding (`reprogram`) resamples a fresh independent
challenge. `reprogram` is the model's rewinding primitive; it is the tool the floor is *phrased* with, not a
mechanized reduction. So every soundness result that consumes the uniform challenge measure is conditional on
this idealization — stated explicitly (e.g. as the `hbridge` of `deployed_forking_soundness_of_bridge`),
rather than proved.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Reprogramming — the rewinding primitive -/

open Classical in
/-- Reprogram a Fiat-Shamir oracle at one transcript prefix `t`: answer `c` there, `O` everywhere else.
Forking reprograms the oracle at the forked round's query and re-runs the prover, producing a transcript
that agrees with the original on the prefix and diverges at `t`. -/
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

/-- The random-oracle idealization of a fresh squeeze: a uniform field challenge over `Fp`. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- Each field element is the squeezed challenge with probability `1/p`. -/
theorem uniformChallenge_apply (a : Fp) :
    uniformChallenge a = (Fintype.card Fp : ℝ≥0∞)⁻¹ := by
  rw [uniformChallenge, PMF.uniformOfFintype_apply]

/-- A fresh squeeze lands in a finite bad set of size `d` with probability `d / p` (`p = card Fp`) — the
Schwartz–Zippel exclusion budget the good-challenge arguments (issue #12) and the forking-collision bounds
draw on. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end Zcash.Snark
