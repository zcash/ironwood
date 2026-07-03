import Mathlib
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.RandomOracle

/-!
# Schwartz–Zippel good-challenge exclusions from challenge uniformity

The constraint layer consumes good-challenge hypotheses (`hgood`): the vanishing-check challenge
avoids the Schwartz–Zippel bad set `szBadSet C` — the roots of the constraint difference
`C = numerator − h · (Xⁿ − 1)` (`Zcash.Snark.Soundness.Constraints`). This module derives those
exclusions from challenge uniformity under the random-oracle model (issue #12), so they are budgeted
consequences of the one distributional idealization rather than unexamined assumptions:

* `uniformChallenge_szBadSet` — **the exclusion budget.** A fresh uniform squeeze lands in a use
  site's bad set with probability at most `natDegree C / p`: root counting (`szBadSet_card_le`)
  composed with the uniform-measure identity (`uniformChallenge_badSet`).
* `uniformChallenge_szGoodSet` — **the good-challenge condition holds with overwhelming
  probability**: the complement event `x ∉ szBadSet C` (exactly the `hgood` shape, by
  `not_mem_szBadSet`) has probability at least `1 − natDegree C / p` — for the deployed degrees
  against `p ≈ 2²⁵⁴`, overwhelming.
* `uniformChallenge_quotient_szBadSet` — the vanishing-check site with its degree made explicit:
  the budget is `max (deg numerator) (deg h + n) / p` (via `szBadSet_quotient_card_le`).
* `quotientCheck_badSet_measure` — the acceptance-side reading (the random-oracle-measure twin of
  `quotientCheck_sound`): a committed-polynomial set that *violates* the constraint identity passes
  the verifier's point check on a set of challenges of measure at most `natDegree C / p`.

## Scope

The measure is `uniformChallenge`, the random-oracle idealization of one fresh squeeze
(`Zcash.Snark.Soundness.RandomOracle` — the accepted uniformity axiom, carried in the statements).
The Schwartz–Zippel argument needs the difference polynomial pinned before the challenge is sampled,
and the deployed schedule provides exactly that: `deriveChallenges` squeezes `x` from a transcript
that has already absorbed the column and quotient commitments, so `C` is a function of the prefix
the squeeze hashes. Like the other per-hypothesis exclusions (`z ≠ 0` and the `ξ`-recovery, `1/p`
each), this `d / p` budget is stated per use site and not yet composed into one end-to-end bound —
see the "uncomposed budgets" note in `Zcash.Snark.Soundness.RandomOracle`. Capstones whose `hgood`
is quantified over a family (one instance per opening of the pinned statement) draw the budget once
per instantiated site; the terminal decoded capstones take a single canonical difference polynomial.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal

/-- **The Schwartz–Zippel exclusion budget, derived from challenge uniformity.** A fresh uniform
squeeze lands in the bad set of a use site with probability at most `natDegree C / p`: the
good-challenge hypotheses (`hgood`, the shape `x ∉ szBadSet C`) exclude a set of uniform
random-oracle measure at most `d / p`. -/
theorem uniformChallenge_szBadSet (C : Polynomial Fp) :
    uniformChallenge.toOuterMeasure (szBadSet C)
      ≤ (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast szBadSet_card_le C

/-- **The good-challenge condition holds with overwhelming probability.** Under the random-oracle
uniform challenge, the event `x ∉ szBadSet C` — exactly the `hgood` hypothesis shape, by
`not_mem_szBadSet` — has probability at least `1 − natDegree C / p`. This is the derived form of the
good-challenge assumption: what the soundness capstones take per instance, this bounds in measure. -/
theorem uniformChallenge_szGoodSet (C : Polynomial Fp) :
    1 - (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      ≤ uniformChallenge.toOuterMeasure ((szBadSet C)ᶜ : Finset Fp) := by
  rw [uniformChallenge_badSet, tsub_le_iff_right, ENNReal.div_add_div_same]
  have hp0 : (Fintype.card Fp : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Fintype.card Fp : ℝ≥0∞)
      ≤ ((szBadSet C)ᶜ.card : ℝ≥0∞) + (C.natDegree : ℝ≥0∞) := by
    have h1 : Fintype.card Fp ≤ (szBadSet C)ᶜ.card + C.natDegree := by
      have h2 : (szBadSet C).card + (szBadSet C)ᶜ.card = Fintype.card Fp :=
        Finset.card_add_card_compl _
      have h3 := szBadSet_card_le C
      omega
    exact_mod_cast h1
  calc (1 : ℝ≥0∞) = (Fintype.card Fp : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) :=
        (ENNReal.div_self hp0 (ENNReal.natCast_ne_top _)).symm
    _ ≤ _ := ENNReal.div_le_div_right hcard _

/-- The vanishing-check site with its degree explicit: the bad set of the constraint difference
`numerator − h · (Xⁿ − 1)` has uniform measure at most `max (deg numerator) (deg h + n) / p` — the
concrete `d / p` budget for the quotient identity's Schwartz–Zippel use. -/
theorem uniformChallenge_quotient_szBadSet (numerator h : Polynomial Fp) (n : ℕ) :
    uniformChallenge.toOuterMeasure (szBadSet (numerator - h * (X ^ n - 1)))
      ≤ (max numerator.natDegree (h.natDegree + n) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  refine le_trans (Nat.cast_le.mpr (szBadSet_quotient_card_le numerator h n)) (le_of_eq ?_)
  rw [Nat.mono_cast.map_max, Nat.cast_add]

/-- The acceptance-side reading — the random-oracle-measure twin of `quotientCheck_sound`: a
committed-polynomial set that violates the constraint identity passes the verifier's point check
only on the bad set (`quotientCheck_filter_eq_szBadSet`), a set of challenges of uniform measure at
most `natDegree (numerator − h · (Xⁿ − 1)) / p`. -/
theorem quotientCheck_badSet_measure (numerator h : Polynomial Fp) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    uniformChallenge.toOuterMeasure (Finset.univ.filter fun x => quotientCheck numerator h n x)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [quotientCheck_filter_eq_szBadSet numerator h n hne]
  exact uniformChallenge_szBadSet _

end Zcash.Snark
