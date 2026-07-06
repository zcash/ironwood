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
* `exists_accepting_good_challenge` / `_quotient` — **the production step.** An accept event whose
  uniform measure beats the budget contains an accepting challenge *outside* the bad set. This is
  what the `_xgood` capstone rungs consume: the good challenge is *produced* from the accept
  measure, so `hgood` disappears from those signatures — the x-site analogue of the forking floors
  (`extractable_of_prob`, `exists_injective_accepting_of_measure`).

## Scope

The measure is `uniformChallenge`, the random-oracle idealization of one fresh squeeze
(`Zcash.Snark.Soundness.RandomOracle` — the accepted uniformity axiom, carried in the statements).
The Schwartz–Zippel argument needs the difference polynomial pinned before the challenge is sampled,
and the deployed schedule provides exactly that: `deriveChallenges` squeezes `x` from a transcript
that has already absorbed the advice column commitments and the quotient `h` pieces
(`adviceCommitments_mem_preXTranscript`/`hPieces_mem_preXTranscript`, sealed by
`deriveChallenges_x_eq` in `Soundness.TranscriptOrdering`; instance data enters through the `init`
prefix and the fixed columns through the VK), so `C` is a function of the prefix the squeeze hashes
— pinned across the `x`-reprogramming runs (`Soundness.Forking.reprogramX`) and independent of which
rewound batch decoded it, up to the relation branch (`decodedCols_eq_or_relation`,
`Soundness.Main`). Like the other per-hypothesis exclusions (`z ≠ 0` and the `ξ`-recovery, `1/p`
each), this `d / p` budget is stated per use site — the `_xgood` rungs compose it into their own
accept-measure hypothesis, while the cross-budget composition stays with the "uncomposed budgets"
note in `Zcash.Snark.Soundness.RandomOracle`. Capstones whose `hgood` is quantified over a family
(one instance per opening of the pinned statement) draw the budget once per instantiated site; the
terminal decoded capstones take a single canonical difference polynomial.
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

/-! ## Producing a good accepting challenge from an accept measure

The lemmas above *price* the exclusion; the lemmas below *spend* it. An accept event whose uniform
measure beats `m / p` has more than `m` accepting challenges, so if the bad set has at most `m`
elements some accepting challenge avoids it — the good-challenge condition is produced from the
accept measure rather than assumed. This is the x-site instance of the codebase-wide
counting floors: `extractable_of_prob` forces the round-forking tree, and
`exists_injective_accepting_of_measure` forces the `x₄` rewound family, from the same
measure-beats-count shape. The `_xgood` capstone rungs (`Zcash.Snark.Soundness.Main`,
`Zcash.Snark.Soundness.Vesta`) consume these, dropping the `hgood` hypothesis. -/

/-- **The pigeonhole core.** If the accept event's uniform measure beats `m / p` and the bad set has
at most `m` elements, some accepting challenge avoids the bad set: the accept set has more than `m`
elements, so it cannot be contained in a set of at most `m`. -/
theorem exists_accepting_avoiding_of_measure {acc : Fp → Prop} [DecidablePred acc]
    {bad : Finset Fp} {m : ℕ} (hcard : bad.card ≤ m)
    (hprob : (m : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ bad := by
  have hcount : bad.card < (Finset.univ.filter acc).card := by
    have hm : m < (Finset.univ.filter acc).card := by
      by_contra hle
      have hmono : uniformChallenge.toOuterMeasure (Finset.univ.filter acc)
          ≤ (m : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
        rw [uniformChallenge_badSet]
        exact ENNReal.div_le_div_right (by exact_mod_cast Nat.le_of_not_lt hle) _
      exact absurd hprob (not_lt.mpr hmono)
    exact lt_of_le_of_lt hcard hm
  obtain ⟨xv, hmem, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcount
  exact ⟨xv, (Finset.mem_filter.mp hmem).2, hnot⟩

/-- **Good-challenge production at a Schwartz–Zippel site.** An accept measure beating
`natDegree C / p` yields an accepting challenge outside `szBadSet C` — the capstones' `hgood`,
derived from the accept measure rather than assumed. -/
theorem exists_accepting_good_challenge {acc : Fp → Prop} [DecidablePred acc] (C : Polynomial Fp)
    (hprob : (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ szBadSet C :=
  exists_accepting_avoiding_of_measure (szBadSet_card_le C) hprob

/-- Good-challenge production at the vanishing-check site, with the degree explicit: an accept
measure beating `max (deg numerator) (deg h + n) / p` yields an accepting challenge that is good for
the quotient difference. The threshold is the caller-computable `d` of `szBadSet_quotient_card_le`,
so instantiations need not evaluate the difference polynomial's degree. -/
theorem exists_accepting_good_challenge_quotient {acc : Fp → Prop} [DecidablePred acc]
    (numerator h : Polynomial Fp) (n : ℕ)
    (hprob : ((max numerator.natDegree (h.natDegree + n) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ szBadSet (numerator - h * (X ^ n - 1)) :=
  exists_accepting_avoiding_of_measure (szBadSet_quotient_card_le numerator h n) hprob

end Zcash.Snark
