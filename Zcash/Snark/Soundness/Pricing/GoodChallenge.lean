import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Constraint.Constraints
import Zcash.Snark.Soundness.Oracle.Model

/-!
# Schwartz–Zippel good-challenge exclusions from challenge uniformity

The constraint layer assumes the vanishing-check challenge avoids the roots of the constraint
difference `C = numerator − h · (Xⁿ − 1)` (`hgood`). This module derives that from challenge
uniformity: a fresh uniform squeeze lands in the bad set with probability at most `natDegree C / p`
(`uniformChallenge_szBadSet`), so an accept event whose measure beats the budget contains an
accepting challenge outside it (`exists_accepting_good_challenge`) — `hgood` is *produced* from the
accept measure, not assumed.

## Scope

The measure is `uniformChallenge`, the random-oracle idealization of one fresh squeeze
(`FiatShamir.Oracle`). The argument needs the difference polynomial pinned before the challenge is
sampled, and the deployed schedule provides exactly that: `x` is squeezed from a transcript that has
already absorbed the advice commitments and the quotient pieces (sealed by `deriveChallenges_x_eq`,
`FiatShamir.Ordering`). The several `d / p` exclusions compose subadditively
(`uniformChallenge_szBadSet_union`).
-/

namespace Zcash.Snark

open CompPoly.CPolynomial
open scoped ENNReal

/-- **The Schwartz–Zippel exclusion budget, derived from challenge uniformity.** A fresh uniform
squeeze lands in the bad set of a use site with probability at most `natDegree C / p`: the
good-challenge hypotheses (`hgood`, the shape `x ∉ szBadSet C`) exclude a set of uniform
random-oracle measure at most `d / p`. -/
theorem uniformChallenge_szBadSet (C : CPoly) :
    uniformChallenge.toOuterMeasure (szBadSet C)
      ≤ (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast szBadSet_card_le C

/-- **The good-challenge condition holds with overwhelming probability.** Under the random-oracle
uniform challenge, the event `x ∉ szBadSet C` — exactly the `hgood` hypothesis shape, by
`not_mem_szBadSet` — has probability at least `1 − natDegree C / p`. This is the derived form of the
good-challenge assumption: what the soundness capstones take per instance, this bounds in measure. -/
theorem uniformChallenge_szGoodSet (C : CPoly) :
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
theorem uniformChallenge_quotient_szBadSet (numerator h : CPoly) (n : ℕ) :
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
theorem quotientCheck_badSet_measure (numerator h : CPoly) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    uniformChallenge.toOuterMeasure (Finset.univ.filter fun x => quotientCheck numerator h n x)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [quotientCheck_filter_eq_szBadSet numerator h n hne]
  exact uniformChallenge_szBadSet _

/-! ## Producing a good accepting challenge from an accept measure

The lemmas above *price* the exclusion; the lemmas below *spend* it. An accept event whose uniform
measure beats `m / p` has more than `m` accepting challenges, so if the bad set has at most `m`
elements some accepting challenge avoids it — the good-challenge condition is produced from the
accept measure rather than assumed. -/

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
theorem exists_accepting_good_challenge {acc : Fp → Prop} [DecidablePred acc] (C : CPoly)
    (hprob : (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ szBadSet C :=
  exists_accepting_avoiding_of_measure (szBadSet_card_le C) hprob

/-- Good-challenge production at the vanishing-check site, with the degree explicit: an accept
measure beating `max (deg numerator) (deg h + n) / p` yields an accepting challenge that is good for
the quotient difference. The threshold is the caller-computable `d` of `szBadSet_quotient_card_le`,
so instantiations need not evaluate the difference polynomial's degree. -/
theorem exists_accepting_good_challenge_quotient {acc : Fp → Prop} [DecidablePred acc]
    (numerator h : CPoly) (n : ℕ)
    (hprob : ((max numerator.natDegree (h.natDegree + n) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ szBadSet (numerator - h * (X ^ n - 1)) :=
  exists_accepting_avoiding_of_measure (szBadSet_quotient_card_le numerator h n) hprob

/-! ## Composing the per-site exclusion budgets into one bound

The lemmas above price each Schwartz–Zippel / point exclusion separately (`d / p`, `1 / p`). The two
below combine any finite collection of `Fp`-challenge exclusions into a single subadditive bound, so
a run that avoids *all* of them is priced once. This lemma covers exclusions over one fresh `Fp`
squeeze — the `z ≠ 0` and `ξ`-recovery singletons, the vanishing-check Schwartz–Zippel set, and any
further point exclusions. Other transcript surfaces and adaptive query loss are accounted for by
their composition modules. -/

open scoped ENNReal in
/-- **The composed exclusion budget.** A uniform challenge avoids *both* the Schwartz–Zippel bad
set of the constraint difference `C` *and* a finite set `extra` of further excluded points, except
on a set of measure at most `(natDegree C + |extra|) / p`. `extra` holds the `z = 0` and
`ξ`-recovery singletons and any per-hypothesis point exclusions.

This is the several `d / p` and `1 / p` budgets over one fresh `Fp` squeeze, combined by
subadditivity: a run avoiding all of them at once is priced once. Any collection of point
exclusions composes, since `extra` is an arbitrary finite set. Challenge surfaces over other
squeeze domains are priced separately. -/
theorem uniformChallenge_szBadSet_union (C : CPoly) (extra : Finset Fp) :
    uniformChallenge.toOuterMeasure ((szBadSet C ∪ extra : Finset Fp))
      ≤ ((C.natDegree + extra.card : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (szBadSet_card_le C) _)

/-! ## Named additive-factor exclusions

`ChallengePricing.escape_measure_le` prices the same vanishing-factor event as a set.
The circuit bridge also needs a finite, reusable set that can be carried as a
good-challenge hypothesis, so retain this equivalent indexed presentation. -/

/-- Challenge values that make at least one member of a finite family
`offset i + challenge` vanish. -/
def additiveZeroBadSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (offset : ι → Fp) : Finset Fp :=
  Finset.univ.image fun i => -offset i

/-- Membership in the additive bad set is exactly the existence of a vanishing factor. -/
theorem mem_additiveZeroBadSet_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (offset : ι → Fp) (challenge : Fp) :
    challenge ∈ additiveZeroBadSet offset ↔
      ∃ i, offset i + challenge = 0 := by
  simp [additiveZeroBadSet, neg_eq_iff_add_eq_zero]

/-- One challenge value per index is the complete additive-factor exclusion budget. -/
theorem additiveZeroBadSet_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (offset : ι → Fp) :
    (additiveZeroBadSet offset).card ≤ Fintype.card ι := by
  simpa [additiveZeroBadSet] using
    (Finset.card_image_le :
      (Finset.univ.image fun i : ι => -offset i).card ≤ (Finset.univ : Finset ι).card)

/-- A fresh field challenge makes one of a finite family of additive factors vanish with
probability at most `|ι| / |Fp|`. -/
theorem uniformChallenge_additiveZeroBadSet
    {ι : Type*} [Fintype ι] [DecidableEq ι] (offset : ι → Fp) :
    uniformChallenge.toOuterMeasure (additiveZeroBadSet offset)
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast additiveZeroBadSet_card_le offset

end Zcash.Snark
