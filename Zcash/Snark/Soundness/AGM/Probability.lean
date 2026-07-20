import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Forking.Probability

/-!
# From relation probability to DL probability

`Soundness.AGM.Adapter` extracts a discrete log when a relation hits a fixed challenge slot. This
module proves the probability loss from choosing that slot uniformly.

## Experiment

Sample scalars `s : ι → F` and present the basis `s i • B`. Independently sample a challenge slot
`c`. The basis does not depend on `c`, and the reduction knows the logs of every slot.

## What is proven

* `hitProb_ge_inv_card`: a uniform slot hits a fixed nontrivial relation with probability at least
  `1 / |ι|`.
* `reduction_advantage_ge`: `Pr[relation] / |ι| ≤ Pr[DL solved]`.
* `relation_prob_le_of_DL`: DL hardness bounds relation finding by `|ι| · bound`.

## Tightness

The fixed-slot construction loses a factor `|ι|` (`2 ^ k + 2` for the deployed augmented basis).
A tighter AGM reduction can randomize the challenge into every slot and lose only `1/|F|`; that is
follow-up work.

## Boundary

The relation finder `A` is a deterministic total function. These are information-theoretic counting
theorems; efficiency is modeled outside Lean. `Soundness.AGM.Capstone` supplies the deployed finder,
and `.ProbabilityVesta` specializes the bounds. Plain-DL hardness, the AGM, and the generator
random-oracle model remain assumptions at those boundaries.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A uniform challenge slot hits a fixed nontrivial relation with probability at least `1 / |ι|`. -/
theorem hitProb_ge_inv_card {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {basis : ι → G} (r : AlgebraicRelationWitness (F := F) basis) :
    (1 : ℝ≥0∞) / Fintype.card ι
      ≤ (PMF.uniformOfFintype ι).toOuterMeasure r.nonzeroCoeffSlots := by
  rw [uniformOfFintype_toOuterMeasure_finset]
  gcongr
  have : 0 < r.nonzeroCoeffSlots.card := Finset.card_pos.mpr r.nonzeroCoeffSlots_nonempty
  exact_mod_cast this

section Reduction
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] (B : G)

/-- The public basis whose slot `i` is `s i • B`. -/
def scalarBasis (s : ι → F) : ι → G := fun i => s i • B

/-- The fixed-slot embedding is available by construction: with `logs := s`, `known` is `rfl`. -/
def scalarEmbedding (s : ι → F) (c : ι) :
    FixedSlotEmbedding (F := F) B (scalarBasis B s) c :=
  { logs := s, known := fun _ _ => rfl }

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-- Relation-finding event: on the presented basis, `A` returns a (nontrivial) relation. -/
noncomputable def relSet : Finset (ι → F) :=
  Finset.univ.filter (fun s => (A (scalarBasis B s)).isSome)

/-- Scalar vectors and challenge slots where `A` returns a relation that hits the slot. -/
noncomputable def succSet : Finset ((ι → F) × ι) :=
  Finset.univ.filter (fun p => ∃ r, A (scalarBasis B p.1) = some r ∧ r.coeffs p.2 ≠ 0)

omit [Nonempty ι] in
/-- Every relation-producing scalar vector has at least one challenge slot that solves DL. -/
theorem relSet_card_le_succSet_card :
    (relSet B A).card ≤ (succSet B A).card := by
  have hsub : relSet B A ⊆ Finset.image Prod.fst (succSet B A) := by
    intro s hs
    simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨c, hc⟩ := r.nonzeroCoeffSlots_nonempty
    rw [Finset.mem_image]
    refine ⟨(s, c), ?_, rfl⟩
    simp only [succSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, hr, (r.mem_nonzeroCoeffSlots c).mp hc⟩
  calc (relSet B A).card
        ≤ (Finset.image Prod.fst (succSet B A)).card := Finset.card_le_card hsub
    _ ≤ (succSet B A).card := Finset.card_image_le

/-- The DL-solving probability is at least the relation probability divided by `|ι|`. -/
theorem reduction_advantage_ge :
    (1 : ℝ≥0∞) / Fintype.card ι
        * (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((ι → F) × ι)).toOuterMeasure (succSet B A) := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    Fintype.card_prod]
  have hcard : ((relSet B A).card : ℝ≥0∞) ≤ (succSet B A).card := by
    exact_mod_cast relSet_card_le_succSet_card B A
  have hn0 : (Fintype.card (ι → F) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn_top : (Fintype.card (ι → F) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [one_div, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl hn0) (Or.inl hn_top)]
  calc (Fintype.card ι : ℝ≥0∞)⁻¹ * ((relSet B A).card * (Fintype.card (ι → F) : ℝ≥0∞)⁻¹)
        = (relSet B A).card
            * ((Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (Fintype.card ι : ℝ≥0∞)⁻¹) := by ac_rfl
    _ ≤ (succSet B A).card
            * ((Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (Fintype.card ι : ℝ≥0∞)⁻¹) := by gcongr

/-- The reduction's probability of solving the embedded challenge is at most `bound`.

This is not yet textbook DL hardness because the experiment samples all slot logs. Use
`TextbookDLAdvantageLE` for the standard DL game. -/
def DLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype ((ι → F) × ι)).toOuterMeasure (succSet B A) ≤ bound

/-- Bound relation finding by `|ι| · bound` from a bound on the embedded DL game. -/
theorem relation_prob_le_of_DL {bound : ℝ≥0∞} (h : DLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A) ≤ Fintype.card ι * bound := by
  have hm0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm_top : (Fintype.card ι : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hstep : (1 : ℝ≥0∞) / Fintype.card ι
      * (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A) ≤ bound :=
    le_trans (reduction_advantage_ge B A) h
  have hmul : (Fintype.card ι : ℝ≥0∞)
      * ((1 : ℝ≥0∞) / Fintype.card ι
          * (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A))
      ≤ Fintype.card ι * bound := by gcongr
  rwa [one_div, ← mul_assoc, ENNReal.mul_inv_cancel hm0 hm_top, one_mul] at hmul

/-! ### Reduction to textbook single-generator discrete log

The textbook game supplies `x • B`. The reduction places it in a uniform slot and generates the
other slots. The map `(x, c, s') ↦ (Function.update s' c x, c)` shows that this game has the same
success probability as the embedded game.
-/

/-- Winning coins for the textbook DL reduction: secret `x`, challenge slot `c`, and other slot logs
`s'`. -/
noncomputable def winSet : Finset (F × ι × (ι → F)) :=
  Finset.univ.filter (fun t => (Function.update t.2.2 t.2.1 t.1, t.2.1) ∈ succSet B A)

omit [Nonempty ι] in
/-- The winning-coins set has `|F|` elements for each element of `succSet`. -/
theorem winSet_card :
    (winSet B A).card = (succSet B A).card * Fintype.card F := by
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ => ((Function.update t.2.2 t.2.1 t.1, t.2.1), t.2.2 t.2.1))
    (fun p _ => (p.1.1 p.1.2, p.1.2, Function.update p.1.1 p.1.2 p.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨x, c, s'⟩ ht
    simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact ht
  case hj =>
    rintro ⟨⟨s, c⟩, t⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
    simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_idem, Function.update_eq_self]
    exact hp
  case left =>
    rintro ⟨x, c, s'⟩ _
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  case right =>
    rintro ⟨⟨s, c⟩, t⟩ _
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

/-- The textbook reduction and embedded game have the same success probability. -/
theorem textbook_winProb_eq_succProb :
    (PMF.uniformOfFintype (F × ι × (ι → F))).toOuterMeasure (winSet B A)
      = (PMF.uniformOfFintype ((ι → F) × ι)).toOuterMeasure (succSet B A) := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset, winSet_card]
  have hcard : Fintype.card (F × ι × (ι → F))
      = Fintype.card F * Fintype.card ((ι → F) × ι) := by
    simp only [Fintype.card_prod]; ring
  rw [hcard]
  push_cast
  rw [mul_comm ((succSet B A).card : ℝ≥0∞) (Fintype.card F : ℝ≥0∞),
    ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- The reduction built from `A` wins the textbook single-generator DL game with probability at most
`bound`. -/
def TextbookDLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × ι × (ι → F))).toOuterMeasure (winSet B A) ≤ bound

/-- Under textbook DL hardness, relation finding has probability at most `|ι| · bound`. -/
theorem relation_prob_le_of_textbookDL {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A) ≤ Fintype.card ι * bound := by
  refine relation_prob_le_of_DL B A ?_
  show (PMF.uniformOfFintype ((ι → F) × ι)).toOuterMeasure (succSet B A) ≤ bound
  rw [← textbook_winProb_eq_succProb]
  exact h

end Reduction

end Zcash.Snark
