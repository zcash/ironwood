import Zcash.Snark.Soundness.AGM
import Zcash.Snark.Soundness.ForkingProbability

/-!
# The AGM probability wrapper: relation-finder ⇒ discrete-log solver

`Soundness.AGM` proves the *deterministic* fixed-slot extractor (`discreteLogOfBasis_of_relation`)
and the *finite* hit accounting (`challengeHitCount_pos`, `challengeHitCount_le_total`). This module
supplies the probabilistic step those set up, closing the "random-slot / probability wrapper" that
`Soundness.AGM` previously stated only in prose.

## The experiment (perfect simulation by construction)

Sample the whole scalar vector `s : ι → F` uniformly and present the public basis
`scalarBasis B s i = s i • B`; independently sample a uniform challenge slot `c : ι`. Because the
basis is a function of `s` alone, it is independent of `c` **by construction** — no group
re-randomization lemma is needed — and the fixed-slot embedding holds with `logs := s`
(`scalarEmbedding`, definitionally). The presented discrete-log instance is `(B, scalarBasis B s c)`
with valid preimage `s c`.

## What is proven

* `hitProb_ge_inv_card` — a uniform challenge slot hits any fixed nontrivial relation with
  probability ≥ `1 / |ι|` (the caveat's claim, now a theorem; reuses
  `uniformOfFintype_toOuterMeasure_finset` from `ForkingProbability` and `challengeHitCount_pos`).
* `reduction_advantage_ge` — the advantage-preserving reduction
  `Pr[relation found] / |ι| ≤ Pr[reduction outputs a valid discrete log]`, over the uniform product
  `(ι → F) × ι`. Pure finite counting: every relation-finding `s` contributes at least one hitting
  slot (`relSet_card_le_succSet_card`).
* `relation_prob_le_of_DL` — binding from discrete-log hardness: if no reduction solves the discrete
  log of the challenge slot with probability more than `bound` (`DLAdvantageLE`), the algebraic
  adversary finds a relation with probability at most `|ι| · bound`.

## Residual (genuine assumptions, not prose)

The adversary is the *abstract* algebraic relation-finder
`A : (b : ι → G) → Option (AlgebraicRelationWitness b)`. What remains outside this file:
(i) discrete-log hardness itself (the `DLAdvantageLE` hypothesis — an assumption by definition);
(ii) the AGM idealization; (iii) connecting the deployed Ironwood prover's outputs (representations
through the IPA verifier equation) to this abstract `A` — issue #15's other half. None of these is
the probability accounting, which is now formalized here.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Over a uniformly sampled challenge slot, a fixed nontrivial relation is hit — its coefficient at
that slot is nonzero — with probability at least `1 / |ι|`. This is the finite hit accounting of
`Soundness.AGM` (`challengeHitCount_pos`) turned into the probability statement, via the uniform-event
identity `uniformOfFintype_toOuterMeasure_finset`. -/
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

/-- The public basis presented to the adversary: slot `i` holds `s i • B`. Sampling `s` uniformly and
designating a uniform slot as the challenge makes the challenge slot independent of the basis, so no
separate perfect-simulation argument is required. -/
def scalarBasis (s : ι → F) : ι → G := fun i => s i • B

/-- The fixed-slot embedding is available by construction: with `logs := s`, `known` is `rfl`. -/
def scalarEmbedding (s : ι → F) (c : ι) :
    FixedSlotEmbedding (F := F) B (scalarBasis B s) c :=
  { logs := s, known := fun _ _ => rfl }

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-- Relation-finding event: on the presented basis, `A` returns a (nontrivial) relation. -/
noncomputable def relSet : Finset (ι → F) :=
  Finset.univ.filter (fun s => (A (scalarBasis B s)).isSome)

/-- Discrete-log-solving event over (scalars, challenge slot): `A`'s returned relation has a nonzero
coefficient at the challenge slot, so the deterministic extractor recovers that slot's discrete log. -/
noncomputable def succSet : Finset ((ι → F) × ι) :=
  Finset.univ.filter (fun p => ∃ r, A (scalarBasis B p.1) = some r ∧ r.coeffs p.2 ≠ 0)

omit [Nonempty ι] in
/-- Every relation-finding scalar vector contributes at least one solving (scalars, slot) pair: the
count of solving pairs dominates the count of relation-finding vectors. -/
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

/-- **Advantage-preserving reduction.** Over the uniform product `(ι → F) × ι`, the probability that
the reduction extracts a genuine discrete log is at least `1/|ι|` times the probability the algebraic
adversary finds a relation. Pure finite counting on top of `relSet_card_le_succSet_card`. -/
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

/-- Discrete-log hardness at `B`, in the form the reduction consumes: the reduction's probability of
extracting a genuine discrete log (over `B`) of the challenge slot's basis element is at most `bound`.
`succSet` is exactly the event "the returned relation hits the challenge slot", on which the
deterministic extractor outputs a `w` with `w • B = (scalarBasis B s) c` — a valid discrete log of the
challenge point. Bounding this probability is the discrete-log assumption. -/
def DLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype ((ι → F) × ι)).toOuterMeasure (succSet B A) ≤ bound

/-- **Binding from discrete-log hardness.** If no reduction solves the discrete log of the challenge
slot with probability more than `bound`, then the algebraic adversary finds a relation with
probability at most `|ι| · bound`. Contrapositive of `reduction_advantage_ge`: a relation-finder that
beats `|ι| · bound` would give a discrete-log solver beating `bound`. -/
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

end Reduction

end Zcash.Snark
