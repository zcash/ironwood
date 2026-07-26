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
* `relation_prob_le_of_tightDL`: the randomized-basis reduction bounds relation finding by
  `bound + 1 / |F|`.

## Tightness

The fixed-slot construction loses a factor `|ι|` (`2 ^ k + 2` for the deployed augmented basis)
because it must guess, before the adversary runs, which slot the returned relation will hit.

`## A tighter reduction` below removes the guess. The reduction presents `α i • B + t i • X` for
uniform `α, t`, so the challenge sits in *every* slot at once; extraction fails only when the
returned coefficients annihilate the hiding vector `t`, which — `t` being independent of the
adversary's view — happens with probability at most `1 / |F|`. The loss is therefore an additive
`1 / |F|` rather than a multiplicative `|ι|`.

Both reductions are proved here against the same textbook single-generator DL game
(`TextbookDLAdvantageLE`, `TightDLAdvantageLE`). The deployed endpoints still route through the
fixed-slot bound; migrating them to the tight one is a separate change.

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

/-! ## A tighter reduction: randomized basis, additive `1/|F|` loss

The fixed-slot reduction plants the challenge in one slot chosen before the adversary runs, and
throws away every run whose relation misses that slot — a factor `|ι|`. Presenting
`α i • B + t i • X` instead plants the challenge in all slots simultaneously. A relation with
coefficients `c` then yields

  `(∑ i, c i · α i) • B + (∑ i, c i · t i) • X = 0`,

so the log of `X` is recoverable whenever the *mask combination* `∑ i, c i · t i` is nonzero. The
adversary sees only `α + x · t`, which for fixed `x` is uniform and independent of `t`; a nonzero
`c` is annihilated by exactly a `1/|F|` fraction of hiding vectors.
-/

section TightReduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] (B : G)

/-- The public basis presented by the randomized reduction: slot `i` is `α i • B + t i • X`. -/
def randomizedBasis (X : G) (α t : ι → F) : ι → G := fun i => α i • B + t i • X

/-- The pairing of a relation's coefficients with the hiding vector. Extraction succeeds exactly
when it is nonzero. -/
def maskCombination (coeffs t : ι → F) : F := ∑ i, coeffs i * t i

/-- With `X = x • B` the randomized basis is the plain scalar basis at logs `α + x · t`: the
reduction presents exactly the distribution the honest experiment does. -/
theorem randomizedBasis_smul (x : F) (α t : ι → F) :
    randomizedBasis B (x • B) α t = scalarBasis B (fun i => α i + x * t i) := by
  funext i
  show α i • B + t i • (x • B) = (α i + x * t i) • B
  rw [smul_smul, add_smul, mul_comm (t i) x]

/-- Recover the discrete log of the challenge `X` over `B` from a relation over the randomized
basis whose mask combination is nonzero.

No slot is fixed in advance: every returned relation extracts unless it lands in the annihilator
of the hiding vector. -/
def discreteLogOfRandomizedRelation (X : G) (α t : ι → F)
    (r : AlgebraicRelationWitness (F := F) (randomizedBasis B X α t))
    (hmask : maskCombination r.coeffs t ≠ 0) :
    DiscreteLogWitness (F := F) B X := by
  refine ⟨(maskCombination r.coeffs t)⁻¹ * (-(maskCombination r.coeffs α)), ?_⟩
  have hsplit : representationEval (randomizedBasis B X α t) r.coeffs
      = maskCombination r.coeffs α • B + maskCombination r.coeffs t • X := by
    rw [representationEval, maskCombination, maskCombination, Finset.sum_smul, Finset.sum_smul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    show r.coeffs i • (α i • B + t i • X)
      = (r.coeffs i * α i) • B + (r.coeffs i * t i) • X
    rw [smul_add, smul_smul, smul_smul]
  have hzero : maskCombination r.coeffs t • X + maskCombination r.coeffs α • B = 0 := by
    rw [add_comm, ← hsplit]
    exact r.relation
  have hmul : maskCombination r.coeffs t • X = (-(maskCombination r.coeffs α)) • B := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hzero
  have hX : X = ((maskCombination r.coeffs t)⁻¹ * (-(maskCombination r.coeffs α))) • B := by
    have h := congrArg (fun Y : G => (maskCombination r.coeffs t)⁻¹ • Y) hmul
    simp only [smul_smul, inv_mul_cancel₀ hmask, one_smul] at h
    exact h
  exact hX.symm

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-- The coefficient vector the finder returns on the presented basis, `0` when it returns
nothing. -/
noncomputable def returnedCoeffs (s : ι → F) : ι → F :=
  match A (scalarBasis B s) with
  | some r => r.coeffs
  | none => 0

/-- On a relation-producing scalar vector, the returned coefficients are nontrivial. -/
theorem returnedCoeffs_ne_zero {s : ι → F} (hs : (A (scalarBasis B s)).isSome) :
    returnedCoeffs B A s ≠ 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have h : returnedCoeffs B A s = r.coeffs := by simp only [returnedCoeffs, hr]
  rw [h]
  exact r.nontrivial

/-- A slot at which the returned relation has a nonzero coefficient.

This is chosen *after* the adversary runs and is used only to count annihilating hiding vectors;
the reduction itself plants no slot. -/
noncomputable def pivotSlot (s : ι → F) : ι :=
  if h : ∃ i, returnedCoeffs B A s i ≠ 0 then h.choose else Classical.arbitrary ι

/-- The pivot slot really carries a nonzero coefficient. -/
theorem returnedCoeffs_pivotSlot {s : ι → F} (hs : returnedCoeffs B A s ≠ 0) :
    returnedCoeffs B A s (pivotSlot B A s) ≠ 0 := by
  have hex : ∃ i, returnedCoeffs B A s i ≠ 0 := by
    by_contra h
    exact hs (funext fun i => not_not.mp (not_exists.mp h i))
  rw [pivotSlot, dif_pos hex]
  exact hex.choose_spec

/-- Scalar vectors and hiding vectors on which the randomized reduction extracts. -/
noncomputable def tightSuccSet : Finset ((ι → F) × (ι → F)) :=
  Finset.univ.filter
    (fun p => (A (scalarBasis B p.1)).isSome ∧ maskCombination (returnedCoeffs B A p.1) p.2 ≠ 0)

/-- A nonzero coefficient vector is annihilated by at most a `1/|F|` fraction of hiding vectors:
fixing the entries off a nonzero slot determines the entry at it.

This is the whole probabilistic content of the tight reduction, stated for one fixed coefficient
vector. `relProb_le_tightSuccProb_add_inv` reruns the same injection with the pivot slot varying
per scalar vector, so it does not call this lemma; the standalone form is here because it is the
claim a reader should check. -/
theorem card_maskZero_mul_card_le {c : ι → F} (hc : c ≠ 0) :
    (Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)).card * Fintype.card F
      ≤ Fintype.card (ι → F) := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    exact hc (funext fun i => not_not.mp (not_exists.mp h i))
  have hinj : Set.InjOn (fun q : (ι → F) × F => Function.update q.1 j q.2)
      ↑((Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)) ×ˢ
        (Finset.univ : Finset F)) := by
    rintro ⟨t₁, u₁⟩ h₁ ⟨t₂, u₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at h₁ h₂
    have hupd : Function.update t₁ j u₁ = Function.update t₂ j u₂ := heq
    have hu : u₁ = u₂ := by
      have h := congrFun hupd j
      simpa using h
    have hoff : ∀ i, i ≠ j → t₁ i = t₂ i := by
      intro i hi
      have h := congrFun hupd i
      simpa [Function.update_apply, hi] using h
    have hsum : ∑ i ∈ Finset.univ.erase j, c i * t₁ i
        = ∑ i ∈ Finset.univ.erase j, c i * t₂ i :=
      Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.mem_erase.mp hi).1]
    have e₁ : ∑ i ∈ Finset.univ.erase j, c i * t₁ i + c j * t₁ j = 0 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact h₁
    have e₂ : ∑ i ∈ Finset.univ.erase j, c i * t₂ i + c j * t₂ j = 0 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact h₂
    have hcj : c j * t₁ j = c j * t₂ j := by
      have hchain := e₁.trans e₂.symm
      rw [hsum] at hchain
      exact add_left_cancel hchain
    have ht : t₁ = t₂ := by
      funext i
      by_cases hi : i = j
      · subst hi
        exact mul_left_cancel₀ hj hcj
      · exact hoff i hi
    simp [ht, hu]
  calc (Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)).card * Fintype.card F
      = ((Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)) ×ˢ
          (Finset.univ : Finset F)).card := by
        rw [Finset.card_product, Finset.card_univ]
    _ ≤ (Finset.univ : Finset (ι → F)).card :=
        Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
    _ = Fintype.card (ι → F) := Finset.card_univ

/-- The relation event exceeds the randomized reduction's success event by at most `1 / |F|`. -/
theorem relProb_le_tightSuccProb_add_inv :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((ι → F) × (ι → F))).toOuterMeasure (tightSuccSet B A)
        + 1 / Fintype.card F := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  have hN0 : (Fintype.card (ι → F) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card (ι → F) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hF0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hFt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNN0 : ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) ≠ 0 := mul_ne_zero hN0 hN0
  have hNNt : ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) ≠ ⊤ :=
    ENNReal.mul_ne_top hNt hNt
  -- the success set sits inside the relation-producing rectangle
  have hsub : tightSuccSet B A ⊆ relSet B A ×ˢ (Finset.univ : Finset (ι → F)) := by
    intro p hp
    simp only [tightSuccSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, relSet, Finset.mem_filter,
      true_and]
    exact hp.1
  set Miss := (relSet B A ×ˢ (Finset.univ : Finset (ι → F))) \ tightSuccSet B A with hMissdef
  have hMissmem : ∀ p ∈ Miss, (A (scalarBasis B p.1)).isSome ∧
      maskCombination (returnedCoeffs B A p.1) p.2 = 0 := by
    intro p hp
    rw [hMissdef, Finset.mem_sdiff, Finset.mem_product] at hp
    obtain ⟨⟨hrel, -⟩, hout⟩ := hp
    simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and] at hrel
    refine ⟨hrel, ?_⟩
    by_contra hne
    exact hout (by
      simp only [tightSuccSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hrel, hne⟩)
  -- the rectangle splits into successes and annihilations
  have hsum : Miss.card + (tightSuccSet B A).card
      = (relSet B A).card * Fintype.card (ι → F) := by
    rw [hMissdef, Finset.card_sdiff_add_card_eq_card hsub, Finset.card_product, Finset.card_univ]
  -- annihilations are a `1/|F|` slice of the rectangle
  have hmiss : Miss.card * Fintype.card F
      ≤ (relSet B A).card * Fintype.card (ι → F) := by
    have hmap : ∀ q ∈ Miss ×ˢ (Finset.univ : Finset F),
        ((q.1.1, Function.update q.1.2 (pivotSlot B A q.1.1) q.2) : (ι → F) × (ι → F))
          ∈ relSet B A ×ˢ (Finset.univ : Finset (ι → F)) := by
      intro q hq
      rw [Finset.mem_product] at hq
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hMissmem q.1 hq.1).1
    have hinj : Set.InjOn
        (fun q : ((ι → F) × (ι → F)) × F =>
          ((q.1.1, Function.update q.1.2 (pivotSlot B A q.1.1) q.2) : (ι → F) × (ι → F)))
        ↑(Miss ×ˢ (Finset.univ : Finset F)) := by
      rintro ⟨⟨s₁, t₁⟩, u₁⟩ h₁ ⟨⟨s₂, t₂⟩, u₂⟩ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at h₁ h₂
      have hs : s₁ = s₂ := congrArg Prod.fst heq
      subst hs
      have hc₁ := hMissmem (s₁, t₁) h₁
      have hc₂ := hMissmem (s₁, t₂) h₂
      have hcne : returnedCoeffs B A s₁ ≠ 0 := returnedCoeffs_ne_zero B A hc₁.1
      have hj : returnedCoeffs B A s₁ (pivotSlot B A s₁) ≠ 0 :=
        returnedCoeffs_pivotSlot B A hcne
      have hupd : Function.update t₁ (pivotSlot B A s₁) u₁
          = Function.update t₂ (pivotSlot B A s₁) u₂ := congrArg Prod.snd heq
      have hu : u₁ = u₂ := by
        have h := congrFun hupd (pivotSlot B A s₁)
        simpa using h
      have hoff : ∀ i, i ≠ pivotSlot B A s₁ → t₁ i = t₂ i := by
        intro i hi
        have h := congrFun hupd i
        simpa [Function.update_apply, hi] using h
      have hsum' : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₁ i
          = ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₂ i :=
        Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.mem_erase.mp hi).1]
      have e₁ : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₁ i
          + returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₁ (pivotSlot B A s₁) = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (pivotSlot B A s₁))]
        exact hc₁.2
      have e₂ : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₂ i
          + returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₂ (pivotSlot B A s₁) = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (pivotSlot B A s₁))]
        exact hc₂.2
      have hcj : returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₁ (pivotSlot B A s₁)
          = returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₂ (pivotSlot B A s₁) := by
        have hchain := e₁.trans e₂.symm
        rw [hsum'] at hchain
        exact add_left_cancel hchain
      have ht : t₁ = t₂ := by
        funext i
        by_cases hi : i = pivotSlot B A s₁
        · subst hi
          exact mul_left_cancel₀ hj hcj
        · exact hoff i hi
      simp [ht, hu]
    calc Miss.card * Fintype.card F
        = (Miss ×ˢ (Finset.univ : Finset F)).card := by
          rw [Finset.card_product, Finset.card_univ]
      _ ≤ (relSet B A ×ˢ (Finset.univ : Finset (ι → F))).card :=
          Finset.card_le_card_of_injOn _ hmap hinj
      _ = (relSet B A).card * Fintype.card (ι → F) := by
          rw [Finset.card_product, Finset.card_univ]
  -- move to `ℝ≥0∞`
  have hsumE : (Miss.card : ℝ≥0∞) + (tightSuccSet B A).card
      = ((relSet B A).card : ℝ≥0∞) * Fintype.card (ι → F) := by exact_mod_cast hsum
  have hmissE : (Miss.card : ℝ≥0∞) * Fintype.card F
      ≤ (Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F) := by
    have hR : (relSet B A).card ≤ Fintype.card (ι → F) := by
      simpa using Finset.card_le_card (Finset.subset_univ (relSet B A))
    have h1 : (Miss.card : ℝ≥0∞) * Fintype.card F
        ≤ ((relSet B A).card : ℝ≥0∞) * Fintype.card (ι → F) := by exact_mod_cast hmiss
    refine h1.trans ?_
    gcongr
    exact_mod_cast hR
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    Fintype.card_prod, Nat.cast_mul]
  have hstep1 : ((relSet B A).card : ℝ≥0∞) / Fintype.card (ι → F)
      = ((tightSuccSet B A).card : ℝ≥0∞)
          / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
        + (Miss.card : ℝ≥0∞) / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) := by
    rw [ENNReal.div_add_div_same]
    have hnum : ((tightSuccSet B A).card : ℝ≥0∞) + Miss.card
        = (Fintype.card (ι → F) : ℝ≥0∞) * (relSet B A).card := by
      rw [add_comm, hsumE, mul_comm]
    rw [hnum]
    exact (ENNReal.mul_div_mul_left _ _ hN0 hNt).symm
  have hstep2 : (Miss.card : ℝ≥0∞)
        / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
      ≤ 1 / Fintype.card F := by
    have hle : (Miss.card : ℝ≥0∞)
        ≤ ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) / Fintype.card F := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
      exact hmissE
    calc (Miss.card : ℝ≥0∞) / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
        ≤ (((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) / Fintype.card F)
            / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) :=
          ENNReal.div_le_div_right hle _
      _ = 1 / Fintype.card F := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_div,
            mul_comm ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
              ((Fintype.card F : ℝ≥0∞)⁻¹),
            mul_assoc, ENNReal.mul_inv_cancel hNN0 hNNt, mul_one]
  rw [hstep1]
  exact add_le_add_left hstep2 _

/-- Winning coins for the tight reduction against the textbook DL game: the secret `x`, the base
randomization `α`, and the hiding vector `t`. The presented basis is `scalarBasis B (α + x · t)`,
which is uniform and independent of `t`. -/
noncomputable def tightWinSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter
    (fun w => ((fun i => w.2.1 i + w.1 * w.2.2 i), w.2.2) ∈ tightSuccSet B A)

/-- The winning-coins set has `|F|` elements for each element of `tightSuccSet`: for each fixed
secret, `(α, t) ↦ (α + x · t, t)` is a bijection. -/
theorem tightWinSet_card :
    (tightWinSet B A).card = (tightSuccSet B A).card * Fintype.card F := by
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  refine Finset.card_bij'
    (fun w _ => (((fun i => w.2.1 i + w.1 * w.2.2 i), w.2.2), w.1))
    (fun p _ => (p.2, (fun i => p.1.1 i - p.2 * p.1.2 i), p.1.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨x, α, t⟩ hw
    simp only [tightWinSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact hw
  case hj =>
    rintro ⟨⟨s, t⟩, x⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
    simp only [tightWinSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun i => (s i - x * t i) + x * t i) = s := by funext i; ring
    simpa only [hfun] using hp
  case left =>
    rintro ⟨x, α, t⟩ _
    have hfun : (fun i => (α i + x * t i) - x * t i) = α := by funext i; ring
    simp only [hfun]
  case right =>
    rintro ⟨⟨s, t⟩, x⟩ _
    have hfun : (fun i => (s i - x * t i) + x * t i) = s := by funext i; ring
    simp only [hfun]

/-- The tight reduction and the randomized experiment have the same success probability. -/
theorem tight_winProb_eq_succProb :
    (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (tightWinSet B A)
      = (PMF.uniformOfFintype ((ι → F) × (ι → F))).toOuterMeasure (tightSuccSet B A) := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    tightWinSet_card]
  have hcard : Fintype.card (F × (ι → F) × (ι → F))
      = Fintype.card F * Fintype.card ((ι → F) × (ι → F)) := by
    simp only [Fintype.card_prod]; ring
  rw [hcard]
  push_cast
  rw [mul_comm ((tightSuccSet B A).card : ℝ≥0∞) (Fintype.card F : ℝ≥0∞),
    ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- The randomized reduction built from `A` wins the textbook single-generator DL game with
probability at most `bound`. -/
def TightDLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (tightWinSet B A) ≤ bound

/-- Under textbook DL hardness, relation finding has probability at most `bound + 1 / |F|`.

This is the tight counterpart of `relation_prob_le_of_textbookDL`, whose fixed-slot reduction pays
a multiplicative `|ι|` instead. -/
theorem relation_prob_le_of_tightDL {bound : ℝ≥0∞} (h : TightDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card F := by
  refine le_trans (relProb_le_tightSuccProb_add_inv B A) ?_
  gcongr
  rw [← tight_winProb_eq_succProb]
  exact h

end TightReduction

end Zcash.Snark
