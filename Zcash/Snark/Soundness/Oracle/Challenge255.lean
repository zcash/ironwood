import Mathlib.Data.Int.CardIntervalMod
import Zcash.Common.Oracle.Hybrid
import Zcash.Snark.Soundness.Oracle.ChallengeUniform

/-!
# Exact bias of the deployed challenge conversion

Halo2's `Challenge255::new` turns one 64-byte squeeze into a field challenge: the digest is read
as a 512-bit integer and reduced modulo `p`.  The security layer prices squeezes as exactly
uniform (`uniformChallenge`); this module prices the gap between that ideal and the deployed
conversion, assuming only that the digest itself is uniform.  Idealizing BLAKE2b as a uniform
512-bit digest stays external (`Oracle/Model.lean`).

Write `2 ^ 512 = challengeQuot * p + challengeRem`.  Reduction sends `challengeQuot + 1` digests
to each of the first `challengeRem` field elements and `challengeQuot` to the rest
(`challenge255_apply`), so an event's probability exceeds its uniform value by at most
`challengeRem * (p - challengeRem) / (p * 2 ^ 512)` — attained by the heavy residues, so the
constant is exact; it is below `2 ^ -260` (`challenge255Bias_le`).  `challenge255_eventBias_le`
states the event form and `challenge255_weightedBias_le` proves the continuation-weighted form.
`challenge255_joint_eventBias_le` composes the latter through a complete adaptive query tree;
`challenge255_badSet_le` runs one squeeze through the event transport.
`challenge255_joint_charge_le_at_2pow123` prices the joint charge at the `2^123` work limit:
an observer visiting at most `Q + (11 + k)` points, with `Q ≤ 2^123` and `k < 33`, pays under
`2^-136` in total, which is the closed number the deployed Action capstone states.
-/

namespace Zcash.Snark

open Zcash.Common

open scoped ENNReal
open Zcash.Arithmetic (scalarFieldOrder card_Fp)

/-- The digest space of one squeeze: `Challenge255` reads a 64-byte digest as a 512-bit integer. -/
def challengeDigestCard : ℕ := 2 ^ 512

instance : NeZero challengeDigestCard :=
  ⟨by unfold challengeDigestCard; exact pow_ne_zero _ (by decide)⟩

/-- Digests landing on each field element before the remainder is spent: `2 ^ 512 / p`. -/
def challengeQuot : ℕ := challengeDigestCard / scalarFieldOrder

/-- The heavy prefix: field elements below `challengeRem` receive one extra digest. -/
def challengeRem : ℕ := challengeDigestCard % scalarFieldOrder

/-- One deployed squeeze under an ideal digest: a uniform 512-bit integer reduced modulo `p`. -/
noncomputable def challenge255 : PMF Fp :=
  PMF.map (fun n : Fin challengeDigestCard => ((n : ℕ) : Fp))
    (PMF.uniformOfFintype (Fin challengeDigestCard))

/-- The exact one-sided distance from uniform: `challengeRem * (p - challengeRem)` over
`p * 2 ^ 512`, about `2 ^ -260.99`. -/
noncomputable def challenge255Bias : ℝ≥0∞ :=
  ((challengeRem * (scalarFieldOrder - challengeRem) : ℕ) : ℝ≥0∞) /
    ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞)

/-- Each fiber of the reduction has `challengeQuot` digests, plus one on the heavy prefix. -/
private theorem challenge255_fiberCard (x : Fp) :
    (Finset.univ.filter fun n : Fin challengeDigestCard => x = ((n : ℕ) : Fp)).card
      = challengeQuot + if x.val < challengeRem then 1 else 0 := by
  have hp : 0 < scalarFieldOrder := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcard :
      (Finset.univ.filter fun n : Fin challengeDigestCard => x = ((n : ℕ) : Fp)).card
        = ((Finset.range challengeDigestCard).filter
            fun m : ℕ => x = ((m : ℕ) : Fp)).card := by
    refine Finset.card_bij (fun n _ => (n : ℕ)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha⟩
    · intro a _ b _ hab
      exact Fin.val_injective hab
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      exact ⟨⟨m, hm.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.2⟩, rfl⟩
  have hpred : ∀ m : ℕ, (x = ((m : ℕ) : Fp)) ↔ m ≡ x.val [MOD scalarFieldOrder] := by
    intro m
    have h1 : (x = ((m : ℕ) : Fp)) ↔ x.val ≡ m [MOD scalarFieldOrder] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact h1.trans ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  rw [hcard, Finset.filter_congr fun m _ => hpred m, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (hr := hp), Nat.mod_eq_of_lt (ZMod.val_lt x)]
  rfl

/-- The law of one converted squeeze: `challengeQuot + 1` weight on the heavy prefix,
`challengeQuot` elsewhere, over the digest count. -/
theorem challenge255_apply (x : Fp) :
    challenge255 x
      = ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞)
          / (challengeDigestCard : ℕ) := by
  classical
  unfold challenge255
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, challenge255_fiberCard x,
    div_eq_mul_inv]

/-- Clearing denominators reduces the one-squeeze event bound to this natural-number inequality. -/
private theorem challenge255_key_le {p q r N s h : ℕ} (hN : N = p * q + r) (hrp : r ≤ p)
    (hhr : h ≤ r) (hhs : h ≤ s) :
    p * (q * s + h) ≤ s * N + r * (p - r) := by
  have hsplit : (p - r) * h + r * h = p * h := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hrp]
  have hcore : p * h ≤ r * s + r * (p - r) :=
    calc p * h = (p - r) * h + r * h := hsplit.symm
      _ ≤ (p - r) * r + r * s :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hhr) (Nat.mul_le_mul_left _ hhs)
      _ = r * s + r * (p - r) := by rw [Nat.mul_comm (p - r) r]; exact Nat.add_comm _ _
  calc p * (q * s + h) = p * q * s + p * h := by ring
    _ ≤ p * q * s + (r * s + r * (p - r)) := Nat.add_le_add_left hcore _
    _ = s * (p * q + r) + r * (p - r) := by ring
    _ = s * N + r * (p - r) := by rw [hN]

/-- **The deployed conversion overshoots uniform by at most the exact reduction bias.**  This is
the `PMFEventBiasLE` premise of `event_measure_le_of_bias` and of the work-factor capstone's bias
conjunct, instantiated at the deployed `Challenge255` law for one squeeze. -/
theorem challenge255_eventBias_le :
    PMFEventBiasLE challenge255 uniformChallenge challenge255Bias := by
  classical
  intro S
  have hS : S = ↑S.toFinset := (Set.coe_toFinset S).symm
  set T : Finset Fp := S.toFinset
  have hp0 : ((scalarFieldOrder : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hN0 : ((challengeDigestCard : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  set h : ℕ := (T.filter fun x : Fp => x.val < challengeRem).card with hh
  have hH_le_r : h ≤ challengeRem := by
    have hle : (T.filter fun x : Fp => x.val < challengeRem).card
        ≤ (Finset.range challengeRem).card := by
      refine Finset.card_le_card_of_injOn ZMod.val ?_ ?_
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro a _ b _ hab
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
    simpa [hh] using hle.trans_eq (Finset.card_range _)
  have hH_le_s : h ≤ T.card := Finset.card_filter_le _ _
  have hsum : ∑ x ∈ T, (challengeQuot + if x.val < challengeRem then 1 else 0)
      = challengeQuot * T.card + h := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, hh,
      Finset.card_filter]
  have lhs_eq : challenge255.toOuterMeasure S
      = ((challengeQuot * T.card + h : ℕ) : ℝ≥0∞) / (challengeDigestCard : ℕ) := by
    rw [hS, PMF.toOuterMeasure_apply_finset,
      Finset.sum_congr rfl fun x _ => challenge255_apply x]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]
  have rhs_eq : uniformChallenge.toOuterMeasure S
      = ((T.card : ℕ) : ℝ≥0∞) / (scalarFieldOrder : ℕ) := by
    rw [hS, uniformChallenge_badSet, card_Fp]
  rw [lhs_eq, rhs_eq]
  unfold challenge255Bias
  have e1 : ((challengeQuot * T.card + h : ℕ) : ℝ≥0∞) / (challengeDigestCard : ℕ)
      = ((scalarFieldOrder * (challengeQuot * T.card + h) : ℕ) : ℝ≥0∞)
          / ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_left _ _ hp0 (ENNReal.natCast_ne_top _)).symm
  have e2 : ((T.card : ℕ) : ℝ≥0∞) / (scalarFieldOrder : ℕ)
      = ((T.card * challengeDigestCard : ℕ) : ℝ≥0∞)
          / ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_right _ _ hN0 (ENNReal.natCast_ne_top _)).symm
  rw [e1, e2, ENNReal.div_add_div_same, ← Nat.cast_add]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have hp : 0 < scalarFieldOrder := Nat.pos_of_ne_zero (NeZero.ne scalarFieldOrder)
  unfold challengeQuot challengeRem at hH_le_r ⊢
  exact challenge255_key_le
    (Nat.div_add_mod challengeDigestCard scalarFieldOrder).symm
    (Nat.mod_lt challengeDigestCard hp).le hH_le_r hH_le_s

/-- The weighted heavy-residue bound used to compose Challenge255 through adaptive continuations. -/
private theorem challenge255_weighted_key_le {p q r N : ℕ} {s h : ℝ≥0∞}
    (hN : N = p * q + r) (hrp : r ≤ p)
    (hhr : h ≤ r) (hhs : h ≤ s) :
    (p : ℝ≥0∞) * ((q : ℝ≥0∞) * s + h) ≤
      s * (N : ℝ≥0∞) + (r : ℝ≥0∞) * ((p - r : ℕ) : ℝ≥0∞) := by
  have hsplit : ((p - r : ℕ) : ℝ≥0∞) * h + (r : ℝ≥0∞) * h =
      (p : ℝ≥0∞) * h := by
    rw [← add_mul, ← Nat.cast_add, Nat.sub_add_cancel hrp]
  have hcore : (p : ℝ≥0∞) * h ≤
      (r : ℝ≥0∞) * s + (r : ℝ≥0∞) * (p - r : ℕ) := by
    calc
      (p : ℝ≥0∞) * h = ((p - r : ℕ) : ℝ≥0∞) * h + (r : ℝ≥0∞) * h := hsplit.symm
      _ ≤ ((p - r : ℕ) : ℝ≥0∞) * r + (r : ℝ≥0∞) * s :=
        add_le_add (mul_le_mul_right hhr _) (mul_le_mul_right hhs _)
      _ = (r : ℝ≥0∞) * s + (r : ℝ≥0∞) * (p - r : ℕ) := by ring
  calc
    (p : ℝ≥0∞) * ((q : ℝ≥0∞) * s + h) =
        (p : ℝ≥0∞) * q * s + (p : ℝ≥0∞) * h := by ring
    _ ≤ (p : ℝ≥0∞) * q * s +
        ((r : ℝ≥0∞) * s + (r : ℝ≥0∞) * (p - r : ℕ)) :=
      add_le_add le_rfl hcore
    _ = s * ((p : ℝ≥0∞) * q + r) + (r : ℝ≥0∞) * (p - r : ℕ) := by ring
    _ = s * (N : ℝ≥0∞) + (r : ℝ≥0∞) * ((p - r : ℕ) : ℝ≥0∞) := by
      rw [hN, Nat.cast_add, Nat.cast_mul]

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 32768 in
/-- The exact Challenge255 one-squeeze bound in the weighted form needed by adaptive
composition.  Unlike the event-only interface, this controls continuation probabilities and can
therefore be applied at each answer-dependent query node. -/
theorem challenge255_weightedBias_le :
    PMFWeightedBiasLE challenge255 uniformChallenge challenge255Bias := by
  classical
  intro weight hweight
  let heavy : Finset Fp := Finset.univ.filter fun x ↦ x.val < challengeRem
  let s : ℝ≥0∞ := ∑ x, weight x
  let h : ℝ≥0∞ := ∑ x ∈ heavy, weight x
  have hcard : heavy.card ≤ challengeRem := by
    have hle : heavy.card ≤ (Finset.range challengeRem).card := by
      refine Finset.card_le_card_of_injOn ZMod.val ?_ ?_
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro a _ b _ hab
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
    simpa using hle
  have hh_le_r : h ≤ (challengeRem : ℝ≥0∞) := by
    calc
      h ≤ ∑ _x ∈ heavy, (1 : ℝ≥0∞) := Finset.sum_le_sum fun x _ ↦ hweight x
      _ = (heavy.card : ℝ≥0∞) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (challengeRem : ℝ≥0∞) := by exact_mod_cast hcard
  have hh_le_s : h ≤ s := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have lhs_eq : ∑ x, challenge255 x * weight x =
      ((challengeQuot : ℝ≥0∞) * s + h) / challengeDigestCard := by
    unfold s h heavy
    calc
      ∑ x, challenge255 x * weight x =
          ∑ x, (((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞) /
            challengeDigestCard) * weight x :=
        Finset.sum_congr rfl fun x _ ↦ by rw [challenge255_apply]
      _ = (∑ x, ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞) *
            weight x) / challengeDigestCard := by
        simp only [div_eq_mul_inv]
        calc
          ∑ x, ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞) *
              (challengeDigestCard : ℝ≥0∞)⁻¹ * weight x =
              ∑ x, (((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) :
                ℝ≥0∞) * weight x) * (challengeDigestCard : ℝ≥0∞)⁻¹ :=
            Finset.sum_congr rfl fun _ _ ↦ by ac_rfl
          _ = (∑ x, ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) :
                ℝ≥0∞) * weight x) * (challengeDigestCard : ℝ≥0∞)⁻¹ :=
            by rw [Finset.sum_mul]
      _ = ((challengeQuot : ℝ≥0∞) * ∑ x, weight x +
            ∑ x ∈ Finset.univ.filter (fun x : Fp ↦ x.val < challengeRem), weight x) /
            challengeDigestCard := by
        apply congrArg (fun z : ℝ≥0∞ ↦ z / challengeDigestCard)
        simp only [Nat.cast_add, add_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
        apply congrArg (fun z : ℝ≥0∞ ↦
          (challengeQuot : ℝ≥0∞) * ∑ x, weight x + z)
        exact Finset.sum_congr rfl fun x _ ↦ by
          by_cases hx : x.val < challengeRem <;> simp [hx]
  have rhs_eq : ∑ x, uniformChallenge x * weight x =
      s / scalarFieldOrder := by
    unfold s uniformChallenge
    simp only [PMF.uniformOfFintype_apply, card_Fp, div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  rw [lhs_eq, rhs_eq]
  unfold challenge255Bias
  have hp0 : ((scalarFieldOrder : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hN0 : ((challengeDigestCard : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  have e1 : ((challengeQuot : ℝ≥0∞) * s + h) / challengeDigestCard =
      ((scalarFieldOrder : ℝ≥0∞) * ((challengeQuot : ℝ≥0∞) * s + h)) /
        ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul]
    exact (ENNReal.mul_div_mul_left _ _ hp0 (ENNReal.natCast_ne_top _)).symm
  have e2 : s / scalarFieldOrder =
      (s * (challengeDigestCard : ℝ≥0∞)) /
        ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul]
    exact (ENNReal.mul_div_mul_right _ _ hN0 (ENNReal.natCast_ne_top _)).symm
  rw [e1, e2, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  have hp : 0 < scalarFieldOrder := Nat.pos_of_ne_zero (NeZero.ne _)
  have hrem : challengeRem ≤ scalarFieldOrder :=
    (Nat.mod_lt challengeDigestCard hp).le
  have hdecomp : challengeDigestCard =
      scalarFieldOrder * challengeQuot + challengeRem :=
    (Nat.div_add_mod challengeDigestCard scalarFieldOrder).symm
  have hkey := challenge255_weighted_key_le
    (p := scalarFieldOrder) (q := challengeQuot) (r := challengeRem)
    (N := challengeDigestCard) (s := s) (h := h)
    hdecomp hrem hh_le_r hh_le_s
  simpa only [Nat.cast_mul, Nat.cast_sub hrem] using hkey

/-- **Joint Challenge255 hybrid.** For a `Q`-bounded adaptive query tree, every final event under
Challenge255 has probability at most its uniform-answer probability plus
`Q * challenge255Bias`; later queries and the event may depend on earlier answers. Apply this to
`OracleComp.dedup [] A` when the original computation can repeat a transcript point. -/
theorem challenge255_joint_eventBias_le {T α : Type*}
    {A : OracleComp T Fp α} {Q : ℕ} (hQ : A.QueryBound Q) :
    PMFEventBiasLE (A.runFreshPMF challenge255) (A.runFreshPMF uniformChallenge)
      (Q * challenge255Bias) :=
  A.runFreshPMF_eventBiasLE challenge255_weightedBias_le hQ

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 8192 in
/-- The exact bias is below `2 ^ -260`: `challengeRem * (p - challengeRem) * 2 ^ 260` fits under
`p * 2 ^ 512`, checked by kernel arithmetic. -/
theorem challenge255Bias_le : challenge255Bias ≤ 1 / 2 ^ 260 := by
  have hnum : challengeRem * (scalarFieldOrder - challengeRem) * 2 ^ 260
      ≤ scalarFieldOrder * challengeDigestCard := by decide
  have hnum' : ((challengeRem * (scalarFieldOrder - challengeRem) : ℕ) : ℝ≥0∞) * 2 ^ 260
      ≤ ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hnum
  have hden0 : ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))
  have hdentop : ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have h2pow0 : ((2 : ℝ≥0∞) ^ 260) ≠ 0 := pow_ne_zero _ (by simp)
  have h2powtop : ((2 : ℝ≥0∞) ^ 260) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  unfold challenge255Bias
  rw [ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdentop), one_div,
    ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl h2pow0) (Or.inl h2powtop)]
  exact hnum'

/-- The joint Challenge255 charge at the `2^123` work limit is below `2^-136`: an observer whose
distinct-query ceiling is `Q + (11 + k)` with `Q ≤ 2^123` and `k < 33` visits fewer than `2^124`
points, and each costs at most the exact bias, which is below `2^-260` (`challenge255Bias_le`).
`Q + (11 + k)` is the envelope one adaptive-statement run certifies
(`ComputedAdaptiveActionStatementFSFamily.relationFinderReads_card_le`): the adversary's `Q`
transcript points plus the verifier's own `11 + k` squeezes. -/
theorem challenge255_joint_charge_le_at_2pow123 {Q k n : ℕ} (hQ : Q ≤ 2 ^ 123) (hk : k < 33)
    (hn : n ≤ Q + (11 + k)) :
    (n : ℝ≥0∞) * challenge255Bias ≤ 1 / 2 ^ 136 := by
  have hn' : n ≤ 2 ^ 124 :=
    calc n ≤ Q + (11 + k) := hn
      _ ≤ 2 ^ 123 + (11 + 32) := Nat.add_le_add hQ (by omega)
      _ ≤ 2 ^ 124 := by norm_num
  have h0 : ((2 : ℝ≥0∞) ^ 260) ≠ 0 := pow_ne_zero _ (by simp)
  have htop : ((2 : ℝ≥0∞) ^ 260) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  calc (n : ℝ≥0∞) * challenge255Bias
      ≤ (2 ^ 124 : ℝ≥0∞) * (1 / 2 ^ 260) :=
        mul_le_mul' (by exact_mod_cast hn') challenge255Bias_le
    _ ≤ 1 / 2 ^ 136 := by
        rw [one_div, one_div, ENNReal.le_inv_iff_mul_le, mul_right_comm, ← pow_add,
          show 124 + 136 = 260 from rfl]
        exact le_of_eq (ENNReal.mul_inv_cancel h0 htop)

/-- One squeeze through the transport theorem: a bad set's probability under the deployed
conversion is its uniform probability plus the exact bias. -/
theorem challenge255_badSet_le (bad : Finset Fp) :
    challenge255.toOuterMeasure ↑bad
      ≤ (bad.card : ℝ≥0∞) / Fintype.card Fp + challenge255Bias :=
  event_measure_le_of_bias challenge255_eventBias_le _
    (le_of_eq (uniformChallenge_badSet bad))

end Zcash.Snark
