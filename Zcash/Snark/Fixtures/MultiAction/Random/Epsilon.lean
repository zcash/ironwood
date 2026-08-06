import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Zcash.Snark.Fixtures.MultiAction.Random.Negative
import Zcash.Snark.Fingerprint.Rational.Capstone
import Zcash.Snark.Fingerprint.Epsilon

/-!
# ε at the random multi-action capture

The quantified match, instantiated at this capture's verifying key: the walk capstone
(`assembleCoeffFamily`) packages every coefficient of the assembled MSM as a polynomial
numerator over the enumerated challenge-only denominators, and the generic ε theorem
(`competing_coefficient_family_agreement_le`) then prices a competing family's agreement at a
uniformly random sample-space point. This module discharges the capstone's verifying-key
hypotheses at the captured key (`native_decide`), pins the degree and coordinate literals, and
states the headline with numerals:

> any competing numerator family of total degree ≤ 16456 over the walk's denominators that
> differs anywhere from Lean's agrees with the assembled MSM at a uniform point with
> probability at most `(16456 + 2071) / p = 18527 / p`, `p = scalarFieldOrder ≈ 2²⁵⁴`.

`competing_family_agreement_le_challengesOnly` restates the bound with the proof-string slots
pinned to the captured scalars (`capturedSlotVals`), counting over the 22 challenge
coordinates alone — what the random-oracle premise alone buys at this capture, covering every
divergence whose restricted discrepancy does not vanish identically at the captured slots.

`competing_family_agreement_le_denClosure` and its challenge-restricted companion extend both
bounds to a competing family bringing its own denominators from the enumerated factor closure,
cross-multiplied at the summed budget: `(16456 + 2077 + 2071) / p = 20604 / p`.

`capturedPoint_goodEvent` corroborates non-vacuity: the good event contains the captured
point itself — the real capture's challenges avoid every enumerated denominator factor.

`fingerprint_matches_positional` bridges the boundary match into the event's positional frame:
the captured `other` bases are pairwise distinct (`capturedMsm_other_bases_nodup`), so the
match's `List.Perm` is realized by the fixed base-matching re-indexing
(`perm_reindex_of_nodup_snd`) and the assembled MSM agrees with the captured one
coordinate-wise.
-/

namespace Zcash.Snark.FixtureRandom2

open Zcash.Snark
open Zcash.Arithmetic (Msm scalarFieldOrder)
open MvPolynomial Finset Fintype

/-- The capstone's verifying-key facts hold at the captured key: domain size positive and
nonzero in `F_p`, ω-powers injective on the opened rotations, the chunk count, and the
reference table duplicate-free with the captured point-set count. -/
theorem vkSymbolicFacts : VkSymbolicFacts shape vk :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- Every permutation chunk stays within the captured chunk width. -/
theorem vk_chunk_width_le : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen := by
  native_decide

/-- The captured chunk count equals the shape's permutation-set count. -/
theorem vk_chunks_length_eq : vk.permutationChunks.length = shape.numPermutationSets := by
  native_decide

/-- The walk's numerator-degree cap at the captured key. -/
theorem msmDegreeBudget_eq : msmDegreeBudget shape vk = 16456 := by native_decide

/-- The walk's denominator-degree cap at the captured key. -/
theorem msmDenBudget_eq : msmDenBudget shape vk = 2077 := by native_decide

/-- The assembled `other` term count at the captured key. -/
theorem otherLen_eq : otherLen shape vk = 123 := by native_decide

/-- The summed Schwartz–Zippel price of the enumerated denominator factors at the captured
key: `n + 1 + |lagrangeRotations| + |queryRotations| + k = 2048 + 1 + 7 + 4 + 11`. -/
theorem denFactors_degree_sum_eq :
    vk.n + 1 + (lagrangeRotations vk).length + (queryRotations vk).length + shape.k = 2071 := by
  native_decide

set_option maxRecDepth 100000 in
/-- The sample space has `49·numProofs + 74` scalar coordinates. -/
theorem card_scalarSlot : Fintype.card (ScalarSlot shape) = 172 := by decide

/-- The captured slot assignment: the captured proof string's scalar slots read through the
sample-space frame, challenge coordinates dropped. The challenge-restricted headliner pins the
proof-string slots here. -/
def capturedSlotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp :=
  fun v => Point.ofInputs ps ch v.val

/-- The challenge block has 22 coordinates: eleven named challenges plus `k = 11` IPA
rounds. -/
theorem card_challengeSlot :
    Fintype.card {v : ScalarSlot shape // IsChallengeSlot v} = 22 := by decide

/-- The rational coefficient family of the deployed assembly at this capture: numerators of
total degree ≤ 16456 over enumerated-factor denominators, one per MSM coordinate, agreeing
with `assemble?` on the whole good event. -/
noncomputable def coefficientFamily :
    RationalCoeffFamily vk derivedInstanceCommitment ps (otherLen shape vk)
      (msmDegreeBudget shape vk) (msmDenBudget shape vk) :=
  assembleCoeffFamily vk derivedInstanceCommitment ps vkSymbolicFacts vk_chunk_width_le
    vk_chunks_length_eq (by decide)

/-- The good event contains the captured point itself: the real capture's challenges avoid
every enumerated denominator factor, so the match-only fixture sits inside the event the ε
theorem prices — the quantified statement is not vacuous at this capture. -/
theorem capturedPoint_goodEvent : GoodEvent vk (Point.ofInputs ps ch) :=
  (goodEvent_iff vk _).mpr (by native_decide)

open Classical in
/-- **ε for the random match at this capture.** Any competing numerator family of total degree
≤ 16456 over the walk's denominators that differs from Lean's at any coordinate agrees with
the assembled MSM at a uniformly random sample-space point with probability at most
`18527 / p`, `p = scalarFieldOrder ≈ 2²⁵⁴`. -/
theorem competing_family_agreement_le
    (num' : MsmCoord shape.k (otherLen shape vk) → MvPolynomial (ScalarSlot shape) Fp)
    (hdeg' : ∀ c, (num' c).totalDegree ≤ msmDegreeBudget shape vk)
    (c₀ : MsmCoord shape.k (otherLen shape vk)) (hne : num' c₀ ≠ coefficientFamily.num c₀) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk derivedInstanceCommitment (Point.toProofString f ps)
              (Point.toChallenges f) = some m
            ∧ m.other.length = otherLen shape vk
            ∧ ∀ c : MsmCoord shape.k (otherLen shape vk),
                m.coeffAt c * eval f (coefficientFamily.den c) = eval f (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ (18527 : ℚ≥0) / scalarFieldOrder := by
  refine le_trans (competing_coefficient_family_agreement_le coefficientFamily
    vkSymbolicFacts.n_pos num' hdeg' c₀ hne) ?_
  have hsum : ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) ≤ ((2071 : ℕ) : ℚ≥0) := by
    have h1 := denFactors_totalDegree_sum_le vk
    have h2 := denFactors_degree_sum_eq
    exact_mod_cast h2 ▸ h1
  rw [msmDegreeBudget_eq]
  gcongr ?_ / _
  calc ((16456 : ℕ) : ℚ≥0) + ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0)
      ≤ ((16456 : ℕ) : ℚ≥0) + ((2071 : ℕ) : ℚ≥0) := add_le_add le_rfl hsum
    _ = (18527 : ℚ≥0) := by norm_num

open Classical in
/-- **ε over the challenge coordinates alone at this capture.** With the proof-string slots
pinned to the captured scalars, any competing numerator family of total degree ≤ 16456 over
the walk's denominators whose restriction to the captured slots differs anywhere from Lean's
agrees with the assembled MSM at a uniformly random challenge assignment with probability at
most `18527 / p` — what the random-oracle premise alone buys at this capture. The
restricted-difference hypothesis is the honest coverage condition: a discrepancy vanishing
identically at the captured slots agrees with probability one over the challenges and is not
covered. -/
theorem competing_family_agreement_le_challengesOnly
    (num' : MsmCoord shape.k (otherLen shape vk) → MvPolynomial (ScalarSlot shape) Fp)
    (hdeg' : ∀ c, (num' c).totalDegree ≤ msmDegreeBudget shape vk)
    (c₀ : MsmCoord shape.k (otherLen shape vk))
    (hne : restrictSlots capturedSlotVals (num' c₀)
        ≠ restrictSlots capturedSlotVals (coefficientFamily.num c₀)) :
    (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk derivedInstanceCommitment
              (Point.toProofString (Point.merge capturedSlotVals g) ps)
              (Point.toChallenges (Point.merge capturedSlotVals g)) = some m
            ∧ m.other.length = otherLen shape vk
            ∧ ∀ c : MsmCoord shape.k (otherLen shape vk),
                m.coeffAt c * eval (Point.merge capturedSlotVals g) (coefficientFamily.den c)
                  = eval (Point.merge capturedSlotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ (18527 : ℚ≥0) / scalarFieldOrder := by
  refine le_trans (competing_coefficient_family_agreement_le_challengesOnly coefficientFamily
    vkSymbolicFacts.n_pos capturedSlotVals num' hdeg' c₀ hne) ?_
  have hsum : ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) ≤ ((2071 : ℕ) : ℚ≥0) := by
    have h1 := denFactors_totalDegree_sum_le vk
    have h2 := denFactors_degree_sum_eq
    exact_mod_cast h2 ▸ h1
  rw [msmDegreeBudget_eq]
  gcongr ?_ / _
  calc ((16456 : ℕ) : ℚ≥0) + ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0)
      ≤ ((16456 : ℕ) : ℚ≥0) + ((2071 : ℕ) : ℚ≥0) := add_le_add le_rfl hsum
    _ = (18527 : ℚ≥0) := by norm_num

open Classical in
/-- **ε across denominators at this capture.** Any competing rational family — numerators of
total degree ≤ 16456, denominators of total degree ≤ 2077 from the enumerated factor closure —
whose cross-multiplied discrepancy with Lean's family is nonzero at some coordinate agrees with
the assembled MSM at a uniformly random sample-space point with probability at most
`(16456 + 2077 + 2071) / p = 20604 / p`. -/
theorem competing_family_agreement_le_denClosure
    (num' den' : MsmCoord shape.k (otherLen shape vk) → MvPolynomial (ScalarSlot shape) Fp)
    (hmem' : ∀ c, den' c ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hdeg' : ∀ c, (num' c).totalDegree ≤ msmDegreeBudget shape vk)
    (hdegden' : ∀ c, (den' c).totalDegree ≤ msmDenBudget shape vk)
    (c₀ : MsmCoord shape.k (otherLen shape vk))
    (hne : num' c₀ * coefficientFamily.den c₀ ≠ coefficientFamily.num c₀ * den' c₀) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk derivedInstanceCommitment (Point.toProofString f ps)
              (Point.toChallenges f) = some m
            ∧ m.other.length = otherLen shape vk
            ∧ ∀ c : MsmCoord shape.k (otherLen shape vk),
                m.coeffAt c * eval f (den' c) = eval f (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ (20604 : ℚ≥0) / scalarFieldOrder := by
  refine le_trans (competing_coefficient_family_agreement_le_denClosure coefficientFamily
    vkSymbolicFacts.n_pos num' den' hmem' hdeg' hdegden' c₀ hne) ?_
  have hsum : ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) ≤ ((2071 : ℕ) : ℚ≥0) := by
    have h1 := denFactors_totalDegree_sum_le vk
    have h2 := denFactors_degree_sum_eq
    exact_mod_cast h2 ▸ h1
  rw [msmDegreeBudget_eq, msmDenBudget_eq]
  gcongr ?_ / _
  calc ((16456 : ℕ) : ℚ≥0) + ((2077 : ℕ) : ℚ≥0)
        + ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0)
      ≤ ((16456 : ℕ) : ℚ≥0) + ((2077 : ℕ) : ℚ≥0) + ((2071 : ℕ) : ℚ≥0) :=
        add_le_add le_rfl hsum
    _ = (20604 : ℚ≥0) := by norm_num

open Classical in
/-- **ε across denominators over the challenge coordinates alone at this capture.** With the
proof-string slots pinned to the captured scalars, a competing rational family within the
16456/2077 budgets agrees with the assembled MSM at a uniformly random challenge assignment
with probability at most `20604 / p`, provided its cross-multiplied discrepancy with Lean's
family does not vanish identically at the captured slots — the cross-denominator form of what
the random-oracle premise alone buys at this capture. -/
theorem competing_family_agreement_le_challengesOnly_denClosure
    (num' den' : MsmCoord shape.k (otherLen shape vk) → MvPolynomial (ScalarSlot shape) Fp)
    (hmem' : ∀ c, den' c ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hdeg' : ∀ c, (num' c).totalDegree ≤ msmDegreeBudget shape vk)
    (hdegden' : ∀ c, (den' c).totalDegree ≤ msmDenBudget shape vk)
    (c₀ : MsmCoord shape.k (otherLen shape vk))
    (hne : restrictSlots capturedSlotVals (num' c₀ * coefficientFamily.den c₀)
        ≠ restrictSlots capturedSlotVals (coefficientFamily.num c₀ * den' c₀)) :
    (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk derivedInstanceCommitment
              (Point.toProofString (Point.merge capturedSlotVals g) ps)
              (Point.toChallenges (Point.merge capturedSlotVals g)) = some m
            ∧ m.other.length = otherLen shape vk
            ∧ ∀ c : MsmCoord shape.k (otherLen shape vk),
                m.coeffAt c * eval (Point.merge capturedSlotVals g) (den' c)
                  = eval (Point.merge capturedSlotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ (20604 : ℚ≥0) / scalarFieldOrder := by
  refine le_trans (competing_coefficient_family_agreement_le_challengesOnly_denClosure
    coefficientFamily vkSymbolicFacts.n_pos capturedSlotVals num' den' hmem' hdeg' hdegden'
    c₀ hne) ?_
  have hsum : ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) ≤ ((2071 : ℕ) : ℚ≥0) := by
    have h1 := denFactors_totalDegree_sum_le vk
    have h2 := denFactors_degree_sum_eq
    exact_mod_cast h2 ▸ h1
  rw [msmDegreeBudget_eq, msmDenBudget_eq]
  gcongr ?_ / _
  calc ((16456 : ℕ) : ℚ≥0) + ((2077 : ℕ) : ℚ≥0)
        + ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0)
      ≤ ((16456 : ℕ) : ℚ≥0) + ((2077 : ℕ) : ℚ≥0) + ((2071 : ℕ) : ℚ≥0) :=
        add_le_add le_rfl hsum
    _ = (20604 : ℚ≥0) := by norm_num

/-- The captured `other` bases are pairwise distinct, so a `List.Perm` match against
`capturedMsm` is forced to the unique base-matching re-indexing
(`perm_reindex_of_nodup_snd`), computed from the two base lists alone. -/
theorem capturedMsm_other_bases_nodup : (capturedMsm.other.map Prod.snd).Nodup := by
  native_decide

/-- **The `Perm`→positional bridge at this capture.** Lean's assembly at the captured inputs
lands inside the positional frame of the agreement event above: `assemble?` succeeds, the
`g`/`w`/`u` coefficients equal the captured ones, and the `other` block equals the captured one
after the base-matching re-indexing `σ`, in the stated `idxOf` form. With
`competing_family_agreement_le`, a competing family in the walk's class differing anywhere from
Lean's passes this capture positionally only on the ≤ ε event.

`σ` is read off the assembled base list at the captured point, so naming one competing family
also needs that base list to be the same across the good event — the positional-frame-stability
premise enumerated in `Fingerprint/Match.lean`, unproven while only the coefficient stream has
`assembleAt_other_map_fst`. -/
theorem fingerprint_matches_positional :
    ∃ m : Msm shape.k Fp G,
      assemble? vk derivedInstanceCommitment ps ch = some m
        ∧ m.other.length = otherLen shape vk
        ∧ capturedMsm.other.length = otherLen shape vk
        ∧ m.gScalars = capturedMsm.gScalars
        ∧ m.wScalar = capturedMsm.wScalar
        ∧ m.uScalar = capturedMsm.uScalar
        ∧ ∃ σ : Fin capturedMsm.other.length ≃ Fin m.other.length,
            ∀ j : Fin capturedMsm.other.length,
              (σ j : ℕ) = (m.other.map Prod.snd).idxOf capturedMsm.other[j].2
                ∧ m.other[(σ j : ℕ)] = capturedMsm.other[j] := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp valid_capture_assembles
  have hassemble : assemble vk derivedInstanceCommitment ps ch = m := by
    unfold assemble
    rw [hm]
    rfl
  have hmatch : MsmMatch m capturedMsm := hassemble ▸ fingerprint_matches
  have hcap : capturedMsm.other.length = otherLen shape vk := by
    rw [otherLen_eq]
    rfl
  exact ⟨m, hm, hmatch.2.2.2.length_eq.trans hcap, hcap, hmatch.1, hmatch.2.1, hmatch.2.2.1,
    msmMatch_other_reindex_of_nodup hmatch capturedMsm_other_bases_nodup⟩

end Zcash.Snark.FixtureRandom2
