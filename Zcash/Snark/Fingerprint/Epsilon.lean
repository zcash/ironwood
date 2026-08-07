import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Fingerprint.SchwartzZippel
import Zcash.Snark.Fingerprint.Rational.Family

/-!
# The quantified random match: ε for a competing coefficient family

The generic half of the quantified match's ε theorem. The representation walk
(`Fingerprint/Rational/`) delivers, per capture family, a `RationalCoeffFamily`: polynomial
numerators over enumerated challenge-only denominators for every coefficient position of the
assembled MSM, agreeing with `assemble?`'s output on the good event. This module prices what
that buys.

## The bounds

* `card_exists_eval_zero_le` — a list of nonzero polynomials vanishes somewhere on at most the
  sum of its Schwartz–Zippel prices.
* `goodEvent_compl_card_le` — the good event's complement costs at most
  `Σ totalDegree (denFactors vk) / p`, which `denFactors_totalDegree_sum_le` reads as
  `(n + 1 + |lagrangeRotations| + |queryRotations| + k) / p`.
* `competing_coefficient_family_agreement_le` — **the ε theorem**: a competing numerator family
  of total degree ≤ `D` over the same denominators, differing from Lean's anywhere, agrees with
  the assembled MSM at a uniform point with probability at most
  `(D + Σ totalDegree (denFactors vk)) / p`, `p = scalarFieldOrder ≈ 2²⁵⁴`. Either the point
  falls off the good event, or the nonzero difference polynomial vanishes.
* `competing_coefficient_family_agreement_le_challengesOnly` — the same bound with the
  proof-string slots pinned to an arbitrary assignment, counted over the challenge coordinates
  alone. This is what the random-oracle premise alone buys at a capture: coverage of every
  divergence whose discrepancy does not vanish identically at the pinned slots.
* `competing_coefficient_family_agreement_le_denClosure` and its challenge-restricted
  companion — both bounds for a family bringing its *own* denominators from the enumerated
  factor closure, at the summed budget `(D + Dden + Σ totalDegree (denFactors vk)) / p`.
  `RationalCoeffFamily.mulDen` cross-multiplies to clear both sides; the cleared identities
  survive multiplication, so no nonvanishing is consumed.

## The frame the comparison lives in

The comparison is positional over `MsmCoord`. On the good event the multiopen grouping is one
fixed combinatorial object, so the coefficient list and its length are fixed
(`assembleAt_other_map_fst`, `assembleAt_other_length`) and families are compared coordinate by
coordinate. `MsmMatch` compares the `other` terms up to `List.Perm`, which absorbs append order
between two concrete assemblies. `perm_reindex_of_nodup_snd` (`Fingerprint/Match.lean`) turns a
passing match into a re-indexing, unique because the captured bases are pairwise distinct
(`capturedMsm_other_bases_nodup`, `fingerprint_matches_positional`), and precomposing the
competing family with a fixed re-indexing changes neither degrees nor ε. That the re-indexing
*is* fixed across the good event is the trust chapter's positional-frame-stability premise, not
a theorem here.

## Scope

Statements are conditioned on `assemble? = some m` throughout — never the total `assemble`,
whose zero-MSM fallback evaluates to the accept value (`Verifier/Assemble.lean`).
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm scalarFieldOrder)
open MvPolynomial Finset Fintype

/-- Union bound over a list of nonzero polynomials: the fraction of the sample space on which
some element vanishes is at most the sum of the elements' Schwartz–Zippel prices. -/
theorem card_exists_eval_zero_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    (l : List (MvPolynomial σ Fp)) (hl : ∀ φ ∈ l, φ ≠ 0) :
    (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ φ ∈ l, eval f φ = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
      ≤ (((l.map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
  classical
  induction l with
  | nil => simp
  | cons φ t ih =>
    have hφ0 : φ ≠ 0 := hl φ List.mem_cons_self
    have ht := ih fun ψ hψ => hl ψ (List.mem_cons_of_mem _ hψ)
    have hsub : {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0}
        ⊆ {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
          ∪ {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} := by
      intro f hf
      simp only [Finset.mem_filter, List.mem_cons, Finset.mem_union] at hf ⊢
      obtain ⟨hmem, ψ, hψ | hψ, hzero⟩ := hf
      · exact Or.inl ⟨hmem, hψ ▸ hzero⟩
      · exact Or.inr ⟨hmem, ψ, hψ, hzero⟩
    have hcard : #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0}
        ≤ #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
          + #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hφSZ := fingerprint_schwartz_zippel_index hφ0
    calc (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
        ≤ ((#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
            + #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} : ℕ) : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ := by
          gcongr
      _ = (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0} : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
            + (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ := by
          push_cast
          rw [add_div]
      _ ≤ (φ.totalDegree : ℚ≥0) / scalarFieldOrder
            + (((t.map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder :=
          add_le_add hφSZ ht
      _ = ((((φ :: t).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
          simp only [List.map_cons, List.sum_cons]
          push_cast
          rw [add_div]

/-- The good event's complement, priced: the fraction of the sample space off the good event is
at most the summed Schwartz–Zippel price of the enumerated denominator factors
(`denFactors_totalDegree_sum_le` bounds the sum by
`n + 1 + |lagrangeRotations| + |queryRotations| + k`). -/
theorem goodEvent_compl_card_le {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (hn : 0 < vk.n) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
  classical
  have hcongr : {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
      = {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
          ∃ φ ∈ denFactors vk, eval f φ = 0} := by
    refine Finset.filter_congr fun f _ => ?_
    simp [GoodEvent]
  rw [hcongr]
  exact card_exists_eval_zero_le _ (denFactors_ne_zero vk hn)

open Classical in
/-- The good event's complement with the proof-string slots pinned, priced over the challenge
coordinates alone — at the same cost as over the full space: the enumerated factors are
challenge-only (`goodEvent_merge_iff`) and restriction does not raise degree
(`restrictSlots_denFactors_totalDegree_sum_le`). -/
theorem goodEvent_merge_compl_card_le {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (hn : 0 < vk.n)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp) :
    (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) | ¬ GoodEvent vk (Point.merge slotVals g)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
  have hcongr : {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) | ¬ GoodEvent vk (Point.merge slotVals g)}
      = {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
          (univ : Finset Fp) |
          ∃ ψ ∈ (denFactors vk).map (restrictSlots slotVals), eval g ψ = 0} := by
    refine Finset.filter_congr fun g _ => ?_
    simp [goodEvent_merge_iff vk slotVals g]
  rw [hcongr]
  refine le_trans
    (card_exists_eval_zero_le _ (restrictSlots_denFactors_ne_zero vk hn slotVals)) ?_
  gcongr
  exact_mod_cast restrictSlots_denFactors_totalDegree_sum_le vk slotVals

open Classical in
/-- **The ε theorem, generic form.** Any competing numerator family of total degree ≤ `D` over
the same denominators that differs from Lean's at some coordinate agrees with the assembled MSM
at a uniformly random sample-space point with probability at most
`(D + Σ totalDegree (denFactors vk)) / p`: either the point falls off the good event (the
second summand, `goodEvent_compl_card_le`), or agreement at the differing coordinate makes the
nonzero difference polynomial vanish (the first summand, Schwartz–Zippel). Conditioned on
`assemble? = some m` — the total `assemble`'s zero fallback evaluates to the accept value and
must not appear here. -/
theorem competing_coefficient_family_agreement_le {shape : Shape} {G : Type*}
    [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden) (hn : 0 < vk.n)
    (num' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hdeg' : ∀ c, (num' c).totalDegree ≤ D)
    (c₀ : MsmCoord shape.k L) (hne : num' c₀ ≠ fam.num c₀) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
  set d : MvPolynomial (ScalarSlot shape) Fp := fam.num c₀ - num' c₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hddeg : d.totalDegree ≤ D :=
    le_trans (totalDegree_sub _ _) (max_le (fam.num_totalDegree_le c₀) (hdeg' c₀))
  have hsub : {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
      ⊆ {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
        ∪ {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0} := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_union] at hf ⊢
    obtain ⟨hmem, m, hm, _, hagree⟩ := hf
    by_cases hgood : GoodEvent vk f
    · refine Or.inr ⟨hmem, ?_⟩
      obtain ⟨m', hm', _, hrep⟩ := fam.represents f hgood
      have hmm : m = m' := Option.some.inj (hm ▸ hm')
      have h1 := hrep c₀
      have h2 := hagree c₀
      rw [hmm] at h2
      rw [hd, map_sub, sub_eq_zero, ← h1, ← h2]
    · exact Or.inl ⟨hmem, hgood⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hbad := goodEvent_compl_card_le vk hn
  have hzero := fingerprint_schwartz_zippel_index hd0
  calc (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
          + #{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0}
          : ℕ) : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape) := by
        gcongr
    _ = (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
          : ℚ≥0) / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
        + (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0}
          : ℚ≥0) / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape) := by
        push_cast
        rw [add_div]
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (d.totalDegree : ℚ≥0) / scalarFieldOrder := add_le_add hbad hzero
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (D : ℚ≥0) / scalarFieldOrder := by
        gcongr
    _ = ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ)) / scalarFieldOrder := by
        rw [add_comm, add_div]

open Classical in
/-- **The ε theorem over the challenge coordinates alone.** Fix the proof-string slots to an
arbitrary assignment `slotVals`; any competing numerator family of total degree ≤ `D` over the
same denominators whose restriction to `slotVals` differs from Lean's at some coordinate agrees
with the assembled MSM at a uniformly random challenge assignment with probability at most
`(D + Σ totalDegree (denFactors vk)) / p` — the full product-space bound, because the good-event
factors are challenge-only and restriction does not raise degree. The hypothesis is the
*restricted* difference being nonzero — the honest coverage condition: a discrepancy vanishing
identically at `slotVals` agrees with probability one over the challenges and is not covered. -/
theorem competing_coefficient_family_agreement_le_challengesOnly {shape : Shape} {G : Type*}
    [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden) (hn : 0 < vk.n)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (num' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hdeg' : ∀ c, (num' c).totalDegree ≤ D)
    (c₀ : MsmCoord shape.k L)
    (hne : restrictSlots slotVals (num' c₀) ≠ restrictSlots slotVals (fam.num c₀)) :
    (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (fam.den c)
                  = eval (Point.merge slotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
  set d : MvPolynomial {v : ScalarSlot shape // IsChallengeSlot v} Fp :=
    restrictSlots slotVals (fam.num c₀) - restrictSlots slotVals (num' c₀) with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hddeg : d.totalDegree ≤ D :=
    le_trans (totalDegree_sub _ _) (max_le
      (le_trans (restrictSlots_totalDegree_le _ _) (fam.num_totalDegree_le c₀))
      (le_trans (restrictSlots_totalDegree_le _ _) (hdeg' c₀)))
  have hsub : {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (fam.den c)
                  = eval (Point.merge slotVals g) (num' c)}
      ⊆ {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
          (univ : Finset Fp) | ¬ GoodEvent vk (Point.merge slotVals g)}
        ∪ {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
            (univ : Finset Fp) | eval g d = 0} := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_union] at hg ⊢
    obtain ⟨hmem, m, hm, _, hagree⟩ := hg
    by_cases hgood : GoodEvent vk (Point.merge slotVals g)
    · refine Or.inr ⟨hmem, ?_⟩
      obtain ⟨m', hm', _, hrep⟩ := fam.represents (Point.merge slotVals g) hgood
      have hmm : m = m' := Option.some.inj (hm ▸ hm')
      have h1 := hrep c₀
      have h2 := hagree c₀
      rw [hmm] at h2
      rw [hd, map_sub, eval_restrictSlots, eval_restrictSlots, sub_eq_zero, ← h1, ← h2]
    · exact Or.inl ⟨hmem, hgood⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hbad := goodEvent_merge_compl_card_le vk hn slotVals
  have hzero := fingerprint_schwartz_zippel_index hd0
  calc (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (fam.den c)
                  = eval (Point.merge slotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ ((#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
            (univ : Finset Fp) | ¬ GoodEvent vk (Point.merge slotVals g)}
          + #{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
              (univ : Finset Fp) | eval g d = 0}
          : ℕ) : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0)
              ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v} := by
        gcongr
    _ = (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
            (univ : Finset Fp) | ¬ GoodEvent vk (Point.merge slotVals g)} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0)
              ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
        + (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
              (univ : Finset Fp) | eval g d = 0} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0)
              ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v} := by
        push_cast
        rw [add_div]
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (d.totalDegree : ℚ≥0) / scalarFieldOrder := add_le_add hbad hzero
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (D : ℚ≥0) / scalarFieldOrder := by
        gcongr
    _ = ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ)) / scalarFieldOrder := by
        rw [add_comm, add_div]

open Classical in
/-- **The ε theorem across denominators.** A competing rational family — numerators of total
degree ≤ `D`, denominators of total degree ≤ `Dden` from the enumerated factor closure — agrees
with the assembled MSM at a uniformly random sample-space point with probability at most
`(D + Dden + Σ totalDegree (denFactors vk)) / p`. The hypothesis is the cross-multiplied
discrepancy `num' c₀ * fam.den c₀ ≠ fam.num c₀ * den' c₀` — disagreement of the rational
functions themselves, both denominators being nonzero polynomials. `mulDen` clears the
denominators and `competing_coefficient_family_agreement_le` reprices at budget `D + Dden`. -/
theorem competing_coefficient_family_agreement_le_denClosure {shape : Shape} {G : Type*}
    [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden) (hn : 0 < vk.n)
    (num' den' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hmem' : ∀ c, den' c ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hdeg' : ∀ c, (num' c).totalDegree ≤ D)
    (hdegden' : ∀ c, (den' c).totalDegree ≤ Dden)
    (c₀ : MsmCoord shape.k L) (hne : num' c₀ * fam.den c₀ ≠ fam.num c₀ * den' c₀) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (den' c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((D : ℚ≥0) + Dden + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
  have hdeg'' : ∀ c, (num' c * fam.den c).totalDegree ≤ D + Dden := fun c =>
    le_trans (totalDegree_mul _ _) (add_le_add (hdeg' c) (fam.den_totalDegree_le c))
  have hsub : {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (den' c) = eval f (num' c)}
      ⊆ {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
          ∃ m : Msm shape.k Fp G,
            assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
              ∧ m.other.length = L
              ∧ ∀ c : MsmCoord shape.k L,
                  m.coeffAt c * eval f ((fam.mulDen den' hmem' hdegden').den c)
                    = eval f (num' c * fam.den c)} := by
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    obtain ⟨hmem, m, hm, hlen, hagree⟩ := hf
    refine ⟨hmem, m, hm, hlen, fun c => ?_⟩
    show m.coeffAt c * eval f (fam.den c * den' c) = eval f (num' c * fam.den c)
    rw [map_mul, map_mul, ← hagree c]
    ring
  have hcard := Finset.card_le_card hsub
  calc (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (den' c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
          ∃ m : Msm shape.k Fp G,
            assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
              ∧ m.other.length = L
              ∧ ∀ c : MsmCoord shape.k L,
                  m.coeffAt c * eval f ((fam.mulDen den' hmem' hdegden').den c)
                    = eval f (num' c * fam.den c)} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape) := by
        gcongr
    _ ≤ (((D + Dden : ℕ) : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder :=
        competing_coefficient_family_agreement_le (fam.mulDen den' hmem' hdegden') hn
          (fun c => num' c * fam.den c) hdeg'' c₀ hne
    _ = ((D : ℚ≥0) + Dden + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
        rw [Nat.cast_add]

open Classical in
/-- **The ε theorem across denominators, over the challenge coordinates alone.** The
cross-denominator bound with the proof-string slots pinned to an arbitrary assignment,
counting over the challenge coordinates: the same
`(D + Dden + Σ totalDegree (denFactors vk)) / p`. The hypothesis is the *restricted*
cross-multiplied discrepancy at `slotVals` — the honest coverage condition of
`competing_coefficient_family_agreement_le_challengesOnly` in the cross-multiplied shape of
`competing_coefficient_family_agreement_le_denClosure`. Same reduction through `mulDen`. -/
theorem competing_coefficient_family_agreement_le_challengesOnly_denClosure {shape : Shape}
    {G : Type*} [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden) (hn : 0 < vk.n)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (num' den' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hmem' : ∀ c, den' c ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hdeg' : ∀ c, (num' c).totalDegree ≤ D)
    (hdegden' : ∀ c, (den' c).totalDegree ≤ Dden)
    (c₀ : MsmCoord shape.k L)
    (hne : restrictSlots slotVals (num' c₀ * fam.den c₀)
        ≠ restrictSlots slotVals (fam.num c₀ * den' c₀)) :
    (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (den' c)
                  = eval (Point.merge slotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ ((D : ℚ≥0) + Dden + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
  have hdeg'' : ∀ c, (num' c * fam.den c).totalDegree ≤ D + Dden := fun c =>
    le_trans (totalDegree_mul _ _) (add_le_add (hdeg' c) (fam.den_totalDegree_le c))
  have hsub : {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (den' c)
                  = eval (Point.merge slotVals g) (num' c)}
      ⊆ {g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
          (univ : Finset Fp) |
          ∃ m : Msm shape.k Fp G,
            assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
                (Point.toChallenges (Point.merge slotVals g)) = some m
              ∧ m.other.length = L
              ∧ ∀ c : MsmCoord shape.k L,
                  m.coeffAt c
                      * eval (Point.merge slotVals g) ((fam.mulDen den' hmem' hdegden').den c)
                    = eval (Point.merge slotVals g) (num' c * fam.den c)} := by
    intro g hg
    simp only [Finset.mem_filter] at hg ⊢
    obtain ⟨hmem, m, hm, hlen, hagree⟩ := hg
    refine ⟨hmem, m, hm, hlen, fun c => ?_⟩
    show m.coeffAt c * eval (Point.merge slotVals g) (fam.den c * den' c)
        = eval (Point.merge slotVals g) (num' c * fam.den c)
    rw [map_mul, map_mul, ← hagree c]
    ring
  have hcard := Finset.card_le_card hsub
  calc (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
        (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
              (Point.toChallenges (Point.merge slotVals g)) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L,
                m.coeffAt c * eval (Point.merge slotVals g) (den' c)
                  = eval (Point.merge slotVals g) (num' c)} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v}
      ≤ (#{g ∈ piFinset fun _ : {v : ScalarSlot shape // IsChallengeSlot v} =>
          (univ : Finset Fp) |
          ∃ m : Msm shape.k Fp G,
            assemble? vk ic (Point.toProofString (Point.merge slotVals g) base)
                (Point.toChallenges (Point.merge slotVals g)) = some m
              ∧ m.other.length = L
              ∧ ∀ c : MsmCoord shape.k L,
                  m.coeffAt c
                      * eval (Point.merge slotVals g) ((fam.mulDen den' hmem' hdegden').den c)
                    = eval (Point.merge slotVals g) (num' c * fam.den c)} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0)
              ^ Fintype.card {v : ScalarSlot shape // IsChallengeSlot v} := by
        gcongr
    _ ≤ (((D + Dden : ℕ) : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder :=
        competing_coefficient_family_agreement_le_challengesOnly
          (fam.mulDen den' hmem' hdegden') hn slotVals
          (fun c => num' c * fam.den c) hdeg'' c₀ hne
    _ = ((D : ℚ≥0) + Dden + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
        rw [Nat.cast_add]

end Zcash.Snark
