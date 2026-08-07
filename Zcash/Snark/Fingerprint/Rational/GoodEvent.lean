import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Zcash.Snark.Fingerprint.SampleSpace

/-!
# The good event: the enumerated denominator factors

The assembled MSM's coefficients are rational functions of the sample-space coordinates
(`Fingerprint/SampleSpace.lean`), and every division the pipeline performs is by a
**challenge-only** value drawn from one enumerated factor list:

| factor | source |
|---|---|
| `xⁿ − 1` | `expectedHEval` (`Verifier/Expressions.lean`) |
| `x` | `lagrangeEval`'s pair differences `x·(ω^{rᵢ} − ω^{rⱼ})` (`Verifier/Checks.lean`) |
| `x − ωⁱ`, `i ∈ lagrangeRotations` | `lagrangeBasisValue` (`Verifier/Assemble.lean`) |
| `x₃ − ω^r·x`, `r ∈ queryRotations` | `multiopenEval`'s `(x₃ − point)⁻¹` (`Verifier/Checks.lean`) |
| `uⱼ` | `ipaFold`'s per-round `uⱼ⁻¹` coefficient (`Verifier/Ipa.lean`) |

`GoodEvent` is *defined* as "no factor vanishes at the point": denominator-nonvanishing for any
product of factors is then definitional (`den_eval_ne_zero`), and the event's complement is
priced by per-factor Schwartz–Zippel at total cost `denFactors_totalDegree_sum_le` — no bespoke
counting. `goodEvent_iff` unfolds the event to its human-readable conjuncts for prose and for
concrete-point checks (the factors themselves live in a noncomputable `MvPolynomial`, so
decidability routes through the unfolded form).

Two of the conjuncts deliberately go beyond `assemble?`'s rejection gates: `x ≠ 0` (note
`0^n = 0 ≠ 1` *passes* the `xⁿ = 1` gate, yet `x` divides the `lagrangeEval` pair differences)
and `uⱼ ≠ 0` (Lean's `0⁻¹ = 0` makes `ipaFold` total, but the `uⱼ⁻¹` coefficient is not a
rational function of `uⱼ` across `uⱼ = 0`). The Lagrange factors `x − ωⁱ` are enumerated instead
of derived from `xⁿ ≠ 1` via `ωⁿ = 1` — pricing seven degree-1 factors costs `7/p` of ε and
saves a primitive-root development the repository does not have.
-/

namespace Zcash.Snark

open MvPolynomial

/-- The rotations at which the vanishing check reads Lagrange basis values
(`lagrangeBasis`): `0` (`l₀`), `−(blinding+1)` (`l_last`), and `−blinding..−1` (`l_blind`). -/
def lagrangeRotations {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G) : List ℤ :=
  0 :: -((vk.blindingFactors : ℤ) + 1)
    :: (List.range vk.blindingFactors).map (fun j => -((j : ℤ) + 1))

/-- Every rotation at which `assembleQueries` opens a commitment: the three query layouts'
rotations, plus `0` (openings at `x`), `1` (`xNext`), `−1` (`xInv`), and `−(blinding+1)`
(`xLast`) from the permutation, lookup, common, and vanishing queries. Every query point is
`x · ω^r` for `r` in this list — `x₃` is never a query point. -/
def queryRotations {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G) : List ℤ :=
  ((vk.instanceQueryLayout ++ vk.adviceQueryLayout ++ vk.fixedQueryLayout).map (·.2)
    ++ [0, 1, -1, -((vk.blindingFactors : ℤ) + 1)]).dedup

/-- The enumerated denominator factors of the assembled coefficients, as polynomials over the
sample space. All are challenge-only: their variables are drawn from the challenge coordinates,
never from proof-string slots. The good event is exactly their joint nonvanishing. -/
noncomputable def denFactors {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G) :
    List (MvPolynomial (ScalarSlot shape) Fp) :=
  [X .x ^ vk.n - 1, X .x]
    ++ ((lagrangeRotations vk).map fun i => X .x - C (vk.omega ^ i))
    ++ ((queryRotations vk).map fun r => X .x3 - C (vk.omega ^ r) * X .x)
    ++ ((List.finRange shape.k).map fun j => X (.ipaRound j))

/-- The good event: no enumerated denominator factor vanishes at the point. Every division the
assembly performs on the event is by a nonzero value (`den_eval_ne_zero`), and the complement is
priced factor-by-factor via Schwartz–Zippel. -/
def GoodEvent {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (pt : Point shape) : Prop :=
  ∀ φ ∈ denFactors vk, eval pt φ ≠ 0

/-- The good event, unfolded to its human-readable conjuncts. Decidability and concrete-point
checks route through this form (the factor list itself is noncomputable `MvPolynomial` data). -/
theorem goodEvent_iff {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (pt : Point shape) :
    GoodEvent vk pt ↔
      pt .x ^ vk.n ≠ 1 ∧ pt .x ≠ 0
        ∧ (∀ i ∈ lagrangeRotations vk, pt .x ≠ vk.omega ^ i)
        ∧ (∀ r ∈ queryRotations vk, pt .x3 ≠ vk.omega ^ r * pt .x)
        ∧ (∀ j : Fin shape.k, pt (.ipaRound j) ≠ 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, fun i hi => ?_, fun r hr => ?_, fun j => ?_⟩
    · have := h (X ScalarSlot.x ^ vk.n - 1) (by simp [denFactors])
      simpa [sub_ne_zero] using this
    · have := h (X ScalarSlot.x) (by simp [denFactors])
      simpa using this
    · have := h (X ScalarSlot.x - C (vk.omega ^ i)) ?_
      · simpa [sub_ne_zero] using this
      · simp only [denFactors, List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, hi, rfl⟩)))
    · have := h (X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x) ?_
      · simpa [sub_ne_zero] using this
      · simp only [denFactors, List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · have := h (X (ScalarSlot.ipaRound j)) ?_
      · simpa using this
      · simp only [denFactors, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  · rintro ⟨h1, h2, h3, h4, h5⟩ φ hφ
    simp only [denFactors, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_finRange, true_and] at hφ
    rcases hφ with (((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨j, rfl⟩
    · simpa [sub_ne_zero] using h1
    · simpa using h2
    · simpa [sub_ne_zero] using h3 i hi
    · simpa [sub_ne_zero] using h4 r hr
    · simpa using h5 j

instance {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G) (pt : Point shape) :
    Decidable (GoodEvent vk pt) :=
  decidable_of_iff' _ (goodEvent_iff vk pt)

/-- Every enumerated factor is a nonzero polynomial (witnessed by evaluation points), so each is
individually priceable by Schwartz–Zippel. -/
theorem denFactors_ne_zero {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (hn : 0 < vk.n) : ∀ φ ∈ denFactors vk, φ ≠ 0 := by
  intro φ hφ
  simp only [denFactors, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_finRange, true_and] at hφ
  rcases hφ with (((rfl | rfl) | ⟨i, _, rfl⟩) | ⟨r, _, rfl⟩) | ⟨j, rfl⟩
  · intro h
    have := congrArg (eval (0 : Point shape)) h
    simp [zero_pow hn.ne'] at this
  · exact X_ne_zero _
  · intro h
    have := congrArg (eval fun s => if s = ScalarSlot.x then vk.omega ^ i + 1 else 0) h
    simp at this
  · intro h
    have := congrArg (eval fun s => if s = ScalarSlot.x3 then 1 else 0) h
    simp at this
  · exact X_ne_zero _

/-- The total Schwartz–Zippel price of the good event: the factor degrees sum to at most
`n + 1 + |lagrangeRotations| + |queryRotations| + k` (`2048 + 1 + 7 + 4 + 11 = 2071` at the
captured key). -/
theorem denFactors_totalDegree_sum_le {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) :
    ((denFactors vk).map totalDegree).sum
      ≤ vk.n + 1 + (lagrangeRotations vk).length + (queryRotations vk).length + shape.k := by
  have hXpow : ((X ScalarSlot.x ^ vk.n - 1 : MvPolynomial (ScalarSlot shape) Fp)).totalDegree
      ≤ vk.n := by
    refine le_trans (totalDegree_sub _ _) ?_
    simp [totalDegree_X_pow]
  have hlag : ∀ i : ℤ,
      ((X ScalarSlot.x - C (vk.omega ^ i) : MvPolynomial (ScalarSlot shape) Fp)).totalDegree
        ≤ 1 := by
    intro i
    refine le_trans (totalDegree_sub _ _) ?_
    simp [totalDegree_X]
  have hqr : ∀ r : ℤ,
      ((X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x :
        MvPolynomial (ScalarSlot shape) Fp)).totalDegree ≤ 1 := by
    intro r
    refine le_trans (totalDegree_sub _ _) ?_
    refine max_le (by simp [totalDegree_X]) (le_trans (totalDegree_mul _ _) ?_)
    simp [totalDegree_X, totalDegree_C]
  have hsum : ∀ (l : List ℤ) (f : ℤ → MvPolynomial (ScalarSlot shape) Fp),
      (∀ i, (f i).totalDegree ≤ 1) → ((l.map f).map totalDegree).sum ≤ l.length := by
    intro l f hf
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hf a
      omega
  have hipa : (((List.finRange shape.k).map fun j =>
      (X (ScalarSlot.ipaRound j) : MvPolynomial (ScalarSlot shape) Fp)).map
        totalDegree).sum ≤ shape.k := by
    have hj : ∀ j : Fin shape.k,
        ((X (ScalarSlot.ipaRound j) : MvPolynomial (ScalarSlot shape) Fp)).totalDegree ≤ 1 :=
      fun j => by simp [totalDegree_X]
    calc (((List.finRange shape.k).map fun j =>
          (X (ScalarSlot.ipaRound j) : MvPolynomial (ScalarSlot shape) Fp)).map
            totalDegree).sum
        ≤ (List.finRange shape.k).length := by
          induction (List.finRange shape.k) with
          | nil => simp
          | cons a t ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            have := hj a
            omega
      _ = shape.k := by simp
  have h1 := hsum (lagrangeRotations vk) (fun i => X ScalarSlot.x - C (vk.omega ^ i)) hlag
  have h2 := hsum (queryRotations vk)
    (fun r => X ScalarSlot.x3 - C (vk.omega ^ r) * X ScalarSlot.x) hqr
  simp only [denFactors, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, totalDegree_X]
  omega

/-- Denominator-nonvanishing on the good event is definitional: any product of enumerated
factors evaluates to a product of nonzero values. This is the lemma the representation walk's
`divFactor`/`invFactor` steps and the ε theorem's agreement reading rest on. -/
theorem den_eval_ne_zero {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}
    {den : MvPolynomial (ScalarSlot shape) Fp}
    (hmem : den ∈ Submonoid.closure {φ | φ ∈ denFactors vk}) {pt : Point shape}
    (hgood : GoodEvent vk pt) : eval pt den ≠ 0 := by
  induction hmem using Submonoid.closure_induction with
  | mem φ hφ => exact hgood φ hφ
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

/-- Substituting degree-≤ 1 polynomials for the variables does not raise total degree: a
monomial of degree `Σᵥ d v` maps to `C r · Πᵥ (f v) ^ d v`, of total degree at most
`Σᵥ d v · totalDegree (f v)`. The restriction step of the challenge-restricted ε theorem
substitutes variables and constants, both of degree ≤ 1. -/
theorem totalDegree_aeval_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ v, (f v).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun d hd => le_trans ?_ (le_totalDegree hd)
  rw [aeval_monomial]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [algebraMap_eq, totalDegree_C, zero_add, Finsupp.prod]
  refine le_trans (totalDegree_finsetProd _ _) ?_
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun w _ => ?_
  calc (f w ^ d w).totalDegree ≤ d w * (f w).totalDegree := totalDegree_pow _ _
    _ ≤ d w * 1 := Nat.mul_le_mul_left _ (hf w)
    _ = d w := mul_one _

/-- Restrict a sample-space polynomial along fixing the proof-string slots: slot variables
become the constants `slotVals` prescribes, challenge variables become variables of the
challenge subtype. Evaluation at a challenge assignment is evaluation of the original at the
merged point (`eval_restrictSlots`), and total degree does not increase
(`restrictSlots_totalDegree_le`). -/
noncomputable def restrictSlots {shape : Shape}
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp) :
    MvPolynomial (ScalarSlot shape) Fp
      →ₐ[Fp] MvPolynomial {v : ScalarSlot shape // IsChallengeSlot v} Fp :=
  aeval fun v => if h : IsChallengeSlot v then X ⟨v, h⟩ else C (slotVals ⟨v, h⟩)

/-- A challenge variable restricts to the corresponding subtype variable. -/
theorem restrictSlots_X {shape : Shape}
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    {v : ScalarSlot shape} (h : IsChallengeSlot v) :
    restrictSlots slotVals (X v) = X ⟨v, h⟩ := by
  simp only [restrictSlots, aeval_X, dif_pos h]

/-- Evaluating a restricted polynomial at a challenge assignment evaluates the original at
the merged point. -/
theorem eval_restrictSlots {shape : Shape}
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp)
    (p : MvPolynomial (ScalarSlot shape) Fp) :
    eval g (restrictSlots slotVals p) = eval (Point.merge slotVals g) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrictSlots]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, restrictSlots, aeval_X, eval_X]
    congr 1
    by_cases h : IsChallengeSlot v
    · rw [dif_pos h, eval_X, Point.merge_apply_pos h]
    · rw [dif_neg h, eval_C, Point.merge_apply_neg h]

/-- Restriction does not raise total degree: it substitutes subtype variables and constants,
both of degree ≤ 1. -/
theorem restrictSlots_totalDegree_le {shape : Shape}
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (p : MvPolynomial (ScalarSlot shape) Fp) :
    (restrictSlots slotVals p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le_of_le_one _ (fun v => ?_) p
  by_cases h : IsChallengeSlot v
  · rw [dif_pos h]
    exact le_of_eq (totalDegree_X _)
  · rw [dif_neg h]
    simp

/-- Every restricted denominator factor is still nonzero: the factors are challenge-only, so
the witnesses of `denFactors_ne_zero` constrain only challenge coordinates and survive the
merge with any slot assignment. -/
theorem restrictSlots_denFactors_ne_zero {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (hn : 0 < vk.n)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp) :
    ∀ ψ ∈ (denFactors vk).map (restrictSlots slotVals), ψ ≠ 0 := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
  simp only [denFactors, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_finRange, true_and] at hφ
  rcases hφ with (((rfl | rfl) | ⟨i, _, rfl⟩) | ⟨r, _, rfl⟩) | ⟨j, rfl⟩
  · intro h
    have := congrArg
      (eval (fun _ => 0 : {v : ScalarSlot shape // IsChallengeSlot v} → Fp)) h
    rw [eval_restrictSlots, map_zero] at this
    simp [Point.merge_apply_pos (show IsChallengeSlot (ScalarSlot.x (shape := shape)) from rfl),
      zero_pow hn.ne'] at this
  · rw [restrictSlots_X slotVals (show IsChallengeSlot (ScalarSlot.x (shape := shape)) from rfl)]
    exact X_ne_zero _
  · intro h
    have := congrArg (eval fun w : {v : ScalarSlot shape // IsChallengeSlot v} =>
      if w.val = ScalarSlot.x then vk.omega ^ i + 1 else 0) h
    rw [eval_restrictSlots, map_zero] at this
    simp [Point.merge_apply_pos (show IsChallengeSlot (ScalarSlot.x (shape := shape)) from rfl)]
      at this
  · intro h
    have := congrArg (eval fun w : {v : ScalarSlot shape // IsChallengeSlot v} =>
      if w.val = ScalarSlot.x3 then 1 else 0) h
    rw [eval_restrictSlots, map_zero] at this
    simp [Point.merge_apply_pos (show IsChallengeSlot (ScalarSlot.x (shape := shape)) from rfl),
      Point.merge_apply_pos (show IsChallengeSlot (ScalarSlot.x3 (shape := shape)) from rfl)]
      at this
  · rw [restrictSlots_X slotVals
      (show IsChallengeSlot (ScalarSlot.ipaRound (shape := shape) j) from rfl)]
    exact X_ne_zero _

/-- Restriction does not raise any factor's degree, so the restricted list's summed
Schwartz–Zippel price is bounded by the original's. -/
theorem restrictSlots_denFactors_totalDegree_sum_le {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp) :
    (((denFactors vk).map (restrictSlots slotVals)).map totalDegree).sum
      ≤ ((denFactors vk).map totalDegree).sum := by
  rw [List.map_map]
  exact List.sum_le_sum fun φ _ => restrictSlots_totalDegree_le slotVals φ

/-- The good event at a merged point is a challenge-side event: no restricted factor vanishes
at the challenge assignment. -/
theorem goodEvent_merge_iff {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp) :
    GoodEvent vk (Point.merge slotVals g) ↔
      ∀ ψ ∈ (denFactors vk).map (restrictSlots slotVals), eval g ψ ≠ 0 := by
  constructor
  · intro h ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
    rw [eval_restrictSlots]
    exact h φ hφ
  · intro h φ hφ
    rw [← eval_restrictSlots slotVals g φ]
    exact h _ (List.mem_map_of_mem hφ)

end Zcash.Snark
