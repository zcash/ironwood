import Mathlib
import Zcash.Snark.Core.Group

/-!
# Knowledge soundness: the polynomial-commitment / inner-product-argument layer

Steps 1–2 established faithfulness: the deployed verifier collapses to the fingerprint MSM, and the
Lean assembly reproduces it (the match). This module begins soundness — that an accepting proof implies
the prover knows a valid witness — via the special soundness of the inner-product argument (IPA), the
cryptographic core of the halo2 opening.

The IPA proves knowledge of a coefficient vector `a` (a polynomial) behind a commitment `P = ⟨a, G⟩`
that opens to a value `v` at a point — i.e. `⟨a, b⟩ = v` for the evaluation vector `b = (1, x, x², …)`.
The fingerprint MSM's `g`-part is this commitment, so the layer is expressed directly over the URS:

* `commit` — `⟨a, G⟩ = Σᵢ aᵢ • gᵢ`, the polynomial commitment (the MSM's `g`-part).
* `evalVector` / `innerProduct` — `b = (1, x, …, x^{n−1})` and `⟨a, b⟩` (the polynomial at `x`).
* `IpaRelation` — the opening relation `⟨a, G⟩ = P ∧ ⟨a, b⟩ = v` the IPA is an argument of knowledge for.
* `innerProduct_add_left` — `⟨·, b⟩` is additive in its left argument; together with `commit`'s linearity
  (`commitGen_add_left` / `commitGen_smul_left` in `Zcash.Snark.Soundness.CommitFold`, via
  `commit_eq_commitGen`) this is the algebra the round extractor folds with.

The IPA's witness fold is 2-special-sound per round: from two accepting transcripts that share the round commitments
`(Lⱼ, Rⱼ)` but answer distinct challenges `uⱼ`, the round's witness folds back, and recursing over the
`k` rounds extracts an `a` satisfying `IpaRelation`. Building that extractor is the next phase; the
per-round folding rests on the linearity proved here. Curve-group binding stays an explicit assumption —
modelled as discrete-log-relation (DLR) hardness (`commitmentBinding_iff_no_relation`), per project scope.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The polynomial commitment of a coefficient vector `a` against the URS generators:
`⟨a, G⟩ = Σᵢ aᵢ • gᵢ`. This is the `g`-part of the fingerprint MSM (`Zcash.Snark.Msm.eval`). -/
def commit (urs : URS G) (a : Fin (2 ^ urs.k) → F) : G :=
  ∑ i, a i • urs.g i

/-- The evaluation vector `b = (1, x, x², …, x^{2ᵏ−1})`. The inner product `⟨a, b⟩` is the polynomial
with coefficients `a` evaluated at `x`. -/
def evalVector (k : ℕ) (x : F) : Fin (2 ^ k) → F :=
  fun i => x ^ (i : ℕ)

/-- The inner product `⟨a, b⟩ = Σᵢ aᵢ bᵢ` of two coefficient vectors. -/
def innerProduct {n : ℕ} (a b : Fin n → F) : F :=
  ∑ i, a i * b i

/-- The IPA opening relation: the witness `a` is the polynomial committed by `P` (`⟨a, G⟩ = P`) that
opens to `v` at the point encoded by `b` (`⟨a, b⟩ = v`). The inner-product argument is an argument of
knowledge for this relation; special soundness produces such an `a` from accepting transcripts. -/
def IpaRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v : F)
    (a : Fin (2 ^ urs.k) → F) : Prop :=
  commit urs a = P ∧ innerProduct a b = v

/-- `commit` is additive in the coefficient vector: `⟨a + a', G⟩ = ⟨a, G⟩ + ⟨a', G⟩`. -/
theorem commit_add (urs : URS G) (a a' : Fin (2 ^ urs.k) → F) :
    commit urs (a + a') = commit urs a + commit urs a' := by
  simp only [commit, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- A single-index coefficient vector commits to that generator scaled: `⟨[i ↦ x], G⟩ = x • gᵢ`. -/
theorem commit_single (urs : URS G) (i : Fin (2 ^ urs.k)) (x : F) :
    commit urs (Pi.single i x) = x • urs.g i := by
  simp only [commit]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- `innerProduct` is additive in its left argument. -/
theorem innerProduct_add {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- A single-index left argument: `⟨[i ↦ x], b⟩ = x · bᵢ`. -/
theorem innerProduct_single {n : ℕ} (i : Fin n) (x : F) (b : Fin n → F) :
    innerProduct (Pi.single i x) b = x * b i := by
  simp only [innerProduct]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- **The adjusted-commitment un-shift (halo2's value placement).** halo2's IPA verifier folds the claimed
value into the commitment at `g₀` (`msm.add_constant_term(-v)`, so the opened commitment is `P − [v]g₀`) while
checking the inner product on `U`; the two are reconciled by the evaluation vector's leading entry `b₀ = 1`
(`evalVector` gives `b 0 = x^0 = 1`). So opening `P − [v]g₀` to inner product `0` *is* opening `P` to inner
product `v`: shift the witness's `g₀`-coefficient by `v`. This is the exact halo2 invariant resolving the
value living on `g₀` (the verifier equation) versus on `U` (the transcript tree). -/
theorem ipaRelation_unshift (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v : F)
    (a : Fin (2 ^ urs.k) → F) (hb0 : b 0 = 1)
    (h : IpaRelation urs (P - v • urs.g 0) b 0 a) :
    IpaRelation urs P b v (a + Pi.single 0 v) := by
  obtain ⟨hc, hi⟩ := h
  refine ⟨?_, ?_⟩
  · rw [commit_add, commit_single, hc]; abel
  · rw [innerProduct_add, innerProduct_single, hi, hb0, mul_one, zero_add]

/-- `commit` is homogeneous: `⟨c • a, G⟩ = c • ⟨a, G⟩`. -/
theorem commit_smul (urs : URS G) (c : F) (a : Fin (2 ^ urs.k) → F) :
    commit urs (c • a) = c • commit urs a := by
  simp only [commit, Pi.smul_apply, smul_assoc, ← Finset.smul_sum]

/-- `innerProduct` is homogeneous in its left argument: `⟨c • s, b⟩ = c · ⟨s, b⟩`. -/
theorem innerProduct_smul {n : ℕ} (c : F) (s b : Fin n → F) :
    innerProduct (c • s) b = c * innerProduct s b := by
  simp only [innerProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

/-- **The synthetic-blinding strip (the opened value, unique under binding).** halo2's IPA folds a synthetic
blinding commitment `[ξ]S` into the opened commitment, with `S = ⟨s, G⟩`. Stripping it — subtract `ξ·s` from
the witness — opens the plain `P` to `v − ξ·⟨s, b⟩`. This is *unconditional*: it reports the opened value
of `P` for the supplied `S`-opening `s` (distinct `S`-openings shift it while exhibiting a `g`-relation —
binding pins it), whatever the blinder is. The verifier never checks `s`; `S` is prover-supplied. So the
soundness content lives in how `v − ξ·⟨s, b⟩` relates to the claimed value, which the caller must pin (see
`ipaRelation_unblind` for the honest-prover case, and `Soundness.Forking` for the `ξ`-randomization that
bounds a malicious blinder). -/
theorem ipaRelation_unblind_value (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v ξ : F)
    (s a : Fin (2 ^ urs.k) → F)
    (h : IpaRelation urs (P + ξ • commit urs s) b v a) :
    IpaRelation urs P b (v - ξ * innerProduct s b) (a - ξ • s) := by
  obtain ⟨hc, hi⟩ := h
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, commit_add, commit_smul, hc, neg_smul]; abel
  · rw [sub_eq_add_neg, ← neg_smul, innerProduct_add, innerProduct_smul, hi]; ring

/-- **The synthetic-blinding strip, honest-prover case.** When the blinder vanishes at the evaluation point
(`⟨s, b⟩ = 0` — halo2's prover sets `s_poly[0] -= s(x₃)` so `s(x₃) = 0`), stripping `[ξ]S` leaves the opened
value at the claimed `v`. This is the `⟨s, b⟩ = 0` specialization of `ipaRelation_unblind_value`; a malicious
prover need not satisfy it, which is exactly why `[ξ]S`'s soundness rests on `ξ` being drawn after `S`
(`Soundness.Forking`), not on this hypothesis. With `ipaRelation_unshift` it reconciles the adjusted
commitment `P' = P − [v]g₀ + [ξ]S` with the plain `P`. -/
theorem ipaRelation_unblind (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v ξ : F)
    (s a : Fin (2 ^ urs.k) → F) (hs : innerProduct s b = 0)
    (h : IpaRelation urs (P + ξ • commit urs s) b v a) :
    IpaRelation urs P b v (a - ξ • s) := by
  have h' := ipaRelation_unblind_value urs P b v ξ s a h
  rwa [hs, mul_zero, sub_zero] at h'

/-! ## The IPA round fold and its 2-special-soundness extractor

One round of the inner-product argument halves the witness. The prover sends the cross-commitments
`(Lⱼ, Rⱼ)`, the verifier sends a challenge `uⱼ`, and the length-`2m` vector folds to length `m`. The
core of special soundness is that the same halves, folded at two distinct challenges, are uniquely
recoverable — so an accepting prover is committed to a fixed witness, which the extractor recovers. -/

/-- One IPA round folds a vector into its lower half plus `u` times its upper half (`compute_s`'s
`(1, uⱼ)` structure): `foldVec lo hi u = lo + u • hi`. The round commitments `(Lⱼ, Rⱼ)` pin `lo`, `hi`. -/
def foldVec {m : ℕ} (lo hi : Fin m → F) (u : F) : Fin m → F := lo + u • hi

/-- The IPA round extractor: from the folded vector at two distinct challenges, recover the halves —
`hi = (f₁ − f₂)/(u₁ − u₂)` and `lo = f₁ − u₁ • hi`. -/
def roundExtract {m : ℕ} (f₁ f₂ : Fin m → F) (u₁ u₂ : F) : (Fin m → F) × (Fin m → F) :=
  (f₁ - u₁ • ((u₁ - u₂)⁻¹ • (f₁ - f₂)), (u₁ - u₂)⁻¹ • (f₁ - f₂))

/-- 2-special soundness of one IPA round: the folded vectors at two distinct challenges `u₁ ≠ u₂`
(produced from the same halves `lo, hi`) determine the halves — `roundExtract` recovers exactly
`(lo, hi)`. A prover answering two challenges consistently is thus committed to a unique pair that folds
back to the round witness, the algebraic heart of the IPA's special soundness. -/
theorem roundExtract_correct {m : ℕ} (lo hi : Fin m → F) (u₁ u₂ : F) (h : u₁ ≠ u₂) :
    roundExtract (foldVec lo hi u₁) (foldVec lo hi u₂) u₁ u₂ = (lo, hi) := by
  have hsub : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h
  have hi_eq : (u₁ - u₂)⁻¹ • (foldVec lo hi u₁ - foldVec lo hi u₂) = hi := by
    have hd : foldVec lo hi u₁ - foldVec lo hi u₂ = (u₁ - u₂) • hi := by
      simp only [foldVec, sub_smul]; abel
    rw [hd, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  simp only [roundExtract, Prod.mk.injEq]
  refine ⟨?_, hi_eq⟩
  rw [hi_eq]
  simp only [foldVec]
  abel

/-! ## Inner-product left-additivity

The scalar side of the IPA. The fact needed downstream is that the inner product is additive in its left
argument (`innerProduct_add_left`) — the algebra the round extractor's witness fold rests on. -/

/-- The inner product is additive in its left argument. -/
theorem innerProduct_add_left {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-! ## Commitment binding and knowledge soundness of the opening

The last ingredient is binding: distinct coefficient vectors have distinct commitments (the URS
generators are `F`-linearly independent). On the Vesta curve this is the discrete-log-relation
(DLR) hardness assumption — kept as an explicit hypothesis (project scope), not proved here,
mirroring how `Zcash/Security/BindingSignature/Balance.lean` records its cryptographic assumptions.

Given binding, the witness the special-soundness extractor produces (`roundExtract_correct` per round,
composed over the `k` rounds) is the unique opening, so an accepting proof demonstrates knowledge of
exactly one polynomial. The complementary constraint layer — that the opened polynomials satisfy the
circuit's gate/permutation/lookup identities — is the Schwartz–Zippel bound
(`Zcash.Snark.fingerprint_schwartz_zippel`): a violated identity passes the random-point check only with
probability `≤ d/p`. -/

/-- Commitment binding (the curve assumption, kept explicit): the URS commitment is injective —
coefficient vectors with equal commitments are equal, i.e. the generators `g` are `F`-linearly
independent. On Vesta this is the discrete-log-relation (DLR) hardness assumption
(`commitmentBinding_iff_no_relation`). -/
@[reducible] def CommitmentBinding (urs : URS G) : Prop :=
  Function.Injective (commit (F := F) urs)

/-- Under binding, the IPA opening is unique: two witnesses opening the same commitment to the same
value are equal. So special-soundness extraction (which yields an opening) pins down the witness. -/
theorem ipaRelation_unique {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → F} {v : F}
    {a a' : Fin (2 ^ urs.k) → F} (hb : CommitmentBinding (F := F) urs)
    (h : IpaRelation urs P b v a) (h' : IpaRelation urs P b v a') : a = a' :=
  hb (h.1.trans h'.1.symm)

end Zcash.Snark
