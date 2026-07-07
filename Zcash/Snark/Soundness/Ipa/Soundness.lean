import Mathlib
import Zcash.Snark.Soundness.Ipa.CommitFold
import Zcash.Snark.Soundness.Ipa.Consistency

/-!
# IPA knowledge soundness: the commitment-soundness of one round (3-special)

This begins the genuine inner-product-argument knowledge-soundness proof — deriving the opening relation
`commit g a = P` from the verifier's accept, rather than assuming it.

The key fact: one IPA round is 3-special-sound for the commitment. At a round the verifier folds
`g' = g_lo + u⁻¹·g_hi` and `P' = P + u⁻¹·L + u·R` (the prover's cross-terms `L`,`R` fixed before the
challenge). Given three sub-openings at three distinct challenges, `commit g' cᵢ = P + uᵢ⁻¹·L + uᵢ·R`, the
parent commitment is pinned: `commit g a = P` for an `a` assembled from the `cᵢ` by the Vandermonde
combination that extracts the linear-in-`u` coefficient. Two challenges suffice to extract the witness but
leave `commit g a − P = (u₁+u₂)·X` undetermined; three kill it.

This round step needs no binding — it is pure module linear algebra. (Binding enters only for uniqueness
of the opening.)

* `vandermonde3` — three distinct points admit coefficients `lᵢ` with `Σ lᵢ uᵢᵏ = δ_{k,1}` (`k=0,1,2`):
  the functional extracting the linear coefficient of a degree-≤2 polynomial from its three samples.
* `ipa_round_commit_sound` — from three sub-openings `commit (g_lo + uᵢ⁻¹·g_hi) cᵢ = P + uᵢ⁻¹·L + uᵢ·R` at
  distinct nonzero challenges, the parent commitment `P` is the commitment of `a = (Σ lᵢuᵢ·cᵢ ‖ Σ lᵢ·cᵢ)`:
  `commit g_lo a_lo + commit g_hi a_hi = P`. Pure module linear algebra (the `vandermonde3` combination),
  no binding.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Three-point linear-coefficient functional. For distinct `u₁,u₂,u₃` there are coefficients
`l₁,l₂,l₃` with `Σ lᵢ = 0`, `Σ lᵢuᵢ = 1`, `Σ lᵢuᵢ² = 0` — i.e. `p ↦ Σ lᵢ·p(uᵢ)` reads off the
coefficient of `u` from any degree-≤2 `p`. (The `lᵢ` are the `u`-coefficients of the Lagrange basis.) -/
theorem vandermonde3 (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) :
    ∃ l₁ l₂ l₃ : F, (l₁ + l₂ + l₃ = 0) ∧ (l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
      ∧ (l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0) := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)), -(u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)),
    -(u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The IPA round is 3-special-sound for the commitment — explicit witness. Given the three folded
openings and Vandermonde coefficients `lᵢ` (the `vandermonde3` solution), the explicit parent witness
`a = (Σ lᵢuᵢ·cᵢ ‖ Σ lᵢ·cᵢ)` opens `P`: `commit g_lo a_lo + commit g_hi a_hi = P`.

The proof multiplies each opening by `uᵢ` to clear the inverse (`uᵢ·A_i + B_i = uᵢ·P + L + uᵢ²·R`), then
combines by `lᵢ`: the `P`-coefficient becomes `Σ lᵢuᵢ = 1`, while `L` (`Σ lᵢ = 0`) and `R`
(`Σ lᵢuᵢ² = 0`) cancel, and the `cᵢ`-terms cancel pairwise. No binding. The witness is explicit, not
existential, so the same witness can be reused for the inner-product side at `G := F`. -/
theorem ipa_round_commit_with_coeffs {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ l₁ l₂ l₃ : F)
    (hl0 : l₁ + l₂ + l₃ = 0) (hl1 : l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
    (hl2 : l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁⁻¹ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂⁻¹ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃⁻¹ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    commitGen g_lo (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃))
      + commitGen g_hi (l₁ • c₁ + l₂ • c₂ + l₃ • c₃) = P := by
  rw [commitGen_add_gen, commitGen_smul_gen] at e₁ e₂ e₃
  have s₁ : u₁ • commitGen g_lo c₁ + commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R := by
    have h := congrArg (u₁ • ·) e₁
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₁, one_smul] at h; exact h
  have s₂ : u₂ • commitGen g_lo c₂ + commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R := by
    have h := congrArg (u₂ • ·) e₂
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₂, one_smul] at h; exact h
  have s₃ : u₃ • commitGen g_lo c₃ + commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R := by
    have h := congrArg (u₃ • ·) e₃
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₃, one_smul] at h; exact h
  have hB₁ : commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R - u₁ • commitGen g_lo c₁ := by
    rw [← s₁]; abel
  have hB₂ : commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R - u₂ • commitGen g_lo c₂ := by
    rw [← s₂]; abel
  have hB₃ : commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R - u₃ • commitGen g_lo c₃ := by
    rw [← s₃]; abel
  simp only [commitGen_add_left, commitGen_smul_left, hB₁, hB₂, hB₃]
  match_scalars <;>
    first
      | linear_combination hl1
      | linear_combination hl0
      | linear_combination hl2
      | ring

/-- The IPA round is 3-special-sound for the commitment. Three sub-openings at distinct nonzero
challenges pin the parent opening: `∃ a_lo a_hi, commit g_lo a_lo + commit g_hi a_hi = P`. The existential
form; the witness is the `vandermonde3` combination (`ipa_round_commit_with_coeffs`). No binding. -/
theorem ipa_round_commit_sound {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ : F)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁⁻¹ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂⁻¹ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃⁻¹ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    ∃ a_lo a_hi : Fin m → F, commitGen g_lo a_lo + commitGen g_hi a_hi = P := by
  obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
  exact ⟨_, _, ipa_round_commit_with_coeffs g_lo g_hi P L R c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
    hl0 hl1 hl2 hu₁ hu₂ hu₃ e₁ e₂ e₃⟩

/-- A length-`2^{k+1}` commitment splits over the two halves:
`commit g a = commit (loHalf g) (loHalf a) + commit (hiHalf g) (hiHalf a)`. The IPA recursion's bridge from
a round's folded-generator openings back to the parent generators. -/
theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- The lower half of an `append` is the lower part. -/
theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : loHalf (append lo hi) = lo := by
  funext i; simp only [loHalf, append, dif_pos i.isLt]

/-- The upper half of an `append` is the upper part. -/
theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1; apply Fin.ext; simp

/-- A commitment of an `append` splits over the parent halves:
`commit g (append a_lo a_hi) = commit (loHalf g) a_lo + commit (hiHalf g) a_hi`. -/
theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
    commitGen g (append a_lo a_hi) = commitGen (loHalf g) a_lo + commitGen (hiHalf g) a_hi := by
  rw [commitGen_split, loHalf_append, hiHalf_append]

/-! ## The IPA soundness recursion -/

/-- A 3-ary IPA transcript tree for `d` rounds. At each round the prover's two cross-commitments
`L`, `R` (fixed before the challenge) and three sub-transcripts answering three challenges; at a leaf the
final scalar. The 3-arity is what `ipa_round_commit_sound` consumes (two challenges extract the witness,
the third pins the commitment). -/
inductive IpaTree (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTree F G 0
  | node {d : ℕ} : G → G → F → F → F →
      IpaTree F G d → IpaTree F G d → IpaTree F G d → IpaTree F G (d + 1)

/-- The IPA verifier accepts a transcript tree against generators `g` and commitment `P`: at a leaf,
the final check `P = [c]·g₀` (`= commit g (const c)`); at a node, the three challenges are distinct and
nonzero and each sub-transcript opens the verifier's folded commitment `P + uᵢ⁻¹·L + uᵢ·R` against the
folded generators `foldGens g uᵢ`. This is the verifier's recursion (external `P`, prover `L`/`R`), the
object the soundness peels back. -/
def IpaAccept : {d : ℕ} → (Fin (2 ^ d) → G) → G → IpaTree F G d → Prop
  | 0, g, P, .leaf c => P = commitGen g (fun _ => c)
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAccept (foldGens g u₁) (P + u₁⁻¹ • L + u₁ • R) t₁ ∧
        IpaAccept (foldGens g u₂) (P + u₂⁻¹ • L + u₂ • R) t₂ ∧
        IpaAccept (foldGens g u₃) (P + u₃⁻¹ • L + u₃ • R) t₃

/-- IPA knowledge soundness — the opening, derived (not assumed). An accepting transcript tree yields a
witness opening the commitment: `∃ a, commit g a = P`. By induction on the tree: the leaf gives `a = const c`
directly; a node takes the three sub-witnesses from the IH, pins the parent commitment with
`ipa_round_commit_sound`, and reassembles via `commitGen_append`. The whole argument uses no binding —
3-special soundness alone pins the opening. (Binding/DLR enters only for uniqueness, `ipaRelation_unique`.) -/
theorem ipa_sound : {d : ℕ} → (g : Fin (2 ^ d) → G) → (P : G) → (t : IpaTree F G d) →
    IpaAccept g P t → ∃ a : Fin (2 ^ d) → F, commitGen g a = P
  | 0, g, P, .leaf c, h => ⟨fun _ => c, h.symm⟩
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hc₁⟩ := ipa_sound (foldGens g u₁) _ t₁ ha₁
      obtain ⟨c₂, hc₂⟩ := ipa_sound (foldGens g u₂) _ t₂ ha₂
      obtain ⟨c₃, hc₃⟩ := ipa_sound (foldGens g u₃) _ t₃ ha₃
      obtain ⟨a_lo, a_hi, hP⟩ := ipa_round_commit_sound (loHalf g) (hiHalf g) P L R c₁ c₂ c₃
        u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ hc₁ hc₂ hc₃
      exact ⟨append a_lo a_hi, by rw [commitGen_append]; exact hP⟩

/-! ## The full opening relation (commitment + inner product)

The inner product `⟨a, b⟩ = v` is the same theorem at `G := F`: `commitGen b a = ∑ aⱼ • bⱼ = ⟨a, b⟩`, so
the eval vector `b` plays the role of the generators and the value `v` the role of the commitment, with the
verifier folding `b` by `foldGens` exactly as it folds `g` (`innerProduct_round`). Carrying both in one
tree and reusing `ipa_round_commit_with_coeffs` for each (with the same explicit witness) derives the full
`IpaRelation`. -/

/-- A 3-ary IPA transcript tree carrying both the commitment cross-terms `L`,`R` (in `G`) and the
inner-product cross-terms `Lv`,`Rv` (in `F`) per round. -/
inductive IpaTreeV (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTreeV F G 0
  | node {d : ℕ} : G → G → F → F → F → F → F →
      IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G (d + 1)

/-- Acceptance for the full relation: the verifier folds the generators `g` and the eval vector `b` (both
by `foldGens`), the commitment `P` (by `L`,`R`) and the value `v` (by `Lv`,`Rv`); the leaf checks
`P = [c]·g₀` and `v = c·b₀`. -/
def IpaAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → F → IpaTreeV F G d → Prop
  | 0, g, b, P, v, .leaf c => P = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c)
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAcceptV (foldGens g u₁) (foldGens b u₁) (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) t₁ ∧
        IpaAcceptV (foldGens g u₂) (foldGens b u₂) (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) t₂ ∧
        IpaAcceptV (foldGens g u₃) (foldGens b u₃) (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) t₃

/-- Full IPA knowledge soundness — the opening relation, derived from acceptance. An accepting transcript
tree yields a single witness `a` that both opens the commitment and gives the claimed inner product:
`∃ a, commit g a = P ∧ commit b a = v` (and `commit b a = ⟨a, b⟩`). The two conjuncts share the same `a`
— the explicit Vandermonde combination — by applying `ipa_round_commit_with_coeffs` to the commitment
(`G`) and the inner product (`G := F`, generators `b`) with one set of coefficients. Binding-free. This is
`IpaRelation` (`commit a = P ∧ ⟨a,b⟩ = v`) discharged from the verifier's accept. -/
theorem ipa_soundV : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v : F) →
    (t : IpaTreeV F G d) → IpaAcceptV g b P v t →
    ∃ a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v
  | 0, g, b, P, v, .leaf c, h => ⟨fun _ => c, h.1.symm, h.2.symm⟩
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hP₁, hv₁⟩ := ipa_soundV (foldGens g u₁) (foldGens b u₁) _ _ t₁ ha₁
      obtain ⟨c₂, hP₂, hv₂⟩ := ipa_soundV (foldGens g u₂) (foldGens b u₂) _ _ t₂ ha₂
      obtain ⟨c₃, hP₃, hv₃⟩ := ipa_soundV (foldGens g u₃) (foldGens b u₃) _ _ t₃ ha₃
      obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
      refine ⟨append (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃)) (l₁ • c₁ + l₂ • c₂ + l₃ • c₃),
        ?_, ?_⟩
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf g) (hiHalf g) P L R c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
          hl0 hl1 hl2 hu₁ hu₂ hu₃ hP₁ hP₂ hP₃
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf b) (hiHalf b) v Lv Rv c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
          hl0 hl1 hl2 hu₁ hu₂ hu₃ hv₁ hv₂ hv₃

/-! ## The multiopen batch decode

The deployed verifier batches the per-column commitments by powers of a challenge `z` (the `x₁`/`x₄`
folds), opens the single batched commitment, and the inner-product argument extracts the combined witness.
To recover the individual column openings — what the gate check needs — one rewinds the batching challenge
and solves a Vandermonde system over `n` distinct `z`'s: the `ipa_soundV` technique one layer up, but with
no cross terms (the batch is a plain linear combination), so a single `n`-point Vandermonde inverse
suffices. -/

/-- General Vandermonde inverse. For `n` distinct points `z`, there are coefficients `μ` with
`Σ_k μ i k · (z k)ʲ = δ_{i,j}` — the functional reading off the `i`-th coefficient of a degree-`<n`
polynomial from its `n` samples. (The `n = 3` special case is `vandermonde3`.) From invertibility of the
Vandermonde matrix (`det = ∏_{i<j}(z j − z i) ≠ 0` for distinct points). -/
theorem vandermonde_inv {n : ℕ} (z : Fin n → F) (hz : Function.Injective z) :
    ∃ μ : Fin n → Fin n → F, ∀ (i j : Fin n), (∑ k, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  refine ⟨fun i k => (Matrix.vandermonde z)⁻¹ i k, fun i j => ?_⟩
  have hmul : (Matrix.vandermonde z)⁻¹ * Matrix.vandermonde z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- A length-`m` commitment is additive over a finite sum of witnesses. -/
theorem commitGen_sum {m : ℕ} (g : Fin m → G) {ι : Type*} (s : Finset ι) (f : ι → Fin m → F) :
    commitGen g (∑ k ∈ s, f k) = ∑ k ∈ s, commitGen g (f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [commitGen]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, commitGen_add_left, ih]

/-- Batch-opening soundness — explicit witness. Given the batched openings
`commit g (a k) = Σⱼ (z k)ʲ · C j` at the `n` challenges and the Vandermonde coefficients `μ`, the explicit
combination `Σ_k μ i k · a k` opens the `i`-th individual commitment: `commit g (Σ_k μ i k · a k) = C i`. -/
theorem batch_open_with_coeffs {m n : ℕ} (g : Fin m → G) (C : Fin n → G) (z : Fin n → F)
    (a : Fin n → (Fin m → F)) (μ : Fin n → Fin n → F)
    (hμ : ∀ (i j : Fin n), (∑ k, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0)
    (ha : ∀ k, commitGen g (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • C j) (i : Fin n) :
    commitGen g (∑ k, μ i k • a k) = C i := by
  rw [commitGen_sum]
  simp only [commitGen_smul_left, ha, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- The multiopen batch decode is sound. From the batched commitment/value openings at `n` distinct
challenges, each individual column has a single witness opening it to its commitment `C i` and giving its
claimed evaluation `e i`: `∃ col, ∀ i, commit g (col i) = C i ∧ ⟨col i, b⟩ = e i`. The same explicit
Vandermonde combination serves both (the value side is `batch_open_with_coeffs` at `G := F`,
`commit b = ⟨·,b⟩`). This recovers the per-column openings the gate check (`circuitSatViaGates`) consumes —
the multiopen decode, derived. -/
theorem batch_open_soundV {m n : ℕ} (g : Fin m → G) (b : Fin m → F) (C : Fin n → G) (e : Fin n → F)
    (z : Fin n → F) (hz : Function.Injective z) (a : Fin n → (Fin m → F))
    (haC : ∀ k, commitGen g (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • C j)
    (hae : ∀ k, commitGen b (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • e j) :
    ∃ col : Fin n → (Fin m → F), ∀ i, commitGen g (col i) = C i ∧ commitGen b (col i) = e i := by
  obtain ⟨μ, hμ⟩ := vandermonde_inv z hz
  exact ⟨fun i => ∑ k, μ i k • a k, fun i =>
    ⟨batch_open_with_coeffs g C z a μ hμ haC i, batch_open_with_coeffs b e z a μ hμ hae i⟩⟩

end Zcash.Snark
