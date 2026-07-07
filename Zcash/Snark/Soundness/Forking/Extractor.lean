import Zcash.Snark.Soundness.Ipa.Soundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Forking.Tree
import Zcash.Snark.Soundness.Forking.Probability

/-!
# The deployed special-soundness extractor (Fiat-Shamir forking, part 2)

Building `ForkAccept` from the forking output needs each node's value/blinding cross-terms `Lv/Rv/Lw/Rw`
recovered from the three accepting continuations. `ipa_round_commit_with_coeffs` already *cancels* arbitrary
`L`/`R` cross-terms by Vandermonde and recovers the parent commitment; this module supplies the *recovery*
counterpart for the scalar value/blinding fold: given the three folded scalars at distinct nonzero
challenges, the parent scalar and its two cross-terms exist and interpolate them.

`vandermonde3_recover` is the scalar 3-special-soundness step: the linear map
`(v, Lv, Rv) ↦ (v + uᵢ⁻¹·Lv + uᵢ·Rv)ᵢ` is injective at three distinct nonzero challenges (a quadratic with
three roots is zero), hence surjective, so any triple of folded values is hit.
-/

namespace Zcash.Snark

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- **Group 3-special-soundness recovery.** Given target folded commitments `P₁,P₂,P₃ : G` at three distinct
nonzero challenges, there is a parent commitment `P` and cross-terms `L, R : G` with `P + uᵢ⁻¹•L + uᵢ•R = Pᵢ`.
The commitment counterpart of `vandermonde3_recover`: the bottom-up extractor recovers each node's commitment
and its two cross-terms from the three accepting continuations (the explicit Lagrange combination of the
`Pᵢ`, with the same coefficients as the scalar recovery). -/
theorem vandermonde3_recover_group {u₁ u₂ u₃ : F}
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (P₁ P₂ P₃ : G) :
    ∃ P L R : G, P + u₁⁻¹ • L + u₁ • R = P₁ ∧ P + u₂⁻¹ • L + u₂ • R = P₂
      ∧ P + u₃⁻¹ • L + u₃ • R = P₃ := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨(-(u₁ * (u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)))) • P₁
            + (-(u₂ * (u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)))) • P₂
            + (-(u₃ * (u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)))) • P₃,
          (u₁ * (u₂ * u₃) / ((u₁ - u₂) * (u₁ - u₃))) • P₁
            + (u₂ * (u₁ * u₃) / ((u₂ - u₁) * (u₂ - u₃))) • P₂
            + (u₃ * (u₁ * u₂) / ((u₃ - u₁) * (u₃ - u₂))) • P₃,
          (u₁ / ((u₁ - u₂) * (u₁ - u₃))) • P₁
            + (u₂ / ((u₂ - u₁) * (u₂ - u₃))) • P₂
            + (u₃ / ((u₃ - u₁) * (u₃ - u₂))) • P₃, ?_, ?_, ?_⟩ <;>
    match_scalars <;> field_simp <;> ring

/-- **Uniqueness of the per-round recovery.** The fold map `(P, L, R) ↦ (P + uᵢ⁻¹•L + uᵢ•R)ᵢ` is injective at
three distinct nonzero challenges: two roots folding to the same three children are equal. (A degree-≤2 system
with an invertible Vandermonde matrix has a unique solution.) This pins the bottom-up recovered root — it is
*the* instance consistent with the children, so it matches whatever the deployed verifier equation pins. -/
theorem fold_inj {u₁ u₂ u₃ : F} (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0) {P L R P' L' R' : G}
    (e₁ : P + u₁⁻¹ • L + u₁ • R = P' + u₁⁻¹ • L' + u₁ • R')
    (e₂ : P + u₂⁻¹ • L + u₂ • R = P' + u₂⁻¹ • L' + u₂ • R')
    (e₃ : P + u₃⁻¹ • L + u₃ • R = P' + u₃⁻¹ • L' + u₃ • R') :
    P = P' ∧ L = L' ∧ R = R' := by
  -- clear the inverses: fᵢ : uᵢ•(P-P') + (L-L') + (uᵢ*uᵢ)•(R-R') = 0
  have f : ∀ u : F, u ≠ 0 → (P + u⁻¹ • L + u • R = P' + u⁻¹ • L' + u • R') →
      u • (P - P') + (L - L') + (u * u) • (R - R') = 0 := by
    intro u hu e
    have h := congrArg (u • ·) (sub_eq_zero.mpr e)
    simp only [smul_zero, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hu, one_smul] at h
    rw [← h]; module
  have f₁ := f u₁ hu₁ e₁
  have f₂ := f u₂ hu₂ e₂
  have f₃ := f u₃ hu₃ e₃
  -- eliminate (L-L'): subtract pairs and factor out the nonzero difference
  have g : ∀ u v : F, u ≠ v →
      u • (P - P') + (u * u) • (R - R') = v • (P - P') + (v * v) • (R - R') →
      (P - P') + (u + v) • (R - R') = 0 := by
    intro u v huv e
    have hd : u - v ≠ 0 := sub_ne_zero.mpr huv
    have : (u - v) • ((P - P') + (u + v) • (R - R')) = 0 := by
      rw [← sub_eq_zero] at e; rw [← e]; module
    exact (smul_eq_zero.mp this).resolve_left hd
  have g12 : (P - P') + (u₁ + u₂) • (R - R') = 0 := g u₁ u₂ h12 (by linear_combination (norm := module) f₁ - f₂)
  have g13 : (P - P') + (u₁ + u₃) • (R - R') = 0 := g u₁ u₃ h13 (by linear_combination (norm := module) f₁ - f₃)
  -- (u₂ - u₃)•(R-R') = 0 ⟹ R = R'
  have hR : R - R' = 0 := by
    have hd : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
    have : (u₂ - u₃) • (R - R') = 0 := by linear_combination (norm := module) g12 - g13
    exact (smul_eq_zero.mp this).resolve_left hd
  have hP : P - P' = 0 := by linear_combination (norm := module) g12 - (u₁ + u₂) • hR
  have hL : L - L' = 0 := by linear_combination (norm := module) f₁ - u₁ • hP - (u₁ * u₁) • hR
  exact ⟨sub_eq_zero.mp hP, sub_eq_zero.mp hL, sub_eq_zero.mp hR⟩

/-- **Scalar 3-special-soundness recovery.** Given target folded values `t₁, t₂, t₃` at three distinct
nonzero challenges, there is a parent value `v` and cross-terms `Lv, Rv` with `v + uᵢ⁻¹·Lv + uᵢ·Rv = tᵢ`.
The value/blinding counterpart of `ipa_round_commit_with_coeffs`: the deployed tree's per-node `Lv/Rv`
(resp. `Lw/Rw`) are pinned by the three accepting continuations. -/
theorem vandermonde3_recover {u₁ u₂ u₃ : F}
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (t₁ t₂ t₃ : F) :
    ∃ v Lv Rv : F, v + u₁⁻¹ * Lv + u₁ * Rv = t₁ ∧ v + u₂⁻¹ * Lv + u₂ * Rv = t₂
      ∧ v + u₃⁻¹ * Lv + u₃ * Rv = t₃ := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₁ * t₁ * (u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ * (u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ * (u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂))),
          u₁ * t₁ * (u₂ * u₃) / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ * (u₁ * u₃) / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ * (u₁ * u₂) / ((u₃ - u₁) * (u₃ - u₂)),
          u₁ * t₁ / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;>
    field_simp <;> ring

/-! ## The root-consistent producer: threading the deployed commitment

To pin the extracted root to the deployed commitment — rather than a *free* root, disconnected from the
deployed instance — we thread the deployed commitment-*whole* `Pwhole = P + [z·v]U + [blind]W` top-down.
`DForkCert`/`DeployedForkValid` carry, at each node, the prover's round point `(L, R)` (the rewound
transcript's commitment) so the whole folds by it; at each leaf they assert the flat verifier leaf equation
for the folded whole. The producer `produceDeployed` recovers the cross-terms bottom-up by Vandermonde and
additionally proves the recovered root whole *equals* `Pwhole`: the recovered whole and `Pwhole` fold to the
same three child wholes, so `fold_inj` forces them equal. This is root consistency — the residual collapses to
supplying `DeployedForkValid` (the rewinding) and Blake2b. -/

/-- A deployed forking certificate: the prover's round point `(L, R)` at each node (the rewound transcript's
commitment), the three challenges, and the final opening `(c, f)` at each leaf. It carries the round points,
so the deployed commitment-whole can be folded by them top-down rather than recovered. -/
inductive DForkCert (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → DForkCert F G 0
  | node {d : ℕ} : G → G → F → F → F →
      DForkCert F G d → DForkCert F G d → DForkCert F G d → DForkCert F G (d + 1)

/-- The deployed forking acceptance condition: the deployed commitment-whole `Pwhole`, folded by the prover's
round points `(L, R)` down each path, satisfies the flat verifier leaf equation
`Pwhole = ⟨c,g⟩ + [z·⟨c,b⟩]U + [f]W` at every leaf (with distinct nonzero challenges at each node). The forking
output stated *about the deployed instance* — the rewound transcripts accept against the threaded deployed
commitment, with no decomposition posited. -/
def DeployedForkValid : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (U W : G) → (z : F) → G →
    DForkCert F G d → Prop
  | 0, g, b, U, W, z, Pwhole, .leaf c f =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, g, b, U, W, z, Pwhole, .node L R u₁ u₂ u₃ c₁ c₂ c₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        DeployedForkValid (foldGens g u₁) (foldGens b u₁) U W z (Pwhole + u₁⁻¹ • L + u₁ • R) c₁ ∧
        DeployedForkValid (foldGens g u₂) (foldGens b u₂) U W z (Pwhole + u₂⁻¹ • L + u₂ • R) c₂ ∧
        DeployedForkValid (foldGens g u₃) (foldGens b u₃) U W z (Pwhole + u₃⁻¹ • L + u₃ • R) c₃

/-- **The root-consistent deployed producer.** Threading the deployed commitment-whole `Pwhole`, a valid
deployed forking output yields a transcript tree with `DeployedIpaAcceptV` whose recovered root whole
`P + [z·v]U + [blind]W` is *exactly* `Pwhole`. The cross-terms are recovered bottom-up by Vandermonde; the
root whole is pinned by `fold_inj` — it and `Pwhole` fold to the same three child
wholes (the recursion's invariant), so they coincide. No posited decomposition, and the root is the deployed
commitment, not a free one: root consistency, proven. -/
theorem produceDeployed {U W : G} {z : F} : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
    (Pwhole : G) → (cert : DForkCert F G d) → DeployedForkValid g b U W z Pwhole cert →
    ∃ (P : G) (v blind : F) (t : DeployedIpaTreeV F G d),
      DeployedIpaAcceptV g b U W z P v blind t ∧ P + (z * v) • U + blind • W = Pwhole
  | 0, g, b, Pwhole, .leaf c f, hv =>
      ⟨commitGen g (fun _ => c), commitGen b (fun _ => c), f, .leaf c f, ⟨fun _ => c, rfl, rfl⟩, hv.symm⟩
  | d + 1, g, b, Pwhole, .node L R u₁ u₂ u₃ c₁ c₂ c₃, hv => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩ := hv
      obtain ⟨P₁, v₁, bl₁, t₁, ha₁, hw₁⟩ := produceDeployed (foldGens g u₁) (foldGens b u₁) _ c₁ hv₁
      obtain ⟨P₂, v₂, bl₂, t₂, ha₂, hw₂⟩ := produceDeployed (foldGens g u₂) (foldGens b u₂) _ c₂ hv₂
      obtain ⟨P₃, v₃, bl₃, t₃, ha₃, hw₃⟩ := produceDeployed (foldGens g u₃) (foldGens b u₃) _ c₃ hv₃
      obtain ⟨P, L', R', eP₁, eP₂, eP₃⟩ := vandermonde3_recover_group h12 h13 h23 hu₁ hu₂ hu₃ P₁ P₂ P₃
      obtain ⟨v, Lv, Rv, ev₁, ev₂, ev₃⟩ := vandermonde3_recover h12 h13 h23 hu₁ hu₂ hu₃ v₁ v₂ v₃
      obtain ⟨blind, Lw, Rw, eb₁, eb₂, eb₃⟩ := vandermonde3_recover h12 h13 h23 hu₁ hu₂ hu₃ bl₁ bl₂ bl₃
      refine ⟨P, v, blind, .node L' R' Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃,
        ⟨h12, h13, h23, hu₁, hu₂, hu₃, ?_, ?_, ?_⟩, ?_⟩
      · simp only [smul_eq_mul]; rw [eP₁, ev₁, eb₁]; exact ha₁
      · simp only [smul_eq_mul]; rw [eP₂, ev₂, eb₂]; exact ha₂
      · simp only [smul_eq_mul]; rw [eP₃, ev₃, eb₃]; exact ha₃
      · -- the recovered root whole and `Pwhole` fold to the same three child wholes ⇒ equal (`fold_inj`)
        have key : ∀ (uu : F) (Pi : G) (vi bli : F),
            P + uu⁻¹ • L' + uu • R' = Pi → v + uu⁻¹ * Lv + uu * Rv = vi →
            blind + uu⁻¹ * Lw + uu * Rw = bli → Pi + (z * vi) • U + bli • W = Pwhole + uu⁻¹ • L + uu • R →
            (P + (z * v) • U + blind • W) + uu⁻¹ • (L' + (z * Lv) • U + Lw • W)
                + uu • (R' + (z * Rv) • U + Rw • W) = Pwhole + uu⁻¹ • L + uu • R := by
          intro uu Pi vi bli hP hvv hb hw
          rw [show (P + (z * v) • U + blind • W) + uu⁻¹ • (L' + (z * Lv) • U + Lw • W)
                + uu • (R' + (z * Rv) • U + Rw • W)
              = (P + uu⁻¹ • L' + uu • R') + (z * (v + uu⁻¹ * Lv + uu * Rv)) • U
                + (blind + uu⁻¹ * Lw + uu * Rw) • W from by match_scalars <;> ring,
            hP, hvv, hb, hw]
        exact (fold_inj h12 h13 h23 hu₁ hu₂ hu₃
          (key u₁ P₁ v₁ bl₁ eP₁ ev₁ eb₁ hw₁) (key u₂ P₂ v₂ bl₂ eP₂ ev₂ eb₂ hw₂)
          (key u₃ P₃ v₃ bl₃ eP₃ ev₃ eb₃ hw₃)).1

/-- **Root-consistent extraction (the deployed `FiatShamirTree`).** Threading the deployed commitment-whole
`⟨aDep, g⟩ + [z·vDep]U + [blindDep]W`, a valid deployed forking output yields the deployed accept predicate
for the deployed commitment `⟨aDep, g⟩` and value `vDep` *themselves* — or a nontrivial `(g, U, W)` relation.
`produceDeployed` gives a tree whose recovered root whole equals the deployed whole; extracting that root's
opening (`deployed_to_acceptV`/`ipa_soundV`) and matching it against the deployed whole (`separate_or_relation`
— the binding branch) forces the recovered `(P, v)` to *be* the deployed `(⟨aDep,g⟩, vDep)`. So the extracted
tree opens the deployed commitment, not a free one: root consistency, with no posited decomposition. The
residual is supplying `DeployedForkValid` (the rewinding) and the binding/Blake2b floor. -/
theorem deployed_forking_tree {U W : G} {z : F} (hz : z ≠ 0) {d : ℕ}
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (aDep : Fin (2 ^ d) → F) (vDep blindDep : F)
    (cert : DForkCert F G d)
    (hv : DeployedForkValid g b U W z (commitGen g aDep + (z * vDep) • U + blindDep • W) cert) :
    (∃ (blind : F) (t : DeployedIpaTreeV F G d),
        DeployedIpaAcceptV g b U W z (commitGen g aDep) vDep blind t)
      ∨ HasNontrivialRelation (F := F) g U W := by
  obtain ⟨P, v, blind, t, ha, hw⟩ := produceDeployed g b _ cert hv
  rcases deployed_to_acceptV hz g b P v blind t ha with hclean | hrel
  · obtain ⟨a, hPa, hva⟩ := ipa_soundV g b P v (projTree t) hclean
    rw [← hPa, ← hva] at hw
    rcases separate_or_relation g U W a aDep (z * commitGen b a) (z * vDep) blind blindDep hw
      with ⟨haa, hU, _⟩ | hrel
    · refine Or.inl ⟨blind, t, ?_⟩
      have hPP : P = commitGen g aDep := by rw [← hPa, haa]
      have hvv : v = vDep := by rw [← hva]; exact mul_left_cancel₀ hz hU
      rw [hPP, hvv] at ha; exact ha
    · exact Or.inr hrel
  · exact Or.inr hrel

/-! ## The prover-as-oracle-function model: from the abstract forking tree to `DeployedForkValid`

`extractable_of_prob` (`Soundness.Forking.Probability`) gives a *bare* `(3,…,3)` challenge tree (`Extractable`)
once the accept probability beats the knowledge error. To feed `produceDeployed`/`deployed_forking_tree`, that
abstract tree must be filled with the prover's round points and openings — the data a `DForkCert` records.

`Prover` is the prover's strategy as a tree: at each round the cross-commitment `(L, R)` it sends *before* the
challenge, then a continuation per challenge; at the leaf its final opening `(c, f)`. The tree shape enforces
that the round point depends only on the prefix (the challenges already sent) — exactly the Fiat-Shamir
prover-as-oracle-function structure, with the round point committed before the next challenge is squeezed.

`proverAccept` reads off the deployed accept condition along one challenge path: fold the deployed
commitment-whole by the prover's round points down the path and check the flat verifier leaf equation.
`proverAccept_forkValid` is the assembly: any `Extractable` tree for that accept predicate *is* a valid
`DeployedForkValid` certificate — zip the prover's round points/openings with the tree's challenges. This is
the deterministic bridge from the probabilistic forking tree to the deployed forking output; what stays the
floor is that the *deployed* prover realizes this `Prover`/`proverAccept` shape (the faithful transcript
model) and Blake2b-as-random-oracle. -/

/-- A prover's strategy tree for the `d`-round IPA: at each round the cross-commitment `(L, R)` it sends
*before* the challenge, then a continuation per challenge; at the leaf its final opening `(c, f)`. The tree
shape enforces the Fiat-Shamir prefix-determination — the round point is fixed before the challenge. -/
inductive Prover (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → Prover F G 0
  | node {d : ℕ} : G → G → (F → Prover F G d) → Prover F G (d + 1)

/-- The deployed accept condition along one challenge path `χ`: fold the deployed commitment-whole `Pwhole` by
the prover's round points down `χ` (and the generators/eval-vector accordingly), then check the flat verifier
leaf equation `Pwhole = ⟨c,g⟩ + [z·⟨c,b⟩]U + [f]W` at the bottom. The single-path version of
`DeployedForkValid`, indexed by the prover strategy. -/
def proverAccept : {d : ℕ} → Prover F G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (U W : G) → (z : F) → G →
    (Fin d → F) → Prop
  | 0, .leaf c f, g, b, U, W, z, Pwhole, _ =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, .node L R cont, g, b, U, W, z, Pwhole, χ =>
      proverAccept (cont (χ 0)) (foldGens g (χ 0)) (foldGens b (χ 0)) U W z
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-- **The prover-as-oracle assembly.** A `(3,…,3)` `Extractable` tree for the prover's accept predicate yields
a valid `DeployedForkValid` certificate: zip the prover's round points and openings with the tree's distinct
challenges. By recursion on the prover/tree — each node takes its round point from the prover and its three
challenges from `Extractable`, each leaf its opening from the prover, and the per-leaf accept conditions are
exactly `Extractable`'s. This bridges the probabilistic forking tree (`extractable_of_prob`) to the deployed
forking output that `deployed_forking_tree` consumes. -/
theorem proverAccept_forkValid {U W : G} {z : F} : {d : ℕ} → (P : Prover F G d) → (g : Fin (2 ^ d) → G) →
    (b : Fin (2 ^ d) → F) → (Pwhole : G) → Extractable (proverAccept P g b U W z Pwhole) →
    ∃ cert : DForkCert F G d, DeployedForkValid g b U W z Pwhole cert
  | 0, .leaf c f, g, b, Pwhole, hext => ⟨.leaf c f, hext⟩
  | d + 1, .node L R cont, g, b, Pwhole, hext => by
      obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃, e₁, e₂, e₃⟩ := hext
      obtain ⟨cert₁, hv₁⟩ := proverAccept_forkValid (cont u₁) (foldGens g u₁) (foldGens b u₁)
        (Pwhole + u₁⁻¹ • L + u₁ • R) e₁
      obtain ⟨cert₂, hv₂⟩ := proverAccept_forkValid (cont u₂) (foldGens g u₂) (foldGens b u₂)
        (Pwhole + u₂⁻¹ • L + u₂ • R) e₂
      obtain ⟨cert₃, hv₃⟩ := proverAccept_forkValid (cont u₃) (foldGens g u₃) (foldGens b u₃)
        (Pwhole + u₃⁻¹ • L + u₃ • R) e₃
      exact ⟨.node L R u₁ u₂ u₃ cert₁ cert₂ cert₃,
        h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩

end Zcash.Snark
