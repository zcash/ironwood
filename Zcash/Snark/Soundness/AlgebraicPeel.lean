import Zcash.Snark.Soundness.DeployedIpaPeel
import Zcash.Snark.Soundness.AGMProbability

/-!
# Algebraic-prover model: explicit relation witnesses from prover representations

This module is the algebraic-group-model input side of issue #15(1). `Soundness.DeployedIpaPeel`
peels the deployed IPA to `IpaAcceptV ∨ HasNontrivialRelation` — the relation branch is an
*existential* `Prop`, so extracting a usable witness for the DL reduction (`Soundness.AGMProbability`)
otherwise needs `Classical.choice` (`relationWitnessOfHasNontrivialRelation`), which has no
computational content.

Here the prover is modelled as **algebraic**: its group outputs carry representations over the URS
generators as *data*. `AlgebraicDeployedAcceptV` is the data-carrying accept (the folded commitment's
representation `aP` is a subtype field, not `∃ aP`). The peel then returns an **explicit**
`AugmentedRelationWitness` — whose coefficients are literally the prover's representation difference
`aP - honest` — with no `Classical.choice`:

* `separateOrRelationWitness` / `relationOfFoldGensWitness` / `deployedLeafPeelWitness` — data-carrying
  analogues of the `Soundness.BindingReduction` / `Soundness.DeployedIpaPeel` steps.
* `deployedToAcceptVWitness` — the recursive peel, returning `IpaAcceptV ⊕' AugmentedRelationWitness`.
* `algebraicRelationOfDeployedAccept` — bridges the explicit witness into the
  `AlgebraicRelationWitness (augmentedBasis g U W)` that the probability wrapper's reduction consumes.

This closes the algebraic-prover half of #15(1) at the peel level: a binding failure yields an
explicit relation from the prover's representations. What is **not** done here is threading the
data-carrying accept through the Fiat–Shamir/forking layer (`Soundness.Forking`) up to the top-level
Vesta capstones — those still conclude the existential `HasNontrivialRelation`; that end-to-end
re-threading is mechanical but sizeable and remains future work.
-/

open Classical
namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Data version of `separate_or_relation`: the relation witness coefficients are the explicit
difference `a - a'` (from the prover's representation), not a `Classical.choose` of the existential
`HasNontrivialRelation`. -/
noncomputable def separateOrRelationWitness {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ⊕' AugmentedRelationWitness (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact PSum.inl h
  · refine PSum.inr ⟨a - a', α - α', β - β', ?_, ?_⟩
    · rcases Classical.em (a = a') with ha | ha
      · rcases Classical.em (α = α') with hα | hα
        · exact Or.inr (Or.inr (sub_ne_zero.mpr (fun hβ => h ⟨ha, hα, hβ⟩)))
        · exact Or.inr (Or.inl (sub_ne_zero.mpr hα))
      · exact Or.inl (sub_ne_zero.mpr ha)
    · have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
          = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
        rw [commitGen_sub, sub_smul, sub_smul]; abel
      rw [hrw, e, sub_self]

/-- Data version of `relation_of_foldGens`: an explicit witness over the folded generators lifts to
an explicit witness over the originals. -/
noncomputable def relationOfFoldGensWitness {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (U W : G) (u : F)
    (r : AugmentedRelationWitness (F := F) (foldGens g u) U W) :
    AugmentedRelationWitness (F := F) g U W := by
  refine ⟨append r.a (u⁻¹ • r.a), r.alpha, r.beta, ?_, ?_⟩
  · rcases r.nontrivial with ha | hαβ
    · refine Or.inl (fun hc => ha ?_)
      have h0 : loHalf (append r.a (u⁻¹ • r.a)) = r.a := loHalf_append r.a (u⁻¹ • r.a)
      rw [hc] at h0
      simpa [loHalf] using h0.symm
    · exact Or.inr hαβ
  · have hcg : commitGen g (append r.a (u⁻¹ • r.a)) = commitGen (foldGens g u) r.a := by
      unfold foldGens
      rw [commitGen_append, commitGen_add_gen, commitGen_smul_gen, commitGen_smul_left]
    rw [hcg]; exact r.relation

/-- Data version of `deployed_leaf_peel`: taking the prover's leaf representation `aP` as **data**, the
combined leaf equation either splits into the clean leaf checks or yields an **explicit**
`AugmentedRelationWitness` over `(g, U, W)`. -/
noncomputable def deployedLeafPeelWitness {n : ℕ} {g : Fin n → G} {b : Fin n → F} {U W : G} {z : F}
    (aP : Fin n → F) {v blind c f : F} (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W) :
    (commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c))
      ⊕' AugmentedRelationWitness (F := F) g U W := by
  cases separateOrRelationWitness g U W aP (fun _ => c) (z * v)
      (z * commitGen b (fun _ => c)) blind f e with
  | inl h => exact PSum.inl ⟨congrArg (commitGen g) h.1, mul_left_cancel₀ hz h.2.1⟩
  | inr hrel => exact PSum.inr hrel

/-- Data-carrying deployed accept: the algebraic prover supplies, at each leaf, the representation
`aP` of the folded commitment as **data** (a subtype), rather than the existential `∃ aP` of
`DeployedIpaAcceptV`. This is the algebraic-group-model input: group outputs carry representations. -/
def AlgebraicDeployedAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → G → F → G → F → F →
    DeployedIpaTreeV F G d → Type _
  | 0, g, b, U, W, z, P, v, blind, .leaf c f =>
      { aP : Fin (2 ^ 0) → F // P = commitGen g aP ∧
        commitGen g aP + (z * v) • U + blind • W
          = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W }
  | _ + 1, g, b, U, W, z, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃ =>
      PLift (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0) ×'
        AlgebraicDeployedAcceptV (foldGens g u₁) (foldGens b u₁) U W z
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (blind + u₁⁻¹ • Lw + u₁ • Rw) t₁ ×'
        AlgebraicDeployedAcceptV (foldGens g u₂) (foldGens b u₂) U W z
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (blind + u₂⁻¹ • Lw + u₂ • Rw) t₂ ×'
        AlgebraicDeployedAcceptV (foldGens g u₃) (foldGens b u₃) U W z
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (blind + u₃⁻¹ • Lw + u₃ • Rw) t₃

/-- **Explicit-witness peel (algebraic prover).** From the data-carrying accept — the prover's
representations — the deployed recursion yields either the clean `IpaAcceptV` transcript or an
**explicit** `AugmentedRelationWitness` over `(g, U, W)`, built from those representations with no
`Classical.choice`. Data-carrying analogue of `deployed_to_acceptV`. -/
noncomputable def deployedToAcceptVWitness {U W : G} {z : F} (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → AlgebraicDeployedAcceptV g b U W z P v blind t →
      IpaAcceptV g b P v (projTree t) ⊕' AugmentedRelationWitness (F := F) g U W
  | 0, g, b, P, v, blind, .leaf c f, h => by
      obtain ⟨aP, hP, he⟩ := h
      cases deployedLeafPeelWitness aP hz he with
      | inl h1 => exact PSum.inl ⟨hP.trans h1.1, h1.2⟩
      | inr hrel => exact PSum.inr hrel
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨hu, h1, h2, h3⟩ := h
      obtain ⟨h12, h13, h23, hz1, hz2, hz3⟩ := hu.down
      cases deployedToAcceptVWitness hz _ _ _ _ _ t₁ h1 with
      | inl hc₁ =>
        cases deployedToAcceptVWitness hz _ _ _ _ _ t₂ h2 with
        | inl hc₂ =>
          cases deployedToAcceptVWitness hz _ _ _ _ _ t₃ h3 with
          | inl hc₃ => exact PSum.inl ⟨h12, h13, h23, hz1, hz2, hz3, hc₁, hc₂, hc₃⟩
          | inr hr₃ => exact PSum.inr (relationOfFoldGensWitness g U W u₃ hr₃)
        | inr hr₂ => exact PSum.inr (relationOfFoldGensWitness g U W u₂ hr₂)
      | inr hr₁ => exact PSum.inr (relationOfFoldGensWitness g U W u₁ hr₁)

/-- **Bridge to the probability wrapper.** From the algebraic prover's representations, the deployed
opening is either the clean `IpaAcceptV` transcript or an explicit `AlgebraicRelationWitness` over the
augmented basis `(g, U, W)` — precisely the adversary output that `Soundness.AGMProbability`'s
reduction consumes (`succSet`/`relSet`), with **no** `Classical.choice`. This is the algebraic-prover
model of issue #15(1) wired to the DL reduction at the peel level. -/
noncomputable def algebraicRelationOfDeployedAccept {d : ℕ} {U W : G} {z : F} (hz : z ≠ 0)
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : AlgebraicDeployedAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t)
      ⊕' AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  match deployedToAcceptVWitness hz g b P v blind t h with
  | PSum.inl hc => PSum.inl hc
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
