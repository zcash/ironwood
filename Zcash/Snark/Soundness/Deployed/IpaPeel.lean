import Zcash.Snark.Soundness.Deployed.Ipa
import Zcash.Snark.Soundness.Deployed.Binding

/-!
# Peeling the deployed IPA onto the clean recursive IPA, as a binding reduction

`Zcash.Snark.Soundness.Deployed.Ipa` modelled halo2's deployed IPA — the clean recursion plus the `U`/`W`
apparatus (`S`/`ξ` stays in the verifier equation, not the tree) — as `DeployedIpaAcceptV`. This module peels
that apparatus off onto the clean `IpaAcceptV`, so
the deployed opening reduces to `ipa_soundV`, expressing commitment binding as a discrete-log-relation (DLR)
reduction: a leaf collision yields a nontrivial relation among the augmented generators.

* `relation_of_foldGens` — a nontrivial relation among the folded generators lifts to one among the
  originals, so the per-round peel reports any relation it finds against the fixed URS generators `g`.
* `deployed_leaf_peel` — one combined leaf equation splits into the clean leaf checks *or* exhibits a
  relation among `(g, U, W)` (via `separate_or_relation`).
* `deployed_to_acceptV` — recurse the peel over the tree, threading the relation branch: an accepting
  deployed tree yields a clean `IpaAcceptV` transcript *or* a nontrivial relation among `(g, U, W)`.

The `... ∨ HasNontrivialRelation` conclusion is a reduction, not a logical exclusion: a relation always
*exists* in a prime-order group, so the relation branch is ruled out not by `¬ HasNontrivialRelation` but by
DLR hardness — no feasible adversary can *find* one — leaving the clean `ipa_soundV` opening.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial relation among the folded generators lifts to one among the originals. With
`foldGens g u = loHalf g + u⁻¹ • hiHalf g`, a relation `⟨a', foldGens g u⟩ + α•U + β•W = 0` is, via
`append a' (u⁻¹ • a')`, a relation `⟨·, g⟩ + α•U + β•W = 0`; it stays nontrivial because
`loHalf (append a' _) = a'`. So the per-round peel can always report its relation against the fixed `g`. -/
theorem relation_of_foldGens {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (U W : G) (u : F)
    (h : HasNontrivialRelation (F := F) (foldGens g u) U W) :
    HasNontrivialRelation (F := F) g U W := by
  obtain ⟨a', α, β, hne, heq⟩ := h
  have hcg : commitGen g (append a' (u⁻¹ • a')) = commitGen (foldGens g u) a' := by
    unfold foldGens
    rw [commitGen_append, commitGen_add_gen, commitGen_smul_gen, commitGen_smul_left]
  refine ⟨append a' (u⁻¹ • a'), α, β, ?_, ?_⟩
  · rcases hne with ha | hαβ
    · refine Or.inl (fun hc => ha ?_)
      have h0 : loHalf (append a' (u⁻¹ • a')) = a' := loHalf_append a' (u⁻¹ • a')
      rw [hc] at h0
      simpa [loHalf] using h0.symm
    · exact Or.inr hαβ
  · rw [hcg]; exact heq

/-- One deployed leaf peels (reduction form). The reformulated leaf relation
`⟨aP, g⟩ + [z·v]U + [blind]W = [c]g₀ + [z·c·b₀]U + [f]W` (value carried on `U` via `z`; halo2's literal check
instead uses `g₀`/`[ξ]S`, see `DeployedIpaVerifierEq`) either splits into the clean leaf checks
`⟨aP, g⟩ = [c]g₀` and `v = c·b₀` (the `W`-side blinding identity discarded), or exhibits a nontrivial
relation among `(g, U, W)`. `separate_or_relation` gives the coordinate split and `z ≠ 0` cancels the
`U`-side. -/
theorem deployed_leaf_peel {n : ℕ} {g : Fin n → G} {b : Fin n → F} {U W : G} {z : F}
    {aP : Fin n → F} {v blind c f : F} (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W) :
    (commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c))
      ∨ HasNontrivialRelation (F := F) g U W := by
  rcases separate_or_relation g U W aP (fun _ => c) (z * v) (z * commitGen b (fun _ => c)) blind f e
    with ⟨ha, hα, _⟩ | hrel
  · exact Or.inl ⟨congrArg (commitGen g) ha, mul_left_cancel₀ hz hα⟩
  · exact Or.inr hrel

/-- The deployed recursion peels to the clean `IpaAcceptV`, or exhibits a relation. By induction on the
tree: each leaf peels via `deployed_leaf_peel`; at a node, if all three subtrees peel cleanly the clean node
check holds, and any relation a subtree finds (against `foldGens g uᵢ`) lifts to one against `g`
(`relation_of_foldGens`). Binding enters only as the `HasNontrivialRelation` branch of the disjunction —
the reduction, not an assumed independence. -/
theorem deployed_to_acceptV {U W : G} {z : F} (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → DeployedIpaAcceptV g b U W z P v blind t →
      IpaAcceptV g b P v (projTree t) ∨ HasNontrivialRelation (F := F) g U W
  | 0, g, b, P, v, blind, .leaf c f, h => by
      obtain ⟨aP, hP, he⟩ := h
      rcases deployed_leaf_peel hz he with ⟨h1, h2⟩ | hrel
      · exact Or.inl ⟨hP.trans h1, h2⟩
      · exact Or.inr hrel
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      rcases deployed_to_acceptV hz _ _ _ _ _ t₁ ha₁ with hc₁ | hr₁
      · rcases deployed_to_acceptV hz _ _ _ _ _ t₂ ha₂ with hc₂ | hr₂
        · rcases deployed_to_acceptV hz _ _ _ _ _ t₃ ha₃ with hc₃ | hr₃
          · exact Or.inl ⟨h12, h13, h23, hu₁, hu₂, hu₃, hc₁, hc₂, hc₃⟩
          · exact Or.inr (relation_of_foldGens g U W u₃ hr₃)
        · exact Or.inr (relation_of_foldGens g U W u₂ hr₂)
      · exact Or.inr (relation_of_foldGens g U W u₁ hr₁)

end Zcash.Snark
