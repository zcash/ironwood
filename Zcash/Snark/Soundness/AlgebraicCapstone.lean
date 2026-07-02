import Zcash.Snark.Soundness.AlgebraicPeel
import Zcash.Snark.Soundness.Forking

/-!
# Deployed capstone from an algebraic prover (issue #15, at the deployed level)

`Soundness.AlgebraicPeel` extracts an explicit relation witness from the algebraic prover's
representations. This module wires that up to the deployed opening: `deployedAlgebraicRelation` is the
data-carrying analogue of `Soundness.Forking.deployed_forking_relation`, concluding the multiopen
inner-product opening **or** an explicit `AugmentedRelationWitness` — with no `Classical.choice`.

## The boundary with the Fiat–Shamir/forking layer

The forking layer (`extractable_of_prob` → `deployed_forking_tree`) *produces* the accepting
transcript existentially, from the accept probability beating the knowledge error — an inherently
existential (probabilistic) extraction. So the top-level *forking* capstones
(`orchard_verifier_vesta_forking_*`) necessarily conclude the existential `HasNontrivialRelation`;
that is the nature of rewinding-based extraction, not a missing construction. What the algebraic-prover
model contributes — and what this module makes precise — is that **once the transcript is in hand with
its representations** (the AGM hypothesis, here the data `AlgebraicDeployedAcceptV`), the relation is
an *explicit* function of those representations, not a `Classical.choice` of an existential.
`deployedAlgebraicRelationWitness` exposes it in the `AlgebraicRelationWitness` form that
`Soundness.AGMProbability`'s discrete-log reduction consumes.
-/

open Classical
namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The deployed opening from an algebraic prover.** Data-carrying analogue of
`deployed_forking_relation`: given the algebraic prover's deployed transcript `t` *with its
representations supplied as data* (`AlgebraicDeployedAcceptV`, in place of the existentially-extracted
forking tree), the deployed opening either yields the multiopen inner-product relation, or an
**explicit** `AugmentedRelationWitness` over `(g, U, W)` built from those representations with no
`Classical.choice`. -/
noncomputable def deployedAlgebraicRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  cases deployedToAcceptVWitness hz urs.g b (commit urs aDep) 0 blind t ht with
  | inl hclean =>
    refine PSum.inl ?_
    obtain ⟨a, ha⟩ := ipaRelation_of_acceptV urs b (commit urs aDep) 0 (projTree t) hclean
    have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
      (by rw [add_sub_cancel_right]; exact ha)
    have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
      rw [hP]; abel
    rw [h2] at h1
    exact ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _ h1⟩
  | inr hrel => exact PSum.inr hrel

/-- The same, with the relation branch in the `AlgebraicRelationWitness (augmentedBasis …)` form that
`Soundness.AGMProbability`'s reduction (`relSet` / `succSet`) consumes — the explicit adversary output
of the discrete-log reduction, sourced from the prover's representations. -/
noncomputable def deployedAlgebraicRelationWitness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployedAlgebraicRelation urs b v ξ z blind aMulti aDep s t hz hb0 hP ht with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
