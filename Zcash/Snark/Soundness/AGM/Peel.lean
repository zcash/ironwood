import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.AGM.Probability

/-!
# Compute relation witnesses from algebraic prover data

Each prover round point includes coefficients over `(g, U, W)`. The definitions below compute either
a clean IPA transcript or an explicit `NontrivialRelation`. The relation coefficients are the
difference between the prover's representation and the expected one; no witness is selected with
`Classical.choice`.

* `separateOrRelationWitness`, `relationOfFoldGensWitness`, and `deployedLeafPeelWitness` implement
  the corresponding deployed peel steps with explicit data.
* `deployedToAcceptVWitness` — the recursive peel, returning `IpaAcceptV ⊕' AugmentedRelationWitness`.
* `algebraicRelationOfDeployedAccept` converts the result to the form used by the probability proof.

`Soundness.AGM.Capstone` connects this peel to the deployed opening. The forking layer must supply
the transcript and representations as data.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- Compare two representations, returning equality or their explicit difference as a relation. -/
def separateOrRelationWitness {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ⊕' AugmentedRelationWitness (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact PSum.inl h
  · exact PSum.inr (NontrivialRelation.ofCombinationCollision e h)

/-- Lift a relation over folded generators to the original generators. -/
def relationOfFoldGensWitness {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (U W : G) (u : F)
    (r : AugmentedRelationWitness (F := F) (foldGens g u) U W) :
    AugmentedRelationWitness (F := F) g U W :=
  NontrivialRelation.ofFoldedGens u r

/-- Peel a deployed leaf into clean checks or an explicit relation over `(g, U, W)`. -/
def deployedLeafPeelWitness {n : ℕ} {g : Fin n → G} {b : Fin n → F} {U W : G} {z : F}
    (aP : Fin n → F) {v blind c f : F} (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W) :
    (commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c))
      ⊕' AugmentedRelationWitness (F := F) g U W := by
  cases separateOrRelationWitness g U W aP (fun _ => c) (z * v)
      (z * commitGen b (fun _ => c)) blind f e with
  | inl h => exact PSum.inl ⟨congrArg (commitGen g) h.1, mul_left_cancel₀ hz h.2.1⟩
  | inr hrel => exact PSum.inr hrel

/-- Reassemble a deployed IPA point from its group, value, and blinding parts. -/
def deployedRoundPoint (U W : G) (z : F) (L : G) (Lv Lw : F) : G :=
  L + (z * Lv) • U + Lw • W

/-- Representations for every group point output by a deployed IPA tree.

Each round point combines its group, value, and blinding parts. Every node, including descendants,
uses the original public basis `(g, U, W)`. -/
def AlgebraicTreeRepresentations {n : ℕ} (g : Fin n → G) (U W : G) (z : F) :
    {d : ℕ} → DeployedIpaTreeV F G d → Type _
  | 0, .leaf _ _ _ => PUnit
  | _ + 1, .node L R Lv Rv Lw Rw _ _ _ t₁ t₂ t₃ =>
      GroupRepresentation (F := F) (augmentedBasis g U W)
        (deployedRoundPoint (F := F) U W z L Lv Lw) ×
      GroupRepresentation (F := F) (augmentedBasis g U W)
        (deployedRoundPoint (F := F) U W z R Rv Rw) ×
      AlgebraicTreeRepresentations g U W z t₁ ×
      AlgebraicTreeRepresentations g U W z t₂ ×
      AlgebraicTreeRepresentations g U W z t₃

/-- A deployed accepting tree with representations for every prover-emitted group point. -/
structure AlgebraicDeployedAcceptV {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F)
    (U W : G) (z : F) (P : G) (v blind : F) (t : DeployedIpaTreeV F G d) : Type _ where
  accepts : DeployedIpaAcceptV g b U W z P v blind t
  representations : AlgebraicTreeRepresentations g U W z t

/-- Recursively peel an accepting deployed tree into a clean IPA transcript or explicit relation.

The relation is computed from the acceptance equations and leaf representation. Node
representations enforce the AGM input contract but are not used by this computation. -/
def deployedToAcceptVWitnessCore {U W : G} {z : F} (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → DeployedIpaAcceptV g b U W z P v blind t →
      IpaAcceptV g b P v (projTree t) ⊕' AugmentedRelationWitness (F := F) g U W
  | 0, g, b, P, v, blind, .leaf c f aP, h => by
      cases deployedLeafPeelWitness aP hz h.2 with
      | inl h1 => exact PSum.inl ⟨h.1.trans h1.1, h1.2⟩
      | inr hrel => exact PSum.inr hrel
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hz1, hz2, hz3, h1, h2, h3⟩ := h
      cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₁ h1 with
      | inl hc₁ =>
        cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₂ h2 with
        | inl hc₂ =>
          cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₃ h3 with
          | inl hc₃ => exact PSum.inl ⟨h12, h13, h23, hz1, hz2, hz3, hc₁, hc₂, hc₃⟩
          | inr hr₃ => exact PSum.inr (relationOfFoldGensWitness g U W u₃ hr₃)
        | inr hr₂ => exact PSum.inr (relationOfFoldGensWitness g U W u₂ hr₂)
      | inr hr₁ => exact PSum.inr (relationOfFoldGensWitness g U W u₁ hr₁)

/-- Run the deterministic peel on an accepting tree that includes its AGM representations. -/
def deployedToAcceptVWitness {U W : G} {z : F} (hz : z ≠ 0) {d : ℕ}
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : AlgebraicDeployedAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t) ⊕' AugmentedRelationWitness (F := F) g U W :=
  deployedToAcceptVWitnessCore hz g b P v blind t h.accepts

/-- Return a clean IPA transcript or the explicit relation consumed by the probability proof. -/
def algebraicRelationOfDeployedAccept {d : ℕ} {U W : G} {z : F} (hz : z ≠ 0)
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : AlgebraicDeployedAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t)
      ⊕' AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  match deployedToAcceptVWitness hz g b P v blind t h with
  | PSum.inl hc => PSum.inl hc
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
