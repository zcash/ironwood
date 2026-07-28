import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Deployed.IpaPeel

/-!
# Assemble forked transcripts into the deployed IPA tree

The old `FiatShamirTree` assumption combined two jobs: producing forked transcripts by random-oracle
rewinding, and converting those transcripts into `DeployedIpaAcceptV`. This module proves the second
job.

The verifier equation folds one IPA round at a time (`VerifierIpa.eval_peel`, `Deployed.Flat`), and
`computeB_cons` matches that fold's `b`-value update. `evalLeaf_to_acceptV` identifies the
depth-zero equation with the deployed leaf check, and `forkAccept_to_acceptV` assembles the tree.

`Soundness.Forking.Extractor` recovers the parent data, while the algebraic prover supplies AGM
coefficients. Rewinding and query loss remain outside this structural step.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## The `computeB` round recursion (the `b`-value fold) -/

/-- The second `computeB` accumulator after `|u|` rounds is `x ^ (2 ^ |u|)`. -/
theorem computeB_pt {F : Type*} [CommRing F] (x : F) (u : List F) :
    (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).2
      = x ^ (2 ^ u.length) := by
  induction u with
  | nil => simp
  | cons u₀ tail ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.length_cons, ← pow_add, pow_succ, Nat.mul_two]

/-- Split the leading challenge's factor from `computeB`. -/
theorem computeB_cons {F : Type*} [CommRing F] (x u₀ : F) (tail : List F) :
    computeB x (u₀ :: tail) = computeB x tail * (1 + u₀ * x ^ (2 ^ tail.length)) := by
  rw [computeB, computeB, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ← computeB_pt x tail]

/-! ## The eval-vector fold telescopes to `computeB`

The recursive verifier folds `b = (1, x, x², …)` to one value. The lemmas below show that this value
is the flat verifier's `computeB x u`.
-/

/-- One eval-vector fold produces a shorter eval vector and one scalar factor. -/
theorem foldGens_evalVector {F : Type*} [Field F] (k : ℕ) (x u : F) :
    foldGens (evalVector (k + 1) x) u = (1 + u⁻¹ * x ^ (2 ^ k)) • evalVector k x := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, evalVector, smul_eq_mul]
  rw [pow_add]
  ring

/-- `foldGens` commutes with scalar multiplication. -/
theorem foldGens_smul {F : Type*} [Field F] {k : ℕ} (c : F) (b : Fin (2 ^ (k + 1)) → F) (v : F) :
    foldGens (c • b) v = c • foldGens b v := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, smul_eq_mul]
  ring

/-- `foldAll` commutes with scalar multiplication. -/
theorem foldAll_smul {F : Type*} [Field F] (c : F) (u : List F) (b : Fin (2 ^ u.length) → F) :
    foldAll (G := F) u (c • b) = c • foldAll (G := F) u b := by
  induction u with
  | nil => rfl
  | cons u₀ rest ih => rw [foldAll, foldGens_smul, ih, foldAll]

/-- Folding the eval vector through all challenges gives `computeB x u`. -/
theorem foldAll_evalVector {F : Type*} [Field F] (x : F) (u : List F) :
    foldAll (G := F) u (evalVector u.length x) (0 : Fin (2 ^ 0)) = computeB x u := by
  induction u with
  | nil => simp [foldAll, evalVector, computeB]
  | cons u₀ rest ih =>
    rw [foldAll]
    simp only [List.length_cons]
    rw [foldGens_evalVector, inv_inv, foldAll_smul, Pi.smul_apply, ih, smul_eq_mul, computeB_cons]
    ring

/-! ## Leaf reconciliation: the depth-0 equation is the deployed tree's leaf check

At depth zero, the flat equation rearranges to the deployed IPA leaf check. This step is pure group
algebra; the later peel uses `z ≠ 0`.
-/

/-- Convert the depth-zero equation to the deployed IPA leaf check. -/
theorem evalLeaf_to_acceptV (g : Fin (2 ^ 0) → G) (b : Fin (2 ^ 0) → F) (U W : G) (z : F)
    (aP : Fin (2 ^ 0) → F) (v blind c f : F)
    (hEq : (VerifierIpa.leaf (commitGen g aP + (z * v) • U + blind • W) c
              (-(z * commitGen b (fun _ => c))) (-f)).eval g U W = 0) :
    DeployedIpaAcceptV g b U W z (commitGen g aP) v blind (.leaf c f aP) := by
  refine ⟨rfl, ?_⟩
  have hg : commitGen g (fun _ => c) = c • g 0 := by simp [commitGen]
  rw [hg, ← sub_eq_zero, ← hEq, VerifierIpa.eval_leaf]
  module

/-! ## The tree assembly: the forking output yields `DeployedIpaAcceptV`

`ForkAccept` records three accepting continuations at each round and a verifier equation at each
leaf. `forkAccept_to_acceptV` converts those leaves and assembles `DeployedIpaAcceptV`.
-/

/-- A ternary fork tree with the verifier equation at each leaf. -/
def ForkAccept : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → G → F → G → F → F →
    DeployedIpaTreeV F G d → Prop
  | 0, g, b, U, W, z, P, v, blind, .leaf c f aP =>
      P = commitGen g aP ∧
        (VerifierIpa.leaf (P + (z * v) • U + blind • W) c
          (-(z * commitGen b (fun _ => c))) (-f)).eval g U W = 0
  | _ + 1, g, b, U, W, z, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        ForkAccept (foldGens g u₁) (foldGens b u₁) U W z
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (blind + u₁⁻¹ • Lw + u₁ • Rw) t₁ ∧
        ForkAccept (foldGens g u₂) (foldGens b u₂) U W z
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (blind + u₂⁻¹ • Lw + u₂ • Rw) t₂ ∧
        ForkAccept (foldGens g u₃) (foldGens b u₃) U W z
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (blind + u₃⁻¹ • Lw + u₃ • Rw) t₃

/-- Convert a `ForkAccept` tree to the deployed recursive acceptance predicate. -/
theorem forkAccept_to_acceptV {U W : G} {z : F} :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → ForkAccept g b U W z P v blind t →
      DeployedIpaAcceptV g b U W z P v blind t
  | 0, g, b, P, v, blind, .leaf c f aP, h => by
      obtain ⟨hP, hEq⟩ := h
      rw [hP] at hEq ⊢
      exact evalLeaf_to_acceptV g b U W z aP v blind c f hEq
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      exact ⟨h12, h13, h23, hu₁, hu₂, hu₃,
        forkAccept_to_acceptV _ _ _ _ _ t₁ ha₁,
        forkAccept_to_acceptV _ _ _ _ _ t₂ ha₂,
        forkAccept_to_acceptV _ _ _ _ _ t₃ ha₃⟩

end Zcash.Snark
