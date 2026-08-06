import Mathlib.Tactic
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Deployed.Verification

/-!
# Conditional soundness and deployed acceptance

Soundness starts from `DeployedAccepts`: `assemble?` succeeds and the resulting MSM evaluates to
zero. The adaptive and straight-line AGM routes consume this predicate directly.

## The deployed route

`deployedAccepts_verifierEq` exposes the equivalent flattened IPA equation used by the current
straight-line AGM analysis. Extraction and Action semantics live in `Soundness.AGM` and
`Circuits.Integration`; this module intentionally exports no forked-transcript compatibility lane.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Tracked semantic-adequacy gap: `S` is a free `Prop`, and the Clean/Ironwood representation
-- work is exposed as the named component conditions of `TopLevelCircuitCorrectness` rather than
-- proved, so the chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and
-- never reaches "…therefore a valid Orchard action" (note well-formed, value balanced, nullifier
-- correctly derived, spend authorized). Closing the generic form means instantiating `S` to the
-- concrete Orchard statement and discharging those conditions. The deployed Action key is derived
-- and certified against the capture by `Keygen/Certificate.lean`; only the capture's Rust provenance
-- remains an input-side boundary. The semantic bridge described here remains open.
def DeployedAccepts [DecidableEq G] [Inhabited G] (shape : Shape) (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- Transport MSM evaluation across the equality `shape.k = urs.k`. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Deployed acceptance implies halo2's explicit IPA verifier equation. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk instanceCommitment ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk instanceCommitment ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)), ← hmeq]
      exact h

/-- The proof's deployed multiopen commitment over the supplied URS. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch

end Zcash.Snark
