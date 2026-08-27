import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.KeyDigest
import Zcash.Snark.Verifier.ProofBytes
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

-- Semantic reach of the chain built on this predicate: `TopLevelCircuitCorrectness`'s component
-- conditions are discharged for the deployed Action circuit, so the adaptive-statement stack ends
-- at `ActionTerminal.ActionBundleWitness` — the circuit's private witnesses with their `ActionSpec`
-- satisfaction proofs at the adversary's public inputs — rather than at gate satisfaction. The
-- remaining output-side boundary is composing `ActionSpec`, including its `HashGuarded` Sinsemilla
-- escape branches, with the abstract Orchard ledger relation. On the input side, the deployed Action
-- key is derived and certified against the capture by `Keygen/Certificate.lean`; the exact captured
-- proof bytes are parsed and composed with acceptance below. Universal refinement of the Rust reader
-- by `readProof?` remains external.
/-- **Deployed acceptance.** `assemble?` succeeds on the typed proof string and the assembled MSM
evaluates to zero over the URS — the hypothesis every soundness endpoint consumes.

This is the reusable typed core. `DeployedAcceptsBytes` below composes exact proof parsing, the
derived verifying-key digest, and the deployed BLAKE2b Fiat–Shamir transcript into it. Acceptance
prices one proof bundle: halo2's optional `BatchVerifier` aggregation layer is outside the
formalized verifier. -/
def DeployedAccepts [DecidableEq G] [Inhabited G] (shape : Shape) (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- **Byte-level deployed acceptance.** The whole proof byte string parses canonically and with no
unread suffix, then the existing typed `DeployedAccepts` predicate holds at challenges derived by
the deployed BLAKE2b transcript. The transcript opens with `keyDigest pinnedVkDescription`, so the
description-to-key identification is an explicit caller obligation; the fixture lane discharges it
field by field for the pinned Action key.

This definition composes the modeled layers. Identifying Rust's reader with `readProof?` for every
input remains a refinement boundary; the exact honest and random capture bytes exercise that
boundary concretely. -/
def DeployedAcceptsBytes (shape : Shape) (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (pinnedVkDescription : String)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (proofBytes : List UInt8) : Prop :=
  ∃ ps,
    (readProof? shape).run proofBytes = some (ps, []) ∧
    DeployedAccepts shape urs hk vk instanceCommitment ps
      (deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
        instanceCommitment ps)

/-- Byte-level acceptance exposes the unique parsed proof and its canonical serialization before
entering typed `DeployedAccepts`. -/
theorem deployedAcceptsBytes_canonical {shape : Shape} {urs : URS VestaG}
    {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp VestaG}
    {pinnedVkDescription : String}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} {proofBytes : List UInt8}
    (h : DeployedAcceptsBytes shape urs hk vk pinnedVkDescription instanceCommitment proofBytes) :
    ∃ ps,
      (readProof? shape).run proofBytes = some (ps, []) ∧
      serializeProof ps = proofBytes ∧
      DeployedAccepts shape urs hk vk instanceCommitment ps
        (deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
          instanceCommitment ps) := by
  rcases h with ⟨ps, hread, haccepts⟩
  exact ⟨ps, hread, serializeProof_eq_of_readProof?_eq_some hread, haccepts⟩

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
