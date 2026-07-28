import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Deployed.Flat

/-!
# Deployed acceptance implies the explicit IPA verifier equation

This module instantiates the closed form `CF` (`Deployed.Flat`) at halo2's multiopen assembly and
ties the resulting equation to the deployed accept condition:

* `multiopenCommitment` / `multiopenValue` — the `P` and `v` halo2's IPA verifier opens, read off the
  multiopen assembly on `(vk, ps, ch)`.
* `deployedIpaCommitment` — the adjusted commitment `P' = P − [v]g₀ + [ξ]S` at that `P` and `v`.
* `deployed_verification_eq` — `(assembleFinalMsm …).eval` *is* the closed form, for any multiopen
  grouping.
* `DeployedIpaVerifierEq` — the closed form at the grouping the deployed verifier derives, set to
  the identity.
* the `…?_eq_some` lemmas — deployed acceptance uses the rejecting `assemble?`; when it
  returns `some m`, `m` is the non-rejecting `assembleFinalMsm`, so the equation transfers.

`Soundness.Main` records the legacy bridge; `Forking.Adversary.Algebraic` gives the computed one.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

omit [Field F] [AddCommGroup G] [Module F G] in
/-- `constructIntermediateSets?` returning `some` is the non-rejecting grouping. -/
theorem constructIntermediateSets?_eq_some {k : ℕ} [DecidableEq F] [DecidableEq G]
    {queries : List (VerifierQuery k F G)} {grouped : MultiopenGrouped k F G}
    (h : constructIntermediateSets? queries = some grouped) :
    grouped = constructIntermediateSets queries := by
  unfold constructIntermediateSets? at h
  by_cases hd : hasDuplicateCommitmentPoint queries = true
  · rw [if_pos hd] at h; exact absurd h (by simp)
  · rw [if_neg hd] at h; exact (Option.some.injEq _ _ |>.mp h).symm

omit [AddCommGroup G] [Module F G] in
/-- `assembleOpening?` returning `some` is the non-rejecting opening. -/
theorem assembleOpening?_eq_some {k : ℕ} (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) {opened : Msm k F G × F}
    (h : assembleOpening? x1 x2 x3 x4 qPrime u grouped incoming = some opened) :
    opened = assembleOpening x1 x2 x3 x4 qPrime u grouped incoming := by
  unfold assembleOpening? at h
  by_cases hc : u.length = grouped.sets.length ∧ grouped.points.length = grouped.sets.length
  · rw [if_pos hc] at h; exact (Option.some.injEq _ _ |>.mp h).symm
  · rw [if_neg hc] at h; exact absurd h (by simp)

omit [AddCommGroup G] [Module F G] in
/-- `assembleFinalMsm?` returning `some` is the non-rejecting final MSM. -/
theorem assembleFinalMsm?_eq_some {shape : Shape} (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) {m : Msm shape.k F G}
    (h : assembleFinalMsm? ps ch grouped = some m) :
    m = assembleFinalMsm ps ch grouped := by
  unfold assembleFinalMsm? at h
  cases hop : assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      grouped (Msm.zero shape.k F G) with
  | none => rw [hop] at h; exact absurd h (by simp)
  | some opened =>
      rw [hop] at h
      have hopened := assembleOpening?_eq_some ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
        (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k F G) hop
      rw [← (Option.some.injEq _ _ |>.mp h), assembleFinalMsm, hopened]

omit [AddCommGroup G] [Module F G] in
/-- The deployed accept uses the rejecting `assemble?`; when it returns `some m`, `m` is the
non-rejecting `assembleFinalMsm` over the derived grouping, so `eval_assembleFinalMsm` (hence the
verifier equation) applies to it. -/
theorem assemble?_eq_some {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {m : Msm shape.k F G} (h : assemble? vk instanceCommitment ps ch = some m) :
    m = assembleFinalMsm ps ch (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) := by
  unfold assemble? at h
  by_cases hwf : proofStringWellFormed ps = true
  · rw [if_pos hwf] at h
    by_cases hxn : ch.x ^ vk.n = (1 : F)
    · rw [if_pos hxn] at h; exact absurd h (by simp)
    · rw [if_neg hxn] at h
      cases hcis : constructIntermediateSets? (assembleQueries vk instanceCommitment ps ch) with
      | none => rw [hcis] at h; exact absurd h (by simp)
      | some grouped =>
          rw [hcis] at h
          simp only [] at h
          by_cases hpts : multiopenPointsAvoidX3 ch.x3 grouped = true
          · rw [if_pos hpts] at h
            rw [← constructIntermediateSets?_eq_some hcis]
            exact assembleFinalMsm?_eq_some ps ch grouped h
          · rw [if_neg hpts] at h; exact absurd h (by simp)
  · rw [if_neg hwf] at h; exact absurd h (by simp)

/-- The deployed multiopen commitment `P` the IPA verifier opens: the `x₁`-compressed, `x₄`-collapsed
multiopen assembly on `(vk, ps, ch)`, evaluated against the URS. -/
def multiopenCommitment {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : G :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩

/-- The deployed multiopen value `v` the IPA verifier opens `P` to (halo2 `multiopen/verifier.rs`). -/
def multiopenValue {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G)
    (ch : Challenges shape.k F) : F :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).2

/-- The adjusted commitment the deployed IPA verifier actually opens: `adjustedCommitment` at the
multiopen commitment `P` and value `v` derived from `(vk, ps, ch)`, blinded by the proof's `ipaS` at
`ch.xi`. -/
abbrev deployedIpaCommitment {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : G :=
  adjustedCommitment g (multiopenCommitment g w u vk instanceCommitment ps ch)
    (multiopenValue vk instanceCommitment ps ch) ch.xi ps.ipaS

/-- The deployed fingerprint MSM evaluates to the closed form `CF` (`Deployed.Flat`): the adjusted
commitment `P − [v]g₀ + [ξ]S`, the round total `Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ)`, the value-binding `[-c·b·z]U`,
the blinding `[-f]W`, and the folded generator `[-c]G'₀`. `eval_assembleFinalMsm` plus
`deployed_gterm_foldAll` (the `g`-term is `[-c]·G'₀`).

The grouping is a parameter, so the adjusted commitment reads `assembleOpening` on that grouping
directly. At the grouping the deployed verifier derives it is `deployedIpaCommitment`, which is
where `DeployedIpaVerifierEq` picks it up. -/
theorem deployed_verification_eq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = CF (List.ofFn ps.ipaRounds) (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
          (adjustedCommitment g
            ((assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
                grouped (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩)
            (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
                grouped (Msm.zero shape.k F G)).2
            ch.xi ps.ipaS)
          ps.ipaC (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) u (-ps.ipaF) w := by
  rw [eval_assembleFinalMsm, deployed_gterm_foldAll]
  rfl

/-- halo2's explicit IPA verifier equation for the deployed proof, set to the group identity: the
closed form `CF` at the derived grouping, opening the pinned `deployedIpaCommitment`. By
`deployed_verification_eq` this is exactly `(assembleFinalMsm …).eval = 0`. Stating it as its own
definition lets the forking bridge act on halo2's actual IPA equation.

Totality note: the closed form uses Lean's total inverse (`0⁻¹ = 0`), and the deployed code
computes the same thing — halo2 batch-inverts the round challenges with ff's `batch_invert`,
which leaves a zero challenge at zero — so at `uⱼ = 0` the equation and the Rust agree
term for term. The corner is faithful in both directions: nothing about acceptance can be
shown from this form that the deployed verifier would not exhibit. The forking *extractor*, by
contrast, needs the three sibling challenges at each node to be nonzero (the Vandermonde recovery
and `u⁻¹` fold need cancellable challenges), paying for that extra bad challenge per round in the
knowledge-error count `Soundness.Forking.Tree.kerr` — so this totality concerns only the equation's
definedness, not the extractor's admissible challenges. -/
def DeployedIpaVerifierEq {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : Prop :=
  CF (List.ofFn ps.ipaRounds) (List.ofFn ch.ipaRound)
      (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
      (deployedIpaCommitment g w u vk instanceCommitment ps ch)
      ps.ipaC (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) u (-ps.ipaF) w = 0

end Zcash.Snark
