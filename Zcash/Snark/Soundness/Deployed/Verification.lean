import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Deployed.Fold

/-!
# The deployed accept entails halo2's explicit IPA verifier equation (structural faithfulness)

`eval_assembleFinalMsm` evaluates the assembled fingerprint MSM in closed form; `deployed_gterm_foldAll`
identifies its `g`-term as `[-c]·G'₀`. This module welds them into halo2's published IPA verification
equation and ties it to the deployed accept condition, pinning the opened object `P`/`v` to the proof:

* `multiopenCommitment` / `multiopenValue` — the `P` and `v` halo2's IPA verifier opens, read off the
  multiopen assembly on `(vk, ps, ch)`.
* `deployed_verification_eq` — `(assembleFinalMsm …).eval` *is* the explicit equation
  `P + [-v]g₀ + [ξ]S + Σ(rounds) + [-c·b·z]U + [-f]W + [-c]G'₀`.
* `DeployedIpaVerifierEq` — that equation set to the identity.
* the `…?_eq_some` reconciliation — the deployed accept uses the *rejecting* `assemble?`; when it returns
  `some m`, `m` is the non-rejecting `assembleFinalMsm`, so the equation transfers.

This discharges the assembly↔equation correspondence separately from the bridge. What the bridge still
covers is the forking that produces the recursive tree, the node `L`/`R` decomposition, the leaf
`g`-representation of the folded commitment, and the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S` that folds the value and `S`/`ξ` terms into the opened
commitment (issue #11; see `FiatShamirTree`'s inventory).
-/

namespace Zcash.Snark

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
/-- The deployed accept uses the rejecting `assemble?`; when it returns `some m`, `m` is the non-rejecting
`assembleFinalMsm` over the derived grouping, so `eval_assembleFinalMsm` (hence the verifier equation)
applies to it. -/
theorem assemble?_eq_some {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {m : Msm shape.k F G} (h : assemble? vk ps ch = some m) :
    m = assembleFinalMsm ps ch (constructIntermediateSets (assembleQueries vk ps ch)) := by
  unfold assemble? at h
  by_cases hwf : proofStringWellFormed ps = true
  · rw [if_pos hwf] at h
    by_cases hxn : ch.x ^ vk.n = (1 : F)
    · rw [if_pos hxn] at h; exact absurd h (by simp)
    · rw [if_neg hxn] at h
      cases hcis : constructIntermediateSets? (assembleQueries vk ps ch) with
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
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) : G :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩

/-- The deployed multiopen value `v` the IPA verifier opens `P` to (halo2 `multiopen/verifier.rs`). -/
def multiopenValue {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) : F :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k F G)).2

/-- The deployed fingerprint MSM evaluates to halo2's explicit IPA verifier equation: the multiopen
commitment, the `[-v]g₀` value term, the `[ξ]S` blinding poly, the round total `Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ)`, the
value-binding `[-c·b·z]U`, the blinding `[-f]W`, and the folded generator `[-c]G'₀` (`G'₀ = foldAll`).
`eval_assembleFinalMsm` plus `deployed_gterm_foldAll` (the `g`-term is `[-c]·G'₀`). -/
theorem deployed_verification_eq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped
            (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
        + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
        + ch.xi • ps.ipaS
        + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
            (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
        + (-ps.ipaF) • w
        + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
            (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
  rw [eval_assembleFinalMsm, deployed_gterm_foldAll]

/-- halo2's explicit IPA verifier equation for the deployed proof, set to the group identity. By
`deployed_verification_eq` this is exactly `(assembleFinalMsm …).eval = 0`. Stating it explicitly lets the
forking bridge act on halo2's actual IPA equation, with `P`/`v` the pinned `multiopenCommitment`/`Value`.

Totality caveat: the closed form uses Lean's total inverse (`0⁻¹ = 0`), so at a zero round challenge the
equation is defined although no deployed execution corresponds to it (the Rust inverts the round
challenges). Harmless for the soundness direction — the capstones consume the equation only under
`DeployedAccepts` — but the equation is total where halo2 is partial (a negligible-probability corner). -/
def DeployedIpaVerifierEq {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) : Prop :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
      + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
      + ch.xi • ps.ipaS
      + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
          (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
      + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
      + (-ps.ipaF) • w
      + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 = 0

end Zcash.Snark
