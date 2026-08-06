import Zcash.Snark.Verifier.Assemble

/-!
# What the rejecting assembly returns when it accepts

`assemble?` and the `?`-variants beneath it return `none` on a rejecting input and `some` on a
non-rejecting one. These lemmas say what the `some` is: exactly the value the corresponding
total function computes.

* `constructIntermediateSets?_eq_some` — the non-rejecting grouping.
* `assembleOpening?_eq_some`, `assembleFinalMsm?_eq_some` — the opening and the final MSM.
* `assemble?_eq_some` — `assemble? … = some m` gives `m = assembleFinalMsm …` over the derived
  grouping.
* `assemble_eq_of_assemble?_eq_some` — the same `some m` pins the total wrapper:
  `assemble … = m`, not the zero-MSM rejection fallback.

They are operational facts about the verifier, not about soundness, so they sit with the
verifier. Both the deployed soundness layer and the fingerprint representation walk consume
them; neither has to import the other to get them.
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

omit [AddCommGroup G] [Module F G] in
/-- `assemble?` returning `some m` pins the total `assemble` to `m` — acceptance facts stated
about `assemble` transfer to the `some` payload, with the zero-MSM rejection fallback ruled
out by the `some` itself. -/
theorem assemble_eq_of_assemble?_eq_some {shape : Shape} [DecidableEq F]
    [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {m : Msm shape.k F G} (h : assemble? vk instanceCommitment ps ch = some m) :
    assemble vk instanceCommitment ps ch = m := by
  unfold assemble
  rw [h]
  rfl

end Zcash.Snark
