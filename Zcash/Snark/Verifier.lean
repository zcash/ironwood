import Mathlib
import Zcash.Snark.Msm

/-!
# The verifier's MSM assembly

This module assembles the fingerprint MSM the way the deployed verifier does (`plonk/verifier.rs`
together with the `poly/{multiopen,commitment}` openings): build the per-argument query commitments,
compress them through the multiopen folds, and finish with the inner-product-argument opening
(`Zcash.Snark.ipaFold`). It is filled in incrementally.

What this file currently provides:
* `CommitmentRef`, `VerifierQuery` — the shared query types (halo2 `CommitmentReference` / `VerifierQuery`).
* `vanishingHCommitment` — the vanishing argument's `h` commitment.
* `accumulateCommitment`, `compressQCommitments`, `multiopenCombine` — the multiopen `x₁` compression and
  `x₄` collapse (`multiopen/verifier.rs`).

Two VK-fixed pieces are still taken as inputs here rather than re-derived: the point-set grouping
(`construct_intermediate_sets`, which depends only on the query layout) supplies the `sets` argument of
`compressQCommitments`, and the Lagrange interpolation of the per-set evaluations supplies the `msmEval`
base of `multiopenCombine`.
-/

namespace Zcash.Snark

/-- A multiopen query's commitment reference (halo2 `CommitmentReference`): either a single group
element, or an MSM — the vanishing argument's folded `h` commitment is supplied as an MSM. -/
inductive CommitmentRef (k : ℕ) (F G : Type*) where
  | point : G → CommitmentRef k F G
  | msm : Msm k F G → CommitmentRef k F G

/-- A multiopen query (halo2 `VerifierQuery`): open `commitment` at `point`, claiming the value `eval`. -/
structure VerifierQuery (k : ℕ) (F G : Type*) where
  point : F
  commitment : CommitmentRef k F G
  eval : F

/-- The vanishing argument's `h` commitment (halo2 `vanishing/verifier.rs`): fold the quotient pieces by
`xⁿ` into `Σᵢ hᵢ · (xⁿ)ⁱ`, built as the Rust does — scale the accumulator by `xⁿ` and append the next
piece, over the pieces in reverse. -/
def vanishingHCommitment {F G : Type*} [Field F] (k : ℕ) (xn : F) (hPieces : List G) : Msm k F G :=
  hPieces.reverse.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) (Msm.zero k F G)

/-- Accumulate one query commitment into a point set's compressed commitment, weighted by the current
`x₁` power (the multiopen `accumulate` closure): a plain commitment is appended as a term, an MSM
commitment is scaled by the power and added. -/
def accumulateCommitment {k : ℕ} {F G : Type*} [Field F] (pow : F) (c : CommitmentRef k F G)
    (acc : Msm k F G) : Msm k F G :=
  match c with
  | .point p => acc.appendTerm pow p
  | .msm m => acc.add (m.scale pow)

/-- The multiopen `x₁` compression (`multiopen/verifier.rs`): for each point set, fold its commitments
(in processing order) into `Σⱼ x₁ʲ · cⱼ`. `sets` lists, per point set, the commitments grouped into it by
`construct_intermediate_sets` (taken as input — it is VK-fixed bookkeeping). -/
def compressQCommitments {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sets : List (List (CommitmentRef k F G))) : List (Msm k F G) :=
  sets.map fun setCommitments =>
    (setCommitments.foldl (fun (st : Msm k F G × F) c => (accumulateCommitment st.2 c st.1, st.2 * x1))
      (Msm.zero k F G, (1 : F))).1

/-- The multiopen `x₄` collapse (`multiopen/verifier.rs`): append the quotient commitment `q'`, then fold
the per-set compressed commitments `qCommitments` (paired with the prover's claimed evaluations `u`) by
`x₄`, accumulating both the MSM and the combined value `v` (starting from the Lagrange base `msmEval`). -/
def multiopenCombine {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F)
    (incoming : Msm k F G) : Msm k F G × F :=
  (qCommitments.zip u).foldl
    (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
    (incoming.appendTerm (1 : F) qPrime, msmEval)

end Zcash.Snark
