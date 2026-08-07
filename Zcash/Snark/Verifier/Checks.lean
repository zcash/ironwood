import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Arithmetic
import Zcash.Arithmetic.Msm

/-!
# The verifier's MSM assembly

This module assembles the fingerprint MSM the way the deployed verifier does (`plonk/verifier.rs`
together with the `poly/{multiopen,commitment}` openings): build the per-argument query commitments,
compress them through the multiopen folds, and finish with the inner-product-argument opening
(`Zcash.Snark.ipaFold`).

What this file provides:
* `CommitmentRef`, `VerifierQuery` — the shared query types (halo2 `CommitmentReference` / `VerifierQuery`).
* `vanishingHCommitment` — the vanishing argument's `h` commitment.
* `accumulateCommitment`, `compressQCommitments`, `multiopenCombine` — the multiopen `x₁` compression and
  `x₄` collapse (`multiopen/verifier.rs`).
* `lagrangeEval`, `multiopenEval` — the multiopen combined value `v` (the Lagrange interpolation step).

The primitives here take the point-set grouping as input — VK-fixed bookkeeping, re-derived in
`Verifier/Assemble.lean` (`constructIntermediateSets`); everything downstream (the `x₁`/`x₄`
folds and the combined value `v`) is computed here.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

/-- A multiopen query's commitment reference (halo2 `CommitmentReference`): either a single group
element, or an MSM — the vanishing argument's folded `h` commitment is supplied as an MSM. -/
inductive CommitmentRef (k : ℕ) (F G : Type*) where
  | point : G → CommitmentRef k F G
  | msm : Msm k F G → CommitmentRef k F G
  deriving DecidableEq

/-- A commitment's slot identity — which commitment object it is, independent of its curve value.
Models halo2's pointer identity (`construct_intermediate_sets` keys by `std::ptr::eq`): the
grouping must keep two distinct slots distinct even when their curve values coincide. Each
constructor names a commitment source with its structural indices. -/
inductive CommitmentId where
  | instanceCol : ℕ → ℕ → CommitmentId
  | adviceCol : ℕ → ℕ → CommitmentId
  | fixedCol : ℕ → CommitmentId
  | permProduct : ℕ → ℕ → CommitmentId
  | lookupProduct : ℕ → ℕ → CommitmentId
  | lookupPermInput : ℕ → ℕ → CommitmentId
  | lookupPermTable : ℕ → ℕ → CommitmentId
  | permCommon : ℕ → CommitmentId
  | vanishingH : CommitmentId
  | randomPoly : CommitmentId
  deriving DecidableEq

/-- A multiopen query (halo2 `VerifierQuery`): open `commitment` at `point`, claiming the value
`eval`. `commId` is the slot identity used as the grouping key (see `CommitmentId`). -/
structure VerifierQuery (k : ℕ) (F G : Type*) where
  point : F
  commitment : CommitmentRef k F G
  eval : F
  commId : CommitmentId

/-- The vanishing argument's `h` commitment (halo2 `vanishing/verifier.rs`): the commitment to the
quotient polynomial, reassembled from its degree-bounded pieces as `Σᵢ hᵢ · (xⁿ)ⁱ`. Built as the
Rust builds it. -/
def vanishingHCommitment {F G : Type*} [Field F] (k : ℕ) (xn : F) (hPieces : List G) : Msm k F G :=
  hPieces.reverse.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) (Msm.zero k F G)

/-- Accumulate one query commitment into a point set's compressed commitment, weighted by the
current `x₁` power (the multiopen `accumulate` closure): a plain commitment appends as a term; an
MSM commitment is scaled and added. -/
def accumulateCommitment {k : ℕ} {F G : Type*} [Field F] (pow : F) (c : CommitmentRef k F G)
    (acc : Msm k F G) : Msm k F G :=
  match c with
  | .point p => acc.appendTerm pow p
  | .msm m => acc.add (m.scale pow)

/-- The group value a commitment reference contributes to the MSM: a point is itself; an MSM is its
evaluation against the URS. -/
def CommitmentRef.eval {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G) :
    CommitmentRef urs.k F G → G
  | .point p => p
  | .msm m => m.eval urs

/-- The multiopen `x₁` compression (`multiopen/verifier.rs`): fold each point set's commitments
into `Σⱼ x₁ʲ · cⱼ`. A standalone building block — the live path fuses this with the evaluation
fold in `compressSet`. -/
def compressQCommitments {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sets : List (List (CommitmentRef k F G))) : List (Msm k F G) :=
  sets.map fun setCommitments =>
    (setCommitments.foldl (fun (st : Msm k F G × F) c => (accumulateCommitment st.2 c st.1, st.2 * x1))
      (Msm.zero k F G, (1 : F))).1

/-- The multiopen `x₄` collapse (`multiopen/verifier.rs`): weight the per-set compressed
commitments and their claimed evaluations `u` by powers of `x₄` into one commitment/value claim —
so a single IPA opening checks every point set at once. `qPrime` is the prover's quotient
commitment; `msmEval` seeds the combined value. -/
def multiopenCombine {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F)
    (incoming : Msm k F G) : Msm k F G × F :=
  (qCommitments.zip u).foldl
    (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
    (incoming.appendTerm (1 : F) qPrime, msmEval)

/-- The value at `x` of the polynomial interpolating `(points, evals)`, in barycentric Lagrange
form `Σᵢ evalsᵢ · ∏_{j≠i} (x − pⱼ)/(pᵢ − pⱼ)` — the same field element as halo2's
`eval_polynomial (lagrange_interpolate points evals) x` when `points` are distinct.
`constructIntermediateSets_points_nodup` proves this on the assembly path, matching Halo2's
`BTreeSet` deduplication, so their different zero-denominator behavior is unreachable. -/
def lagrangeEval {F : Type*} [Field F] (x : F) (points evals : List F) : F :=
  let n := points.length
  (List.range n).foldl (fun acc i =>
    let pi := points.getD i 0
    let li := (List.range n).foldl (fun p j =>
      if j = i then p else p * (x - points.getD j 0) / (pi - points.getD j 0)) (1 : F)
    acc + evals.getD i 0 * li) (0 : F)

/-- The multiopen combined evaluation `msm_eval` (`multiopen/verifier.rs`): per point set, the
claimed quotient evaluation `u` and the interpolant `r` of the set's openings combine into
`(u − r(x₃)) / ∏ (x₃ − pt)`; the sets then fold together by `x₂`. This is the value side of
reducing many-point openings to a single opening at `x₃`. -/
def multiopenEval {F : Type*} [Field F] (x2 x3 : F) (sets : List (List F × List F × F)) : F :=
  sets.foldl (fun msmEval s =>
    let rEval := lagrangeEval x3 s.1 s.2.1
    let evalSet := s.1.foldl (fun e point => e * (x3 - point)⁻¹) (s.2.2 - rEval)
    msmEval * x2 + evalSet) (0 : F)

end Zcash.Snark
