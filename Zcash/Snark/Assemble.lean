import Mathlib
import Zcash.Snark.ProofString
import Zcash.Snark.Challenges
import Zcash.Snark.Verifier
import Zcash.Snark.Queries
import Zcash.Snark.Expressions
import Zcash.Snark.Ipa

/-!
# Assembling the fingerprint MSM

This module composes the verified building blocks into the verifier's MSM assembly, in the exact order
of halo2 `plonk/verifier.rs`. It is the Lean image of the interactive verifier: a pure function of the
proof string, the challenges, and the verifying-key–level circuit structure.

The assembly factors into two halves connected by one deferred piece:

* `assembleQueries` (the upstream) — recompute the vanishing `h` commitment and `expected_h_eval`, then
  build the full ordered list of opening queries (per sub-proof: instance, advice, permutation, lookups;
  then shared: fixed, permutation-common, vanishing).
* `construct_intermediate_sets` (deferred) — group the flat query list into per-point-set commitment and
  evaluation data. This is VK-fixed query bookkeeping (it depends on the query layout, not the proof
  values); it is supplied here as a `MultiopenGrouped` value rather than re-derived, and is the one
  piece the fingerprint match (`MultiopenGrouped` from the captured run) exercises directly.
* `assembleFinalMsm` (the downstream) — the multiopen `x₁` compression and `x₄` collapse, then the IPA
  fold, producing the final MSM.

The verifying-key data (`VerifyingKey`) — gate polynomials, query layouts, fixed/permutation
commitments, the permutation column/eval chunking, lookup expressions — is circuit-fixed and supplied as
input; the instance commitments are statement-derived (the verifier computes them from the public
instances) and bundled here for the assembly.
-/

namespace Zcash.Snark

/-- A permutation column's evaluation reference (halo2 `get_any_query_index` + `column_type`): the
column's value is the advice / fixed / instance evaluation at the given query index. -/
inductive ColumnRef where
  | advice : ℕ → ColumnRef
  | fixed : ℕ → ColumnRef
  | instance : ℕ → ColumnRef

/-- Resolve a permutation column reference to its claimed evaluation. -/
def ColumnRef.resolve {F : Type*} (cr : ColumnRef) (instanceEvals adviceEvals fixedEvals : ℕ → F) : F :=
  match cr with
  | .advice i => adviceEvals i
  | .fixed i => fixedEvals i
  | .instance i => instanceEvals i

/-- The verifying-key–level circuit structure the assembly needs (halo2 `VerifyingKey` / `ConstraintSystem`).
`omega` is the domain generator and `n = 2 ^ k` the domain size; `blindingFactors`, `delta`, `chunkLen`
are the permutation-argument constants. `gates` are the custom-gate polynomials; `instance/advice/fixed
QueryLayout` are the `(column, rotation)` query lists; `fixedCommitment`, `permutationCommonCommitment`
and `instanceCommitment` (statement-derived) resolve column indices to commitments;
`permutationChunks` groups the permutation columns (with their common-eval indices) per set; and
`lookupInput/TableExprs` are the per-lookup input/table expressions. -/
structure VerifyingKey (shape : Shape) (F G : Type*) where
  omega : F
  n : ℕ
  blindingFactors : ℕ
  delta : F
  chunkLen : ℕ
  gates : List (Expr F)
  instanceQueryLayout : List (ℕ × ℤ)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  fixedCommitment : ℕ → G
  instanceCommitment : Fin shape.numProofs → ℕ → G
  permutationCommonCommitment : Fin shape.numPermutationColumns → G
  permutationChunks : List (List (ColumnRef × Fin shape.numPermutationColumns))
  lookupInputExprs : Fin shape.numLookups → List (Expr F)
  lookupTableExprs : Fin shape.numLookups → List (Expr F)

/-- View a `Fin n`-indexed family as a total `ℕ`-indexed function, `0` outside range (the query indices
the verifier uses are always in range). -/
def finFn {F : Type*} [Zero F] {n : ℕ} (f : Fin n → F) : ℕ → F :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

/-- View a `Fin n`-indexed family of group elements as a total `ℕ`-indexed function. -/
def finFnG {G : Type*} [Inhabited G] {n : ℕ} (f : Fin n → G) : ℕ → G :=
  fun i => if h : i < n then f ⟨i, h⟩ else default

/-- The `i`-th Lagrange basis polynomial of the size-`n` multiplicative domain, evaluated at `x` (halo2
`Polynomial::l_i_range`): `(xⁿ − 1) · ωⁱ / (n · (x − ωⁱ))`. -/
def lagrangeBasisValue {F : Type*} [Field F] (omega : F) (n : ℕ) (xn x : F) (i : ℤ) : F :=
  (xn - 1) * omega ^ i / ((n : F) * (x - omega ^ i))

/-- The three Lagrange basis values the vanishing check needs (halo2 `plonk/verifier.rs`): `l₀`
(rotation `0`), `l_last` (rotation `−(blinding+1)`), and `l_blind` (sum over rotations `−blinding..−1`). -/
def lagrangeBasis {F : Type*} [Field F] (omega : F) (n blinding : ℕ) (xn x : F) : F × F × F :=
  let l0 := lagrangeBasisValue omega n xn x 0
  let lLast := lagrangeBasisValue omega n xn x (-((blinding : ℤ) + 1))
  let lBlind := ((List.range blinding).map
    (fun j => lagrangeBasisValue omega n xn x (-((j : ℤ) + 1)))).foldl (· + ·) (0 : F)
  (l0, lLast, lBlind)

/-- The constraint values for one sub-proof (halo2 `plonk/verifier.rs`, the per-proof `flat_map`):
the gate-polynomial values, then the permutation-argument values, then the lookup-argument values. -/
def subProofExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F)
    (p : Fin shape.numProofs) : List F :=
  let fE := finFn ps.fixedEvals
  let aE := finFn (ps.adviceEvals p)
  let iE := finFn (ps.instanceEvals p)
  let gateE := vk.gates.map (fun g => g.eval fE aE iE)
  let sets := List.ofFn (fun s => ps.permutationSetEvals p s)
  let chunks := (sets.zip vk.permutationChunks).map (fun sc =>
    (sc.1, sc.2.map (fun cr => (cr.1.resolve iE aE fE, ps.permutationCommonEvals cr.2))))
  let permE := permutationExpressions sets chunks ch.beta ch.gamma ch.x vk.delta vk.chunkLen l0 lLast lBlind
  let lookupE := (List.ofFn (fun l => lookupExpressions (ps.lookupEvals p l)
    (vk.lookupInputExprs l) (vk.lookupTableExprs l) fE aE iE ch.theta ch.beta ch.gamma l0 lLast lBlind)).flatten
  gateE ++ permE ++ lookupE

/-- All constraint values across the sub-proofs, in the verifier's order. -/
def allExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F) : List F :=
  (List.ofFn (fun p => subProofExpressions vk ps ch l0 lLast lBlind p)).flatten

/-- The verifier's full ordered list of opening queries (halo2 `plonk/verifier.rs`): recompute the
vanishing `h` commitment and `expected_h_eval`, then chain, per sub-proof, the instance / advice /
permutation / lookup queries, followed by the shared fixed / permutation-common / vanishing queries. -/
def assembleQueries {shape : Shape} {F G : Type*} [Field F] [Inhabited G] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : List (VerifierQuery shape.k F G) :=
  let x := ch.x
  let xn := x ^ vk.n
  let xNext := rotateOmega vk.omega x 1
  let xInv := rotateOmega vk.omega x (-1)
  let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
  let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
  let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
  let eHEval := expectedHEval exprs ch.y xn
  let hComm := vanishingHCommitment shape.k xn (List.ofFn ps.hPieces)
  let perProof := (List.ofFn (fun p =>
    columnQueries vk.omega x (vk.instanceCommitment p) vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p))
    ++ columnQueries vk.omega x (finFnG (ps.adviceCommitments p)) vk.adviceQueryLayout
        (List.ofFn (ps.adviceEvals p))
    ++ permutationQueries x xNext xLast
        (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))
    ++ lookupQueries x xInv xNext (List.ofFn (fun l =>
        ({ product := ps.lookupProduct p l, permutedInput := ps.lookupPermutedInput p l,
           permutedTable := ps.lookupPermutedTable p l }, ps.lookupEvals p l))))).flatten
  let fixedQ := columnQueries vk.omega x vk.fixedCommitment vk.fixedQueryLayout (List.ofFn ps.fixedEvals)
  let permCommonQ := permutationCommonQueries x
    (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
  let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
  perProof ++ fixedQ ++ permCommonQ ++ vanishingQ

/-- The multiopen point-set grouping (halo2 `construct_intermediate_sets` output): per point set, the
queries grouped into it (in processing order) as `(commitment, evaluations at this set's points)`, and
the set's points. Supplied as input (VK-fixed query bookkeeping). -/
structure MultiopenGrouped (k : ℕ) (F G : Type*) where
  sets : List (List (CommitmentRef k F G × List F))
  points : List (List F)

/-- Compress one point set by the `x₁` powers (halo2 `multiopen/verifier.rs` `accumulate`): fold the
set's query contributions, accumulating both the commitment MSM (`Σⱼ x₁ʲ cⱼ`) and the per-point
evaluation vector (`Σⱼ x₁ʲ evalsⱼ`). -/
def compressSet {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ) : Msm k F G × List F :=
  let res := setQueries.foldl (fun (st : Msm k F G × List F × F) qc =>
      (accumulateCommitment st.2.2 qc.1 st.1,
       (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
       st.2.2 * x1))
    (Msm.zero k F G, List.replicate numPoints (0 : F), (1 : F))
  (res.1, res.2.1)

/-- The multiopen opening MSM and combined value (halo2 `multiopen/verifier.rs`): compress each point
set by `x₁`, compute the combined evaluation by Lagrange interpolation at `x₃` (`multiopenEval`), then
collapse by `x₄` against `q'` (`multiopenCombine`). `u` are the prover's claimed per-set quotient
evaluations. -/
def assembleOpening {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) : Msm k F G × F :=
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet x1 sp.1 sp.2.length)
  let qCommitments := compressed.map Prod.fst
  let setsForEval := ((grouped.points.zip (compressed.map Prod.snd)).zip u).map
    (fun p => (p.1.1, p.1.2, p.2))
  let msmEval := multiopenEval x2 x3 setsForEval
  multiopenCombine x4 qPrime qCommitments u msmEval incoming

/-- The final fingerprint MSM (halo2 `plonk/verifier.rs` → `multiopen/verifier.rs` →
`commitment/verifier.rs`): the multiopen opening, then the IPA fold opening it at `x₃` to the combined
value. `grouped` is the `construct_intermediate_sets` output for `assembleQueries vk ps ch`. -/
def assembleFinalMsm {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) : Msm shape.k F G :=
  let opened := assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    grouped (Msm.zero shape.k F G)
  ipaFold ch.x3 opened.2 ps.ipaC ps.ipaF ch.xi ch.z (List.ofFn ch.ipaRound) ps.ipaS
    (List.ofFn ps.ipaRounds) opened.1

end Zcash.Snark
