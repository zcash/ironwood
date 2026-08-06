import Zcash.Snark.Core.Shape
import Zcash.Snark.Verifier.Expressions

/-!
# Verifier key data

The circuit-independent verifier receives these types as input.  Key generation and
circuit integration construct them; MSM assembly only consumes them.
-/

namespace Zcash.Snark

/-- A permutation column's evaluation reference (halo2 `get_any_query_index` + `column_type`): the
column's value is the advice / fixed / instance evaluation at the given query index. -/
inductive ColumnRef where
  | advice : ℕ → ColumnRef
  | fixed : ℕ → ColumnRef
  | instance : ℕ → ColumnRef
deriving DecidableEq, Repr

/-- Resolve a permutation column reference to its claimed evaluation. -/
def ColumnRef.resolve {F : Type*} (cr : ColumnRef) (instanceEvals adviceEvals fixedEvals : ℕ → F) : F :=
  match cr with
  | .advice i => adviceEvals i
  | .fixed i => fixedEvals i
  | .instance i => instanceEvals i

-- VK provenance: this circuit-independent assembler deliberately receives a `VerifyingKey` as
-- input, populated from the halo2 `dump_vesta_lean_fixture` capture
-- (`Fixtures/SingleAction/Honest/Fixture.lean`) — but it is not trusted verbatim:
-- `Keygen/Certificate.lean` proves the dumped key equals the one derived end-to-end from the
-- ported `configure`/keygen (`vk_eq_toVerifierKey`, transported to the multi-action key in
-- `Fixtures/MultiAction/Honest/VkCertificate.lean`), and the boundary statements consume the derived
-- key (`Fixtures/*/*/Boundary.lean`). The URS dump is checked in turn by the derived commitments
-- and the captured bases (see `Fingerprint/Match.lean`). Distinct from the output-side
-- semantic-adequacy gap (see `Soundness/Main.lean`).
/-- The verifying-key–level circuit structure the assembly needs, mirroring halo2's `VerifyingKey`
field-for-field: **circuit-fixed data only**. `omega` is the domain generator and `n = 2 ^ k` the
domain size; `blindingFactors`, `delta`, `chunkLen` are the permutation-argument constants. `gates`
are the custom-gate polynomials; `instance/advice/fixedQueryLayout` are the `(column, rotation)`
query lists; `fixedCommitment` and `permutationCommonCommitment` resolve column indices to
commitments; `permutationChunks` groups the permutation columns (with their common-eval indices) per
set; and `lookupInput/TableExprs` are the per-lookup input/table expressions.

The instance commitment is deliberately **not** a field: like halo2's `verify_proof`, the verifier
computes it per proof from the public instances (`commit_lagrange`) rather than reading it from the
VK, and supplies it to the assembly as a separate argument (`instanceCommitment` of
`assembleQueries`/`assemble`). This keeps the VK a faithful image of the pinned Rust key.

Two conventions hold for the deployed key but are not enforced by this structure:
* `n` is both Halo2's `params.n` and the domain size; the fixture exporter checks their equality.
* `permutationChunks` uses `chunkLen` as its stride, matching Halo2's `chunks(chunk_len)`; the
  captured key packs 7/7/1 columns with `chunkLen = 7`. -/
structure VerifyingKey (shape : CircuitShape) (F G : Type*) where
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
  permutationCommonCommitment : Fin shape.numPermutationColumns → G
  permutationChunks : List (List (ColumnRef × ℕ))
  lookupInputExprs : Fin shape.numLookups → List (Expr F)
  lookupTableExprs : Fin shape.numLookups → List (Expr F)

end Zcash.Snark
