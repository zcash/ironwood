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

The structure deliberately does not force its lists to agree with the shape's counts, mirroring
halo2, which upholds those agreements by construction (one evaluation read per query; chunks built
by `chunks(chunk_len)`).  Where the Lean split makes disagreement representable, the assembly
degrades rather than rejects — `columnQueries` zips truncate, `finFn`/`finFnG` alias out-of-range
indices to `0`/`default`, and `subProofPermSets.zip vk.permutationChunks` drops unmatched sets —
so supported-key soundness interfaces require `VerifyingKey.WellFormed`. It supplies query-layout
lengths, permutation chunk counts and widths, in-range zero-rotation permutation references,
and room for the blinding rows. `VerifyingKey.FieldSupport` separately ties the domain size,
root and permutation separator to certified field parameters. Derived keys instantiate both;
captured keys inherit them through the keygen equality certificate.

Expression-reference bounds remain separate (`vk_expression_refs_in_range` in fixture
faithfulness). A key outside the required agreements can silently check fewer constraints, so
alternate key-loading or circuit-version paths must establish the same laws. -/
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
