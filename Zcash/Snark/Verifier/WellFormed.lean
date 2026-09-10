import Zcash.Snark.Verifier.Key

/-! # Structural laws of a verifying key

These are agreements between a key's lists, indices and declared shape. They do
not depend on the scalar field's domain convention or on commitment binding.
-/

namespace Zcash.Snark

/-- A permutation reference names an in-range query at rotation zero. -/
def PermutationColumnRef.Coherent {shape : CircuitShape} {F G : Type*}
    (vk : VerifyingKey shape F G) : ColumnRef → Prop
  | .advice i =>
      i < shape.numAdviceQueries ∧ i < vk.adviceQueryLayout.length ∧
        (vk.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < shape.numFixedQueries ∧ i < vk.fixedQueryLayout.length ∧
        (vk.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < shape.numInstanceQueries ∧ i < vk.instanceQueryLayout.length ∧
        (vk.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Every permutation pair routes to a valid value query and common column. -/
def PermutationChunkRoutingCoherent {shape : CircuitShape} {F G : Type*}
    (vk : VerifyingKey shape F G) : Prop :=
  ∀ chunk ∈ vk.permutationChunks, ∀ ref ∈ chunk,
    PermutationColumnRef.Coherent vk ref.1 ∧ ref.2 < shape.numPermutationColumns

namespace VerifyingKey

variable {shape : CircuitShape} {F G : Type*}

/-- The key's query layouts and permutation chunks agree with its shape, and its
domain has room for the blinding rows and the last usable row. -/
class WellFormed (vk : VerifyingKey shape F G) : Prop where
  adviceQueryLayout_length : vk.adviceQueryLayout.length = shape.numAdviceQueries
  instanceQueryLayout_length : vk.instanceQueryLayout.length = shape.numInstanceQueries
  fixedQueryLayout_length : vk.fixedQueryLayout.length = shape.numFixedQueries
  blindingFactors_add_one_lt_n : vk.blindingFactors + 1 < vk.n
  chunkLen_pos : 0 < vk.chunkLen
  permutationChunks_length : vk.permutationChunks.length = shape.numPermutationSets
  permutationChunks_getD_length : ∀ i < vk.permutationChunks.length,
    (vk.permutationChunks.getD i []).length =
      min vk.chunkLen (shape.numPermutationColumns - i * vk.chunkLen)
  permutationChunkRoutingCoherent : PermutationChunkRoutingCoherent vk

/-- Extending a circuit shape with invocation parameters preserves key lawfulness. -/
instance wellFormedWithProofParams (vk : VerifyingKey shape F G) [WellFormed vk]
    (pp : ProofParams) : WellFormed (shape := shape.withProofParams pp) vk := by
  simpa only [Halo2.CircuitShape.withProofParams_toCircuitShape] using
    (inferInstance : WellFormed vk)

theorem blindingFactors_lt_n (vk : VerifyingKey shape F G) [WellFormed vk] :
    vk.blindingFactors < vk.n :=
  Nat.lt_of_succ_lt (WellFormed.blindingFactors_add_one_lt_n (vk := vk))

end VerifyingKey

end Zcash.Snark
