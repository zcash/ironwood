import Zcash.Circuits.Action.FieldSupport
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Mathlib.Util.AssertNoSorry

/-!
# Action permutation domain and verifier layout

This module discharges the domain and chunk-layout premises retained by the
generic permutation semantics for the verifying key derived from
`actionCircuit`.

The keygen permutation itself belongs to the separate replay/assembly layer.
`cycleOfKeygenColumns` therefore accepts `fullSigma`, its active restriction,
the restriction equation, and the common-column identification explicitly.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

variable {G : Type} [AddCommGroup G] [Inhabited G]

abbrev actionShape (pp : ProofParams) : Shape :=
  actionCircuit.shape.withProofParams pp

/--
Flattening the derived verifier chunks and decoding their query references
recovers the compiler's original permutation-column order.
-/
theorem permutationColumnAddresses_eq
    (urs : URS G) :
    (actionCircuit.verifierCS.permutationChunks.flatten.map
        (fun reference =>
          permutationColumnAddress (actionCircuit.toVerifierKey urs) reference.1)) =
      (Keygen.permColsOf
        actionCircuit.constraintSystem).map
          Halo2.Layout.ColRef.toAny := by
  simpa only [actionCircuit.toVerifierKey_permutationChunks] using
    topLevelPermutationColumnAddresses_eq actionCircuit urs

/-! ## Derived evaluation-domain facts -/

/-- The active permutation prefix ends at the last usable Action row. -/
def activeRows : ℕ :=
  actionCircuit.n - actionCircuit.blindingFactors - 1

theorem activeRows_le :
    activeRows ≤ actionCircuit.n := by
  unfold activeRows
  omega

/-- Assemble the semantic cycle at any active-row prefix preserved by the
replayed full permutation. -/
def cycleOfKeygenColumnsAt
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {m : ℕ}
    (hactive : m ≤ actionCircuit.n)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        actionCircuit.n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        m))
    (hcolumns : ∀
      (chunk : Fin actionCircuit.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionCircuit.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p m,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma
          (widenPermutationChunkCell hactive c)) :
    ResolverPermutationCycle (actionCircuit.toVerifierKey urs) poly p m :=
  actionCircuit.resolverPermutationCycleOfKeygenColumns
    urs poly p hactive fullSigma sigma
      hcolumns hrestrict

/-- Assemble the semantic cycle at the verifier-derived active-row boundary. -/
def cycleOfKeygenColumns
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        actionCircuit.n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        activeRows))
    (hcolumns : ∀
      (chunk : Fin actionCircuit.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionCircuit.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
          activeRows,
      widenPermutationChunkCell activeRows_le (sigma c) =
        fullSigma
          (widenPermutationChunkCell activeRows_le c)) :
    ResolverPermutationCycle (actionCircuit.toVerifierKey urs) poly p
      activeRows :=
  cycleOfKeygenColumnsAt pp urs poly p activeRows_le
    fullSigma sigma hcolumns hrestrict

assert_no_sorry cycleOfKeygenColumnsAt
assert_no_sorry cycleOfKeygenColumns

end ActionPermutationDomain

end Zcash.Snark
