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

open Zcash.Arithmetic (omegaOf pastaDomain_omega_eq pastaDomain_delta_eq)

namespace Zcash.Snark

open Zcash.Arithmetic
  (deltaFp omegaOf)

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

/-- The last usable Action row is exactly the verifier's negative rotation. -/
theorem lastRowRotation (urs : URS G) :
    (actionCircuit.toVerifierKey urs).omega ^
        ((actionCircuit.toVerifierKey urs).n - (actionCircuit.toVerifierKey urs).blindingFactors - 1) =
      (actionCircuit.toVerifierKey urs).omega ^
        (-(((actionCircuit.toVerifierKey urs).blindingFactors : ℤ) + 1)) :=
  actionCircuit.toVerifierKey_lastUsableRowRotation
    urs

set_option maxRecDepth 100000 in
/-- Action chunk names are injective on any active prefix of the derived
evaluation domain. This is the `hnames` premise retained by
`ResolverPermutationCycle.ofKeygenColumns`. -/
theorem namesInjective
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {activeRows : ℕ} (hactive : activeRows ≤ actionCircuit.n) :
    Function.Injective fun c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p activeRows =>
      chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
        actionCircuit.chunkLen c.1 c.2.1 c.2.2 := by
  have hRoot : IsPrimitiveRoot actionCircuit.omega actionCircuit.n :=
    CircuitFieldSupport.omega_isPrimitiveRoot actionCircuit
  have hfull :
      Function.Injective fun c :
          ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
            actionCircuit.n =>
        chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen c.1 c.2.1 c.2.2 := by
    apply chunkRowName_injective_of_actual_coset
    · intro j
      apply pow_ne_zero
      simpa only [pastaDomain_delta_eq] using
        (Zcash.Arithmetic.FieldDomainParams.delta_ne_zero (F := Fp))
    · exact hRoot.pow_eq_one
    · intro i i' hi hi' heq
      exact hRoot.pow_inj hi hi' heq
    · intro j j' t hcoset
      have hjWidth :
          (j.2 : ℕ) <
            min actionCircuit.chunkLen
              (actionCircuit.permutationColumnCount -
                (j.1 : ℕ) * actionCircuit.chunkLen) := by
        simpa only [actionCircuit.resolverPermutationPairs_length urs poly p j.1] using
          j.2.isLt
      have hj'Width :
          (j'.2 : ℕ) <
            min actionCircuit.chunkLen
              (actionCircuit.permutationColumnCount -
                (j'.1 : ℕ) * actionCircuit.chunkLen) := by
        simpa only [actionCircuit.resolverPermutationPairs_length urs poly p j'.1] using
          j'.2.isLt
      have hj :
          (j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hj' :
          (j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hglobal :=
        CircuitFieldSupport.eq_of_delta_pow_eq_omega_pow_mul actionCircuit
          ⟨_, hj⟩ ⟨_, hj'⟩ t (by
            simpa only [pastaDomain_delta_eq] using hcoset)
      have hindex :
          (j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ) =
            (j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ) :=
        congrArg Fin.val hglobal
      have hchunkLen :
          0 < actionCircuit.chunkLen :=
        constraintSystem_chunkLen_pos actionCircuit.constraintSystem
      have hjColumn :
          (j.2 : ℕ) < actionCircuit.chunkLen :=
        lt_of_lt_of_le j.2.isLt (by
          rw [actionCircuit.resolverPermutationPairs_length urs poly p j.1]
          exact min_le_left _ _)
      have hj'Column :
          (j'.2 : ℕ) < actionCircuit.chunkLen :=
        lt_of_lt_of_le j'.2.isLt (by
          rw [actionCircuit.resolverPermutationPairs_length urs poly p j'.1]
          exact min_le_left _ _)
      have hchunk :
          (j.1 : ℕ) = (j'.1 : ℕ) := by
        have hjDiv :
            ((j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen * (j.1 : ℕ) + (j.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j.1 : ℕ) +
                (j.2 : ℕ) / actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hjColumn, Nat.add_zero]
        have hj'Div :
            ((j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j'.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen * (j'.1 : ℕ) + (j'.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j'.1 : ℕ) +
                (j'.2 : ℕ) / actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j'.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hj'Column, Nat.add_zero]
        rw [← hjDiv, hindex, hj'Div]
      have hchunkFin : j.1 = j'.1 := Fin.ext hchunk
      have hcolumn : (j.2 : ℕ) = (j'.2 : ℕ) := by
        have hprefix :
            (j.1 : ℕ) * actionCircuit.chunkLen =
              (j'.1 : ℕ) * actionCircuit.chunkLen :=
          congrArg
            (fun chunk => chunk * actionCircuit.chunkLen)
            hchunk
        apply Nat.add_left_cancel
        exact hindex.trans (by rw [hprefix])
      have hwidth :
          (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p j.1).length =
            (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p j'.1).length :=
        congrArg
          (fun chunk : ℕ =>
            (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p chunk).length)
          hchunk
      apply Sigma.ext hchunkFin
      exact (Fin.heq_ext_iff hwidth).mpr hcolumn
  intro c d hname
  have hwiden := widenPermutationChunkCell_injective
    (nc := actionCircuit.permutationSetCount)
    (width := fun i =>
      (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p i).length)
    hactive
  have hwname :
      chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen
          (widenPermutationChunkCell hactive c).1
          (widenPermutationChunkCell hactive c).2.1
          (widenPermutationChunkCell hactive c).2.2 =
        chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen
          (widenPermutationChunkCell hactive d).1
          (widenPermutationChunkCell hactive d).2.1
          (widenPermutationChunkCell hactive d).2.2 := by
    simpa only [widenPermutationChunkCell_fst,
      widenPermutationChunkCell_row,
      widenPermutationChunkCell_column] using hname
  exact hwiden (hfull hwname)

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
      (namesInjective pp urs poly p hactive)

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

assert_no_sorry namesInjective
assert_no_sorry cycleOfKeygenColumnsAt
assert_no_sorry cycleOfKeygenColumns

end ActionPermutationDomain

end Zcash.Snark
