import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.TopLevel
import Zcash.Arithmetic.CommitLagrange
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Concrete certificate for the derived Action verifying key

One bundled `native_decide` compares every field of the derived verifying key against the
capture. The `FixtureCheck` target builds it; ordinary clients need only the generic keygen
pipeline.

Three evaluation choices are load-bearing, each measured against a slower alternative:

* Sequential commitment cores, not `parMap`: nullary sharing does not survive a task fan-out
  here, so every column task re-ran the whole basis derivation. Let-binding the basis instead
  shares correctly but blows the elaborator's budget at proof-term finalization.
* No group FFT. `commitLagrangeSpec_derivedUrsGLagrange` inverse-DFTs each column as scalars
  and commits against the monomial URS. The Lagrange prefix is 10 monomial MSMs
  (`take_derivedUrsGLagrange_natPre`), not an FFT prefix, which would force the transform back.
* The `Nat` kernel lane (`msmNatPre`, `commitInvDftNatWith`), proven equal to the statement
  surface by `msm_spec`. Everything evaluates in the interpreter.
-/

namespace Zcash.Snark.Keygen

open Zcash.Arithmetic (commitInvDftNatWith commitInvDftNatWith_eq commitNatPre deltaFp
  derivedUrsGLagrange lagrangeRow ofPVes omegaOf
  take_derivedUrsGLagrange_natPre)

open Zcash.Snark
open Zcash.Snark.Fixture
open Halo2
open Zcash.Circuits.Action (actionCircuit actionCircuit_shape_eq)
open CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Fast.NatKernel (P3)
open CompElliptic.Curves.Pasta.Fast.Projective.PVes (ofAffine)

/-- The Action circuit's proof-shape parameters at an arbitrary bundle size.  The proof count is
the number of Actions carried by the Halo 2 proof; the five multiopen point sets are protocol
constant. -/
def actionProofParamsFor (numProofs : ℕ) : ProofParams :=
  { numProofs, numPointSets := 5 }

/-- The captured fixture's one-Action proof-shape parameters.  Keeping this name as the captured
specialization lets the expensive certificate below remain a single computation; consensus-sized
capstones transport its circuit-owned fields instead of re-running key generation. -/
def actionProofParams : ProofParams := actionProofParamsFor 1

@[simp] theorem actionProofParamsFor_numProofs (numProofs : ℕ) :
    (actionProofParamsFor numProofs).numProofs = numProofs := rfl

@[simp] theorem actionProofParamsFor_numPointSets (numProofs : ℕ) :
    (actionProofParamsFor numProofs).numPointSets = 5 := rfl

@[simp] theorem actionProofParamsFor_one : actionProofParamsFor 1 = actionProofParams := rfl

/-- The MONOMIAL URS as canonical-`ℕ` triples — THE shared basis of every MSM in the bundle
(all 44 columns and the 10 Lagrange-prefix generators). Nullary, so the coordinate conversion
runs once on the main evaluation thread (all uses are single-threaded). -/
private def monomialBasis : List P3 :=
  (List.ofFn capturedURS.g).map fun g => ofPVes (ofAffine g)

/-- The per-column committer: the column's scalar inverse DFT (`bestFftG` at `Fp`,
GMP-backed), then one scatter Pippenger on the `Nat` kernel against the shared monomial
basis. -/
private def commitProj : List Fp → G :=
  commitInvDftNatWith Fast.Msm.defaultWindow capturedURS.k capturedURS.w monomialBasis

/-- The derived Lagrange URS prefix the bundle cross-checks: one monomial MSM per generator
of the closed coefficient row `n⁻¹·ω^(−j·t)`. -/
private def lagrangeBasis : List G :=
  List.ofFn fun j : Fin capturedUrsGLagrange.length =>
    commitNatPre Fast.Msm.defaultWindow 0 monomialBasis
      (lagrangeRow capturedURS.k (j : ℕ))

/-- The shared pinned view used by the native certificate bundle. -/
private def actionPinned : PinnedConstraintSystem Fp :=
  actionCircuit.pinnedCS

/--
The certificate's evaluation-shared spelling of the Action permutation chunks.
The theorem immediately below identifies it with the public verifier-CS view.
-/
private def actionPermutationChunks :
    List (List (ColumnRef × ℕ)) :=
  let reference : AnyColumn → ColumnRef := fun column =>
    match column.kind with
    | .advice =>
        .advice (actionPinned.adviceQueryLayout.findIdx
          (· = (column.index, 0)))
    | .fixed =>
        .fixed (actionPinned.fixedQueryLayout.findIdx
          (· = (column.index, 0)))
    | .instance =>
        .instance (actionPinned.instanceQueryLayout.findIdx
          (· = (column.index, 0)))
  ((actionCircuit.constraintSystem.permutationColumns.map
    reference).zipIdx).toChunks actionCircuit.constraintSystem.chunkLen

/-- The evaluation-shared certificate computation is the circuit-owned
verifier permutation layout. -/
private theorem actionPermutationChunks_eq_verifierCS :
    actionPermutationChunks =
      actionCircuit.verifierCS.permutationChunks := by
  simp only [actionPermutationChunks, TopLevelCircuit.verifierCS,
    actionPinned, TopLevelCircuit.chunkLen,
    TopLevelCircuit.permutationColumns]
  apply congrArg (fun references : List ColumnRef =>
    references.zipIdx.toChunks
      actionCircuit.constraintSystem.chunkLen)
  apply List.map_congr_left
  intro column _
  cases column.kind <;> rfl


/-- `Decidable` instance for the bundle, CONSTRUCTED leaf-by-leaf (see the module
docstring). -/
private instance bundleDecEq : DecidableEq (List G × List G × List G ×
    (Fp × ℕ × ℕ × Fp × ℕ) ×
    List (Expr Fp) ×
    (List (ℕ × ℤ) × List (ℕ × ℤ) × List (ℕ × ℤ)) ×
    List (List (Snark.ColumnRef × ℕ)) ×
    (List (List (Expr Fp)) × List (List (Expr Fp)))) := by
  repeat' first
    | refine @instDecidableEqProd _ _ ?_ ?_
    | infer_instance

/-- A fieldwise equality across a `CircuitShape` transport reconstructs equality of
the dependent verifying-key records. -/
private theorem verifyingKey_eq_cast_of_fields
    {s₁ s₂ : CircuitShape} {F G : Type*}
    (hshape : s₁ = s₂)
    (left : VerifyingKey s₁ F G)
    (right : VerifyingKey s₂ F G)
    (omega : left.omega = right.omega)
    (n : left.n = right.n)
    (blindingFactors : left.blindingFactors = right.blindingFactors)
    (delta : left.delta = right.delta)
    (chunkLen : left.chunkLen = right.chunkLen)
    (gates : left.gates = right.gates)
    (instanceQueryLayout :
      left.instanceQueryLayout = right.instanceQueryLayout)
    (adviceQueryLayout :
      left.adviceQueryLayout = right.adviceQueryLayout)
    (fixedQueryLayout :
      left.fixedQueryLayout = right.fixedQueryLayout)
    (fixedCommitment :
      left.fixedCommitment = right.fixedCommitment)
    (permutationCommonCommitment :
      ∀ column,
        left.permutationCommonCommitment column =
          right.permutationCommonCommitment
            (Fin.cast
              (congrArg CircuitShape.numPermutationColumns hshape)
              column))
    (permutationChunks :
      left.permutationChunks = right.permutationChunks)
    (lookupInputExprs :
      ∀ lookup,
        left.lookupInputExprs lookup =
          right.lookupInputExprs
            (Fin.cast (congrArg CircuitShape.numLookups hshape) lookup))
    (lookupTableExprs :
      ∀ lookup,
        left.lookupTableExprs lookup =
          right.lookupTableExprs
            (Fin.cast (congrArg CircuitShape.numLookups hshape) lookup)) :
    hshape ▸ left = right := by
  cases hshape
  have permutationCommonCommitment' :
      left.permutationCommonCommitment =
        right.permutationCommonCommitment :=
    funext fun column => by
      simpa using permutationCommonCommitment column
  have lookupInputExprs' :
      left.lookupInputExprs = right.lookupInputExprs :=
    funext fun lookup => by
      simpa using lookupInputExprs lookup
  have lookupTableExprs' :
      left.lookupTableExprs = right.lookupTableExprs :=
    funext fun lookup => by
      simpa using lookupTableExprs lookup
  have hkey : left = right := by
    cases left
    cases right
    simp_all
  simpa only using hkey

/-- **The derived verifying key matches the capture, field by field** — bundled into ONE
`native_decide` so the shared work (the monomial basis, fixed contents, keygen mapping
and all 44 commitment MSMs) evaluates exactly once. Components, in order: the Lagrange
URS 10-generator prefix; the 29 fixed-column and 15 permutation commitments; the
domain/permutation scalars; the gates; the three query layouts; the permutation
chunks; and the two lookup-expression families. -/
theorem certificate :
    (lagrangeBasis.take capturedUrsGLagrange.length,
      fixedCommitmentsSeqWith commitProj
        actionCircuit.fixedRows,
      permutationCommitmentsSeqWith commitProj
        actionCircuit.domainExponent
        actionCircuit.constraintSystem
        (actionCircuit.operations),
      (omegaOf actionCircuit.domainExponent,
        2 ^ actionCircuit.domainExponent,
        actionCircuit.constraintSystem.blindingFactors, deltaFp,
        actionCircuit.constraintSystem.chunkLen),
      actionPinned.gates.map RichExpression.toExpr,
      (actionPinned.instanceQueryLayout,
        actionPinned.adviceQueryLayout,
        actionPinned.fixedQueryLayout),
      actionPermutationChunks,
      (List.ofFn fun lookup : Fin shape.numLookups =>
          (actionPinned.lookupInputExprs.getD lookup.val []).map
            RichExpression.toExpr,
       List.ofFn fun lookup : Fin shape.numLookups =>
          (actionPinned.lookupTableExprs.getD lookup.val []).map
            RichExpression.toExpr))
    = (capturedUrsGLagrange,
       capturedFixedCommitments,
       capturedPermutationCommonCommitments,
       (vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen),
       vk.gates,
       (vk.instanceQueryLayout, vk.adviceQueryLayout, vk.fixedQueryLayout),
       vk.permutationChunks,
       (List.ofFn vk.lookupInputExprs, List.ofFn vk.lookupTableExprs)) := by
  native_decide

/-- The fixture's full proof shape is the Action circuit shape combined with the captured
proof parameters. -/
theorem actionShape_eq_fixtureShape :
    actionCircuit.shape.withProofParams actionProofParams = shape := by
  rw [actionCircuit_shape_eq]
  rfl

/-- Changing the bundle size changes only the `numProofs` field of the captured Action shape.
This follows definitionally from the reduced circuit shape and proof parameters. -/
theorem actionShapeFor_eq_fixtureShape (numProofs : ℕ) :
    actionCircuit.shape.withProofParams (actionProofParamsFor numProofs) =
      { Zcash.Snark.Fixture.shape with numProofs := numProofs } := by
  rw [← actionShape_eq_fixtureShape]
  simp only [Halo2.CircuitShape.withProofParams, actionProofParamsFor, actionProofParams]

/-- The circuit-owned portion of the captured fixture shape is exactly the Action circuit's
derived shape. -/
theorem actionCircuitShape_eq_fixtureCircuitShape :
    actionCircuit.shape = shape.toCircuitShape := by
  rw [actionCircuit_shape_eq]
  rfl

/-- The keygen domain exponent the columns are built at is the captured URS's `k`, so the
column length the commitment families produce is the domain the committer's inverse DFT runs
over. The circuit side comes from the proved planner trace; the capture merely records `k = 11`. -/
private theorem domainExponent_eq :
    actionCircuit.domainExponent = capturedURS.k := by
  rw [TopLevelCircuit.domainExponent, actionCircuit_shape_eq]
  rfl

set_option maxRecDepth 1000000 in
/-- **The bundle's per-column committer IS the pipeline's affine default at the derived
Lagrange basis**, on every full-domain column: `commitInvDftNatWith_eq` is the
bilinearity theorem with the kernel MSM on the group half. -/
private theorem committer_eq (l : List Fp)
    (hl : l.length = actionCircuit.n) :
    commitProj l = Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow capturedURS.w
      (derivedUrsGLagrange capturedURS) l := by
  rw [Fast.Msm.commitLagrangeFastWith_eq _ (by decide)]
  simp only [commitProj, monomialBasis]
  rw [commitInvDftNatWith_eq Fast.Msm.defaultWindow (by decide)
    capturedURS (by decide) l
      (by
        rw [hl, actionCircuit.n_eq_two_pow_domainExponent,
          domainExponent_eq])]

/-- Every Clean-compiled Action fixed row spans the full evaluation domain. -/
private theorem fixedRowLength (row : List Fp)
    (hrow : row ∈ actionCircuit.fixedRows) :
    row.length = actionCircuit.n := by
  obtain ⟨column, hcolumn, rfl⟩ := List.mem_iff_getElem.mp hrow
  have hcolumn' :
      column < actionCircuit.fixedColumnCount := by
    simpa only [actionCircuit.fixedRows_length] using hcolumn
  have hlength :=
    actionCircuit.fixedRows_getD_length column hcolumn'
  rwa [List.getD_eq_getElem _ _ hcolumn] at hlength

set_option maxRecDepth 1000000 in
/-- The derived Lagrange URS reproduces the captured 10-generator prefix. -/
theorem derivedUrsGLagrange_prefix_eq :
    (derivedUrsGLagrange capturedURS).take capturedUrsGLagrange.length
      = capturedUrsGLagrange := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have h1 := h.1
  simp only [lagrangeBasis, monomialBasis] at h1
  rw [List.take_of_length_le (by simp)] at h1
  rw [take_derivedUrsGLagrange_natPre Fast.Msm.defaultWindow (by decide) capturedURS
    (by decide) capturedUrsGLagrange.length (by decide)]
  exact h1

set_option maxRecDepth 1000000 in
/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    actionCircuit.fixedCommitments capturedURS =
      capturedFixedCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hfc := h.2.1
  rw [fixedCommitmentsSeqWith_congr
      actionCircuit.fixedRows
      (fun row hrow => committer_eq row (fixedRowLength row hrow)),
    fixedCommitmentsSeqWith_eq] at hfc
  simp only [fixedCommitmentsWith] at hfc
  simp only [Halo2.TopLevelCircuit.fixedCommitments]
  exact hfc

set_option maxRecDepth 1000000 in
/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    actionCircuit.permutationCommitments capturedURS
      = capturedPermutationCommonCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hpc := h.2.2.1
  rw [permutationCommitmentsSeqWith_congr _ _ _ committer_eq,
    permutationCommitmentsSeqWith_eq] at hpc
  simp only [Halo2.TopLevelCircuit.permutationCommitments,
    permutationCommitmentsOf]
  exact hpc

set_option maxRecDepth 1000000 in
/-- **`vk = actionCircuit.toVerifierKey capturedURS`**
— the captured Orchard Action verifying key is the closed circuit's derived verifying
key, transported only along the equality of their circuit-owned shapes. -/
theorem vk_eq_toVerifierKey :
    vk = actionCircuitShape_eq_fixtureCircuitShape
      ▸ actionCircuit.toVerifierKey capturedURS := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, -, -, ⟨ho, hn, hb, hd, hc⟩, hg,
    ⟨hiq, haq, hfq⟩, hpch, ⟨hli, hlt⟩⟩ := h
  symm
  apply verifyingKey_eq_cast_of_fields actionCircuitShape_eq_fixtureCircuitShape
  · simpa only [actionCircuit.toVerifierKey_omega,
      TopLevelCircuit.omega] using ho
  · simpa only [actionCircuit.toVerifierKey_n,
      actionCircuit.n_eq_two_pow_domainExponent] using hn
  · simpa only [actionCircuit.toVerifierKey_blindingFactors,
      TopLevelCircuit.blindingFactors] using hb
  · simpa only [actionCircuit.toVerifierKey_delta] using hd
  · simpa only [actionCircuit.toVerifierKey_chunkLen,
      TopLevelCircuit.chunkLen] using hc
  · simpa only [actionCircuit.toVerifierKey_gates,
      actionCircuit.verifierCS_gates, actionPinned] using hg
  · simpa only [actionCircuit.toVerifierKey_instanceQueryLayout,
      TopLevelCircuit.instanceQueryLayout, actionPinned] using hiq
  · simpa only [actionCircuit.toVerifierKey_adviceQueryLayout,
      TopLevelCircuit.adviceQueryLayout, actionPinned] using haq
  · simpa only [actionCircuit.toVerifierKey_fixedQueryLayout,
      TopLevelCircuit.fixedQueryLayout, actionPinned] using hfq
  · funext column
    rw [actionCircuit.toVerifierKey_fixedCommitment,
      derivedFixedCommitments_eq]
    simp only [Fixture.vk]
  · intro column
    rw [actionCircuit.toVerifierKey_permutationCommonCommitment,
      derivedPermutationCommonCommitments_eq]
    simp only [Fixture.vk, Fin.val_cast]
  · rw [actionCircuit.toVerifierKey_permutationChunks,
      ← actionPermutationChunks_eq_verifierCS]
    exact hpch
  · intro lookup
    rw [actionCircuit.toVerifierKey_lookupInputExprs]
    have hlookup := congrFun (List.ofFn_inj.mp hli)
      (Fin.cast
        (congrArg CircuitShape.numLookups actionCircuitShape_eq_fixtureCircuitShape)
        lookup)
    simpa only [actionCircuit.verifierCS_lookupInputExprs,
      actionPinned, Fin.val_cast] using hlookup
  · intro lookup
    rw [actionCircuit.toVerifierKey_lookupTableExprs]
    have hlookup := congrFun (List.ofFn_inj.mp hlt)
      (Fin.cast
        (congrArg CircuitShape.numLookups actionCircuitShape_eq_fixtureCircuitShape)
        lookup)
    simpa only [actionCircuit.verifierCS_lookupTableExprs,
      actionPinned, Fin.val_cast] using hlookup

assert_no_sorry certificate
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.Keygen
