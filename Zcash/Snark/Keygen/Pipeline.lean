import CompElliptic.Curves.Pasta
import Zcash.Common.ParMap
import Zcash.Arithmetic.Domain
import Zcash.Arithmetic.Fft
import CompElliptic.Curves.Pasta.Fast.Msm
import Zcash.Circuits.Integration.ExprRich
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.Keygen
import Clean.Halo2.TopLevel
import Zcash.Arithmetic
import Zcash.Snark.Keygen.Commitments
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.Circuit

/-!
# `TopLevelCircuit.toVerifierKey` — the circuit-side half of halo2 `keygen_vk`, generic

The single generic pipeline from a closed circuit (+ a monomial URS) to the full
`VerifyingKey`: Clean's `Halo2.Keygen` supplies the pinned constraint system, domain
exponent and selector map; this module adds the group side — the Lagrange-basis URS by
inverse FFT, the dense fixed columns from the derived layout, the keygen permutation
polynomials, `commit_lagrange` for both commitment families — and assembles the record.

`TopLevelCircuit.shape` records every circuit-fixed count. Proof invocation parameters
remain separate and do not enter `TopLevelCircuit.toVerifierKey`; callers combine them
with `Halo2.CircuitShape.withProofParams` only when they need a complete proof `Shape`. The
Action capture certification lives in `Certificate.lean`.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`),
  `arithmetic.rs:192` (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default() = Blind(F::ONE)`).
* Fixed commitments: `plonk/keygen.rs:230-240` (`keygen_vk`'s `fixed_commitments`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).
-/

namespace Halo2.TopLevelCircuit

open Zcash.Snark
-- This section declares under `Halo2`, not `Zcash`, so the root re-exports of `Fp`/`URS` are not
-- on the enclosing-namespace walk and have to be opened explicitly.
open Zcash.Arithmetic (Fp URS derivedUrsGLagrange)
open Zcash.Snark.Keygen
open Halo2
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The derived fixed-column commitments of a closed circuit against a URS. -/
def fixedCommitments
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top] (urs : URS G) : List G :=
  top.fixedRows.parMap
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
      (derivedUrsGLagrange urs))

/-- The named top-level fixed-row view is exactly the fixed-commitment computation
used by generic keygen. -/
@[simp] theorem fixedCommitments_eq_fixedCommitmentsOf
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top] (urs : URS G) :
    top.fixedCommitments urs =
      fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        top.fixedRows := by
  simp only [fixedCommitments, fixedCommitmentsOf, fixedCommitmentsWith]

/-- The derived permutation common commitments of a closed circuit against a URS. -/
def permutationCommitments
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top] (urs : URS G) : List G :=
  permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) top.domainExponent
    top.constraintSystem (top.operations)

/-- The fitting-domain generator used by the circuit's verifier. -/
def omega (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top] : Fp :=
  Zcash.Arithmetic.omegaOf top.domainExponent

/-- The fitting-domain generator is nonzero whenever its exponent lies in
Pasta's supported range. -/
theorem omega_ne_zero
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (hbound : top.domainExponent ≤ 32) :
    top.omega ≠ 0 :=
  (Zcash.Arithmetic.omegaOf_isPrimitiveRoot
    top.domainExponent hbound).isUnit (by positivity) |>.ne_zero

/-- **The verifying key of a closed top-level circuit**: the `TopLevelCircuit` carries
unit configuration and synthesis inputs, so the only remaining input is the URS —
`keygen_vk` at the `TopLevelCircuit` level, indexed by the circuit-owned shape. -/
def toVerifierKey
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    VerifyingKey top.shape Fp G :=
  let verifierCS := top.verifierCS
  let fixedCommitments := top.fixedCommitments urs
  let permutationCommitments := top.permutationCommitments urs
  { omega := top.omega
    n := top.n
    blindingFactors := top.blindingFactors
    delta := Zcash.Arithmetic.deltaFp
    chunkLen := top.chunkLen
    gates := verifierCS.gates
    instanceQueryLayout := top.instanceQueryLayout
    adviceQueryLayout := top.adviceQueryLayout
    fixedQueryLayout := top.fixedQueryLayout
    fixedCommitment := fun column => fixedCommitments.getD column 0
    permutationCommonCommitment := fun column =>
      permutationCommitments.getD column.val 0
    permutationChunks := verifierCS.permutationChunks
    lookupInputExprs := verifierCS.lookupInputExprs
    lookupTableExprs := verifierCS.lookupTableExprs }

/-- The derived key uses the circuit's fitting-domain generator. -/
@[simp] theorem toVerifierKey_omega
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).omega =
      top.omega := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned fitting domain size. -/
@[simp]
theorem toVerifierKey_n
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).n = top.n := by
  simp only [toVerifierKey]

/-- The derived key preserves the closed constraint system's blinding count. -/
@[simp]
theorem toVerifierKey_blindingFactors
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).blindingFactors = top.blindingFactors := by
  simp only [toVerifierKey]

/-- The derived key uses the protocol's fixed permutation delta. -/
@[simp] theorem toVerifierKey_delta
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).delta =
      Zcash.Arithmetic.deltaFp := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned permutation chunk width. -/
@[simp] theorem toVerifierKey_chunkLen
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).chunkLen = top.chunkLen := by
  simp only [toVerifierKey]

/--
The fitting domain of a circuit-derived verification key has room for all of
the circuit's blinding rows.
-/
theorem toVerifierKey_blindingFactors_lt_n
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).blindingFactors <
      (top.toVerifierKey urs).n := by
  rw [top.toVerifierKey_blindingFactors, top.toVerifierKey_n]
  exact top.blindingFactors_lt_domainSize

/-- The derived key exposes the fixed commitments computed from its own dense rows. -/
theorem toVerifierKey_fixedCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) (column : ℕ) :
    (top.toVerifierKey urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [toVerifierKey]

/-- The derived key exposes the common permutation commitments computed from
its own keygen permutation rows. -/
theorem toVerifierKey_permutationCommonCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G)
    (column : Fin top.permutationColumnCount) :
    (top.toVerifierKey urs).permutationCommonCommitment column =
      (top.permutationCommitments urs).getD column.val 0 := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned advice-query layout. -/
@[simp] theorem toVerifierKey_adviceQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).adviceQueryLayout =
      top.adviceQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned fixed-query layout. -/
@[simp] theorem toVerifierKey_fixedQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).fixedQueryLayout =
      top.fixedQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned instance-query layout. -/
@[simp] theorem toVerifierKey_instanceQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).instanceQueryLayout =
      top.instanceQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's ironwood-native gate expressions. -/
@[simp] theorem toVerifierKey_gates
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).gates = top.verifierCS.gates := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's ironwood-native permutation chunks. -/
@[simp] theorem toVerifierKey_permutationChunks
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).permutationChunks =
      top.verifierCS.permutationChunks := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's ironwood-native lookup input expressions. -/
@[simp] theorem toVerifierKey_lookupInputExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G)
    (lookup : Fin top.lookupCount) :
    (top.toVerifierKey urs).lookupInputExprs lookup =
      top.verifierCS.lookupInputExprs lookup := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's ironwood-native lookup table expressions. -/
@[simp] theorem toVerifierKey_lookupTableExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G)
    (lookup : Fin top.lookupCount) :
    (top.toVerifierKey urs).lookupTableExprs lookup =
      top.verifierCS.lookupTableExprs lookup := by
  simp only [toVerifierKey]

/-- The derived key's advice-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_adviceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).adviceQueryLayout.length =
      top.adviceQueryCount := by
  rw [top.toVerifierKey_adviceQueryLayout,
    top.adviceQueryCount_eq_adviceQueryLayout_length]

/-- The derived key's fixed-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_fixedQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).fixedQueryLayout.length =
      top.fixedQueryCount := by
  rw [top.toVerifierKey_fixedQueryLayout,
    top.fixedQueryCount_eq_fixedQueryLayout_length]

/-- The derived key's instance-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_instanceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) :
    (top.toVerifierKey urs).instanceQueryLayout.length =
      top.instanceQueryCount := by
  rw [top.toVerifierKey_instanceQueryLayout,
    top.instanceQueryCount_eq_instanceQueryLayout_length]

end Halo2.TopLevelCircuit
