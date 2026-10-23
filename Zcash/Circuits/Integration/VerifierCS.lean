import Zcash.Circuits.Integration.ExprRich
import Zcash.Snark.Verifier.ConstraintSystem
import Clean.Halo2.Keygen
import Clean.Halo2.TopLevel

/-!
# Circuit-owned verifier data

`Halo2.TopLevelCircuit.verifierCS` is the single ironwood-native projection of a
closed Clean circuit. It translates the circuit's pinned expressions and permutation
columns into the types consumed by the verifier, without introducing proof parameters,
commitments, or a second source of circuit configuration.
-/

namespace Halo2.TopLevelCircuit

open Zcash.Snark

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The circuit-owned verifier constraint system: Clean's pinned circuit data
translated once into ironwood's expression and column-reference types.
-/
def verifierCS
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top] :
    VerifierCS top.lookupCount F :=
  let pinned := top.pinnedCS
  let permutationReference : AnyColumn → ColumnRef := fun column =>
    match column.kind with
    | .advice =>
        .advice (pinned.adviceQueryLayout.findIdx
          (· = (column.index, 0)))
    | .fixed =>
        .fixed (pinned.fixedQueryLayout.findIdx
          (· = (column.index, 0)))
    | .instance =>
        .instance (pinned.instanceQueryLayout.findIdx
          (· = (column.index, 0)))
  { gates := pinned.gates.map RichExpression.toExpr
    permutationChunks :=
      ((top.permutationColumns.map
        permutationReference).zipIdx).toChunks top.chunkLen
    lookupInputExprs := fun lookup =>
      (pinned.lookupInputExprs.getD lookup.val []).map
        RichExpression.toExpr
    lookupTableExprs := fun lookup =>
      (pinned.lookupTableExprs.getD lookup.val []).map
        RichExpression.toExpr }

/-- The verifier CS translates the circuit-owned pinned gates. -/
@[simp] theorem verifierCS_gates
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top] :
  top.verifierCS.gates =
      top.pinnedCS.gates.map RichExpression.toExpr := by
  simp only [verifierCS]

/-- The verifier CS translates one circuit-owned lookup input. -/
@[simp] theorem verifierCS_lookupInputExprs
    (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top]
    (lookup : Fin top.lookupCount) :
    top.verifierCS.lookupInputExprs lookup =
      (top.pinnedCS.lookupInputExprs.getD lookup.val []).map
        RichExpression.toExpr := by
  simp only [verifierCS]

/-- The verifier CS translates one circuit-owned lookup table. -/
@[simp] theorem verifierCS_lookupTableExprs
    (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top]
    (lookup : Fin top.lookupCount) :
    top.verifierCS.lookupTableExprs lookup =
      (top.pinnedCS.lookupTableExprs.getD lookup.val []).map
        RichExpression.toExpr := by
  simp only [verifierCS]

end Halo2.TopLevelCircuit
