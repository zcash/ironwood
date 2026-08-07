import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Circuit and proof shapes

`CircuitShape` contains the counts fixed by a circuit and therefore shared by its
verifying key and every proof made against that key. `ProofParams` contains the two
counts chosen for one proof invocation. `Shape` combines the two for data structures
whose complete finite layout depends on both.
-/

namespace Zcash.Snark

/-- Counts fixed by a circuit and its verifying key. -/
structure CircuitShape where
  k : ℕ
  numAdviceColumns : ℕ
  numLookups : ℕ
  numPermutationSets : ℕ
  numPermutationColumns : ℕ
  numQuotientPieces : ℕ
  numInstanceColumns : ℕ
  numInstanceQueries : ℕ
  numAdviceQueries : ℕ
  numFixedQueries : ℕ
deriving DecidableEq, Repr

/-- Counts chosen for one proof invocation rather than fixed by the circuit. -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

/-- The complete finite layout of a proof: its circuit shape plus invocation parameters. -/
structure Shape extends CircuitShape where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

instance : Coe Shape CircuitShape :=
  ⟨Shape.toCircuitShape⟩

/-- Extend circuit-fixed counts with the parameters of one proof invocation. -/
def CircuitShape.withProofParams (shape : CircuitShape) (pp : ProofParams) : Shape :=
  { toCircuitShape := shape
    numProofs := pp.numProofs
    numPointSets := pp.numPointSets }

/-- Extending with proof parameters preserves the circuit shape. -/
@[simp] theorem CircuitShape.withProofParams_toCircuitShape
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).toCircuitShape = shape := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit domain exponent. -/
@[simp] theorem CircuitShape.withProofParams_k
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).k = shape.k := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit advice-column count. -/
@[simp] theorem CircuitShape.withProofParams_numAdviceColumns
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numAdviceColumns = shape.numAdviceColumns := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit lookup count. -/
@[simp] theorem CircuitShape.withProofParams_numLookups
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numLookups = shape.numLookups := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit permutation-set count. -/
@[simp] theorem CircuitShape.withProofParams_numPermutationSets
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numPermutationSets = shape.numPermutationSets := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit permutation-column count. -/
@[simp] theorem CircuitShape.withProofParams_numPermutationColumns
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numPermutationColumns = shape.numPermutationColumns := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit quotient-piece count. -/
@[simp] theorem CircuitShape.withProofParams_numQuotientPieces
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numQuotientPieces = shape.numQuotientPieces := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit instance-column count. -/
@[simp] theorem CircuitShape.withProofParams_numInstanceColumns
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numInstanceColumns = shape.numInstanceColumns := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit instance-query count. -/
@[simp] theorem CircuitShape.withProofParams_numInstanceQueries
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numInstanceQueries = shape.numInstanceQueries := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit advice-query count. -/
@[simp] theorem CircuitShape.withProofParams_numAdviceQueries
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numAdviceQueries = shape.numAdviceQueries := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape uses the circuit fixed-query count. -/
@[simp] theorem CircuitShape.withProofParams_numFixedQueries
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numFixedQueries = shape.numFixedQueries := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape preserves the requested proof count. -/
@[simp] theorem CircuitShape.withProofParams_numProofs
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numProofs = pp.numProofs := by
  simp only [CircuitShape.withProofParams]

/-- The extended shape preserves the requested point-set count. -/
@[simp] theorem CircuitShape.withProofParams_numPointSets
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numPointSets = pp.numPointSets := by
  simp only [CircuitShape.withProofParams]

end Zcash.Snark
