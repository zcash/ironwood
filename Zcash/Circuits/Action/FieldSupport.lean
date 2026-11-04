import Zcash.Circuits.Action.Shape
import Clean.Halo2.Compiler.FieldSupport
import Zcash.Arithmetic.Domain

/-! # The Action circuit fits the Pasta evaluation domain and column names -/

namespace Zcash.Circuits.Action

open Halo2 Zcash.Arithmetic

instance actionCircuitFieldSupport :
    CircuitFieldSupport actionCircuit where
  domainExponent_le := by
    simp only [TopLevelCircuit.domainExponent, actionCircuit_shape_eq, actionShape,
      pastaDomain_twoAdicity_eq]
    norm_num
  constraintDegree_lt_ringChar := by
    rw [actionCircuit_constraintDegree_eq]
    norm_num [ZMod.ringChar_zmod_n, scalarFieldOrder]
  permutationColumnCount_le := by
    simp only [TopLevelCircuit.permutationColumnCount,
      actionCircuit_shape_eq, actionShape, pastaDomain_oddPart_eq]
    norm_num [deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

end Zcash.Circuits.Action
