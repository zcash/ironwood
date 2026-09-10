import Zcash.Circuits.Action.Shape
import Zcash.Circuits.Integration.FieldSupport

/-! # The Action circuit fits the Pasta evaluation domain and column names -/

namespace Zcash.Circuits.Action

open Halo2 Zcash.Arithmetic

instance actionCircuitFieldSupport :
    CircuitFieldSupport actionCircuit actionCircuit.omega deltaFp := by
  apply actionCircuit.fieldSupport_of_pastaBounds
  · simp only [TopLevelCircuit.domainExponent, actionCircuit_shape_eq, actionShape]
    norm_num
  · rw [actionCircuit_constraintDegree_eq]
    norm_num [scalarFieldOrder]
  · simp only [TopLevelCircuit.permutationColumnCount,
      actionCircuit_shape_eq, actionShape]
    norm_num [deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

end Zcash.Circuits.Action
