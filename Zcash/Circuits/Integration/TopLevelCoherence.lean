import Clean.Halo2.TopLevel
import Zcash.Circuits.Halo2.GateOperations
import Zcash.Circuits.Integration.OperationLookups

/-!
# Top-level configure/synthesis coherence

`FormalCircuit` deliberately keeps configuration and synthesis independent. A
deployed top-level circuit therefore certifies once that every gate and lookup
activation emitted by synthesis was registered by configuration.

This module proves that the compact operation-level certificate supplies exactly
the membership facts needed by the generic gate and lookup bridges. No circuit,
placement, or verifying key is selected here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace OperationsKeygenCoherent

/-- A coherent region registers every extracted enabled lookup. -/
theorem region_lookup
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ regionEnabledLookups self body) :
    enabled.argument ∈ cs.lookups := by
  induction body with
  | nil => simp [regionEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableLookup argument selectors row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledLookups, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableGate gate row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled lookup. -/
theorem lookup
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ operationEnabledLookups operations i) :
    enabled.argument ∈ cs.lookups := by
  induction operations generalizing i with
  | nil => simp [operationEnabledLookups] at henabled
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          rcases (OperationsKeygenCoherent.region_cons
            cs name body rest).mp hcoherent with
            ⟨hoperation, hrest⟩
          simp only [operationEnabledLookups, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact region_lookup hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          have hrest := (OperationsKeygenCoherent.constrainInstance_cons
            cs cell column row rest).mp hcoherent
          exact ih hrest.2.2 henabled
      | loadTable table values =>
          have hrest := (OperationsKeygenCoherent.loadTable_cons
            cs table values rest).mp hcoherent
          exact ih hrest.2 henabled

end OperationsKeygenCoherent

end Zcash.Snark
