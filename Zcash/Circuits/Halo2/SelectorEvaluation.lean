import Zcash.Circuits.Halo2.GateOperations
import Clean.Halo2.Keygen.GateProjection
import Zcash.Arithmetic

/-! # Semantics of packed selectors in a row assignment -/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)
open Halo2

set_option maxHeartbeats 20000

/-- Every selector-compression entry uses a valid, scalar-field-distinct root. -/
def SelectorRootsWellFormed (map : SelCompressMap) : Prop :=
  ∀ {selector : ℕ} {compressed : SelCompress},
    map.lookup selector = some compressed →
      1 ≤ compressed.assignedRoot ∧
      compressed.assignedRoot ≤ compressed.combinationLen ∧
      compressed.combinationLen < scalarFieldOrder

/--
The packed fixed columns realize the compression map on every selector activation
derived from synthesis and placement.
-/
def SelectorActivationsRealized
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment Fp) : Prop :=
  ∀ {selector row : ℕ} {compressed : SelCompress},
    (selector, row) ∈ activationRows →
    map.lookup selector = some compressed →
      environment.fixed ⟨compressed.packedCol⟩ row =
        (compressed.assignedRoot : Fp)

/--
The selector-compression replacement is nonzero when its packed fixed cell holds
its assigned root.  The only field-specific premise is that the combination length
is below the scalar-field modulus, making its small natural roots injective in `Fp`.
-/
theorem selectorScale_ne_zero_of_root
    (compressed : SelCompress) (valuation : Query → Fp)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (compressed.assignedRoot : Fp))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < scalarFieldOrder) :
    (selReplacement compressed).eval valuation ≠ 0 := by
  apply selReplacement_eval_of_root compressed valuation
    hvalue hpositive hrootBound
  intro left right hleft hright heq
  have hleftOrder : left < scalarFieldOrder := by
    omega
  have hrightOrder : right < scalarFieldOrder := by
    omega
  have hvals := congrArg
    (ZMod.val (n := scalarFieldOrder)) heq
  simpa [ZMod.val_cast_of_lt hleftOrder,
    ZMod.val_cast_of_lt hrightOrder] using hvals

/-- Environment spelling of `selectorScale_ne_zero_of_root`. -/
theorem selectorScale_ne_zero_of_environment
    (compressed : SelCompress) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℕ)
    (hvalue : environment.fixed ⟨compressed.packedCol⟩ row =
      (compressed.assignedRoot : Fp))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < scalarFieldOrder) :
    (selReplacement compressed).eval
      (Query.eval environment selectors row) ≠ 0 := by
  apply selectorScale_ne_zero_of_root compressed
    (Query.eval environment selectors row)
    _ hpositive hrootBound hlengthBound
  simpa [Query.eval] using hvalue

/--
Circuit-derived activation placement and packed fixed data make the selector scale
nonzero at every extracted enabled gate.
-/
theorem selectorScale_ne_zero_of_enabledGate
    (map : SelCompressMap) (starts : List ℕ)
    (operations : Operations Fp) (i : RegionIndex)
    (environment : Environment Fp) (selectors : ℕ → Fp)
    (hroots : SelectorRootsWellFormed map)
    (hfixed : SelectorActivationsRealized map
      (activations starts (indexedRegions operations i).1) environment)
    {enabled : EnabledGate Fp}
    (henabled : enabled ∈ operationEnabledGates operations i)
    {compressed : SelCompress}
    (hcompressed :
      map.lookup enabled.gate.selector.index = some compressed) :
    (selReplacement compressed).eval
      (Query.eval environment selectors
        (starts.getD enabled.region 0 + enabled.row)) ≠ 0 := by
  have hactivation :=
    mem_activations_of_mem_operationEnabledGate starts henabled
  have hvalue := hfixed hactivation hcompressed
  obtain ⟨hpositive, hrootBound, hlengthBound⟩ :=
    hroots hcompressed
  exact selectorScale_ne_zero_of_environment
    compressed environment selectors
    (starts.getD enabled.region 0 + enabled.row)
    hvalue hpositive hrootBound hlengthBound

end Zcash.Snark
