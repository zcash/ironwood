import Zcash.Circuits.Halo2.SelectorCompression
import Zcash.Circuits.Integration.PolynomialEnvironment

/-! # Packed selector values from fixed-column polynomials -/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)
open Halo2 Halo2.Layout

/--
Dense fixed-column rows compiled into their canonical interpolation polynomials
realize selector activations whenever the sparse selector assignments occur at
in-domain rows with the expected dense values.

This is the polynomial boundary expected from key generation: the selector compiler
does not need to know how commitments or a concrete verifying key are assembled.
-/
theorem selectorActivationsRealized_of_fixedRowPolynomials
    {n : ℕ} (omega : Fp)
    (fixedRows : ℕ → List Fp)
    (adviceCols instanceCols : ℕ → CPoly)
    (usableRows : ℕ)
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (hrows :
      Function.Injective fun row : Fin n => omega ^ (row : ℕ))
    (hroots : SelectorRootsWellFormed map)
    (hlength : ∀ column, (fixedRows column).length = n)
    (hfixed :
      ∀ {assignment : Layout.FixedAssignment Fp},
        assignment ∈ Layout.selectorAssignments map activationRows →
          (fixedRows assignment.1).getD assignment.2.1 0 =
            assignment.2.2) :
    SelectorActivationsRealized map activationRows
      (polynomialEnvironment omega usableRows
        (fun column =>
          rowPolynomial omega
            (zeroPaddedRows (n := n) (fixedRows column)))
        adviceCols instanceCols) := by
  intro selector row compressed hactivation hlookup
  have hentry :=
    Layout.mem_selectorAssignments_of_activation (F := Fp) map activationRows
      hactivation hlookup
  have hvalue := hfixed hentry
  obtain ⟨hpositive, hrootBound, hcombinationBound⟩ :=
    hroots hlookup
  have hrootLt :
      compressed.assignedRoot < scalarFieldOrder :=
    hrootBound.trans_lt hcombinationBound
  have hrootNe :
      (compressed.assignedRoot : Fp) ≠ 0 := by
    intro hzero
    have hval := congrArg ZMod.val hzero
    have : compressed.assignedRoot = 0 := by
      simpa [ZMod.val_cast_of_lt hrootLt] using hval
    omega
  have hrow : row < n := by
    by_contra hout
    have hge : (fixedRows compressed.packedCol).length ≤ row := by
      rw [hlength]
      omega
    have hzero :
        (fixedRows compressed.packedCol).getD row 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    rw [hzero] at hvalue
    exact hrootNe hvalue.symm
  rw [polynomialEnvironment_fixed_nat,
    rowPolynomial_eval hrows ⟨row, hrow⟩]
  exact hvalue

end Zcash.Snark
