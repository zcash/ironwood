import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.OrderOfElement
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import Zcash.Arithmetic

/-!
# The deployed verifier group

This module pins the verifier group to the actual Vesta curve: the type `VestaG`, its
group order (every point is `p`-torsion for `p = scalarFieldOrder`, derived from
CompElliptic's pinned point count), and the resulting `Fp`-module structure.

Housed in `Core/`, not `Soundness/Decoded/`, deliberately: the byte-locked fixture
captures state their points in `VestaG` and evaluate the verifier over its `Fp`-module
instance, and the only import halo2's `dump_vesta_lean_fixture` emits is
`Zcash.Snark` — so this vocabulary must be reachable from the umbrella without
dragging the soundness stack into every capture's build path (issue #153). The
soundness-facing Vesta bridges (concrete-to-abstract MSM evaluation, the IPA witness
identities) remain in `Soundness/Decoded/Vesta.lean`, which imports this module.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- Every Vesta point is `p`-torsion for `p = scalarFieldOrder`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Derive the Vesta group order from CompElliptic's pinned point count. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- Install the proved Vesta order for the `Fp`-module instance. -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Give Vesta its scalar-field module structure. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

end Zcash.Snark
