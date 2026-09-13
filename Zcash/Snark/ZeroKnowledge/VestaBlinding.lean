import Zcash.Common.BlindingGenerator
import Zcash.Snark.Core.Vesta

/-!
# Hiding with a nonidentity Vesta generator

Vesta has the scalar field's cardinality, so the abstract simulation's blinding
bijection follows from nonidentity of W. The curve-cardinality fact inherits the
repository's existing `Vesta.p_nsmul_Gpt` native certificate. The field-module
argument itself is kernel-proved in `BlindingGenerator`; no new native
certificate is introduced here.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common

open Zcash.Arithmetic (Fp card_Fp)
open CompElliptic.Curves.Pasta

variable [Module Fp VestaG]

/-- Every nonidentity Vesta point supplies the bijection required by the simulation. -/
theorem vestaBlinding_bijective (point : VestaG) (hpoint : point ≠ 0) :
    Function.Bijective (fun scalar : Fp => scalar • point) := by
  classical
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  apply scalarBlinding_bijective (point := point) _ hpoint
  rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq]

/-- On Vesta the full blinding-generator condition is equivalent to nonidentity. -/
theorem vestaBlinding_bijective_iff (point : VestaG) :
    Function.Bijective (fun scalar : Fp => scalar • point) ↔ point ≠ 0 := by
  classical
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  apply scalarBlinding_bijective_iff
  rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq]

end Zcash.Snark.ZeroKnowledge
