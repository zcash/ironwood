import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Common.UniformMeasure
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Decode

/-!
# MSM evaluation spine for the multiopen decode

The `Msm` evaluation lemmas the decode proofs are stated over (`Msm.eval_{zero,scale,add}`).

Every break charged to DLOG travels as computed `NontrivialRelation` data, per the
breaks-as-computed-data discipline in `Zcash.Security.RandomOracle`; an existential relation alone
would be vacuous in a prime-order group.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

namespace Msm

-- The MSM operations these lemmas are about live in `Zcash.Arithmetic.Msm`; this namespace only
-- adds the evaluation spine lemmas the decode proofs need.
open Zcash.Arithmetic.Msm (eval zero scale add)

/-- The zero MSM evaluates to the group identity. -/
theorem eval_zero {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G) :
    (Msm.zero urs.k F G).eval urs = 0 := by
  simp [eval, zero]

/-- Scaling an MSM scales its evaluation. -/
theorem eval_scale {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.scale c).eval urs = c • m.eval urs := by
  simp only [eval, scale, smul_add, Finset.smul_sum, List.smul_sum, List.map_map,
    Function.comp_def, mul_smul]

/-- Adding two MSMs adds their evaluations. -/
theorem eval_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (m₁ m₂ : Msm urs.k F G) :
    (m₁.add m₂).eval urs = m₁.eval urs + m₂.eval urs := by
  simp only [eval, add, add_smul, Finset.sum_add_distrib, List.map_append, List.sum_append]
  abel

end Msm

section Binding

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]




end Binding

section Decoded

variable {G : Type*} [AddCommGroup G] [Module Fp G]




end Decoded

end Zcash.Snark
