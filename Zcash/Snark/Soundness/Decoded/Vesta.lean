import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Core.Vesta
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# Vesta support for the straight-line soundness stack

The Vesta pinning itself — `VestaG`, its group order, the `Fp`-module structure — lives
in `Zcash/Snark/Core/Vesta.lean`, where the byte-locked fixture captures can reach it
through the `Zcash.Snark` umbrella without importing the soundness stack (issue #153).
This module supplies what sits on top for the soundness development: the
concrete-to-abstract MSM bridge and the IPA witness identities used by the
straight-line extraction.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.evalNat_eq_eval scalarFieldOrder)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- Natural-scalar MSM evaluation agrees with the module-theoretic evaluation
used by the soundness development. -/
theorem Msm.evalNat_eq_eval_vesta (urs : URS VestaG)
    (m : Msm urs.k Fp VestaG) : m.evalNat urs = m.eval urs :=
  Msm.evalNat_eq_eval urs m

/-- The powers evaluation vector has leading entry `1`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) :
    evalVector k x 0 = 1 := by
  simp [evalVector]

/-- The IPA witness after folding in the value term and synthetic blinder. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) :
    Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) =
      commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp,
      commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'
    simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

/-- The single-entry value term in the adjusted commitment is `-v • g 0`. -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G]
    (gg : Fin (2 ^ k) → G) (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

end Zcash.Snark
