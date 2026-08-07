import Zcash.Arithmetic.Msm
import CompElliptic.Curves.Pasta.Fast.Msm

/-!
# Fast compiled evaluation for the fingerprint MSM

`Msm.evalNat` — the executable natural-scalar MSM the captured-fixture fingerprint
checks evaluate (`capturedMsm_eval_eq_zero`) — is spelled as the specification: a
`Finset` sum of per-generator `nsmul`s. Evaluated naively that is ~2050 binary
double-and-add scalar multiplications (each paying one field inversion per affine
point addition), which dominated the fixture modules' build times.

`Msm.evalNatFast` computes the same value through the PROVEN windowed Pippenger
accelerator (`CompElliptic.Curves.Pasta.Fast.Msm.pippengerFast`, generic over any
`AddCommMonoid`), and `Msm.evalNat_eq_evalNatFast` is a kernel-checked equality
registered with `@[csimp]`:
the compiler substitutes the fast implementation at every subsequently compiled call
site — in particular inside the fixtures' `native_decide` auxiliaries — while the
statement surface and the kernel-level meaning of `evalNat` are untouched. This is
the proven-equality counterpart of `implemented_by`, which is forbidden here because it
is unchecked — a ban the trusted-base census enforces rather than leaves to convention:
`Zcash.Meta.assert_axioms` and `Zcash.Meta.assert_computable` fail the build on any
`@[implemented_by]` or `@[extern]` outside the toolchain's own ambient surface.
-/

namespace Zcash.Arithmetic.Msm

open CompElliptic.Curves.Pasta.Fast.Msm (defaultWindow pippengerFastPar
  pippengerFastPar_eq pippengerFast_eq pippenger_eq_msm)

/-- `evalNat` through the proven windowed Pippenger accelerator, with the ~32 independent
windows evaluated in parallel (`CompElliptic.Curves.Pasta.Fast.Msm.pippengerFastPar`):
one bucketed MSM over the generator terms, the blinding/inner-product generators, and
the extra term list.

The replacement must stay generic over `[AddCommGroup G]` (a `@[csimp]` lemma replaces the
whole constant), so the *affine* windows-parallel accelerator is the fastest admissible form
here; the Vesta-specific projective interior
(`CompElliptic.Curves.Pasta.Fast.MsmProj.pippengerProjScatterPar`) cannot be dispatched
from a generic `G`. -/
def evalNatFast {p : ℕ} {G : Type*} [AddCommGroup G]
    (urs : URS G) (m : Msm urs.k (ZMod p) G) : G :=
  pippengerFastPar defaultWindow
    ((List.ofFn fun i => ((m.gScalars i).val, urs.g i))
      ++ (m.wScalar.val, urs.w) :: (m.uScalar.val, urs.u)
        :: m.other.map fun t => (t.1.val, t.2))

/-- **The fast MSM evaluation is `evalNat`** — registered with `@[csimp]` so compiled
code (including the fixtures' `native_decide` auxiliaries) runs the windows-parallel
Pippenger form. -/
@[csimp] theorem evalNat_eq_evalNatFast : @evalNat = @evalNatFast := by
  funext p G inst urs m
  unfold evalNat evalNatFast
  rw [pippengerFastPar_eq, pippengerFast_eq, pippenger_eq_msm _ (by decide)]
  simp only [List.map_append, List.map_cons, List.map_ofFn, List.map_map,
    List.sum_append, List.sum_cons, List.sum_ofFn, Function.comp_def]
  abel

end Zcash.Arithmetic.Msm
