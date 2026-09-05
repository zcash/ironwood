import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Common.DiscreteLogRelation

/-!
# Acceptance at the zero basis, structurally

At the all-zero basis every representable group element is the identity, so the verifier's final
check — the assembled MSM evaluates to `0` — holds for free on any proof whose assembly succeeds.
This module proves that chain with no computation and no compiler trust: representations vanish
(`representationEval_zeroBasis`), an algebraic point over the zero basis is the identity
(`AlgebraicPoint.point_eq_zero_of_zeroBasis`), MSM evaluation over the zero URS reduces to its
base terms (`Msm.eval_zeroURS`), and checked assembly plus vanishing bases give `DeployedAccepts`
(`deployedAccepts_of_assembles_of_zeroBases`).

Two lemmas complete the chain into an unconditional acceptance witness for the adaptive family,
and are the tracked remainder: checked assembly succeeds on the zero family's proof
string at an oracle whose derived challenges pass the vanishing, grouping, and multiopen guards;
and every base of the assembled MSM is drawn from the verifying-key, instance, and proof-string
point families — the base-provenance walk over `Verifier/Assemble.lean`.  Both are structural
statements; neither needs evaluation.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm URS)

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Over the all-zero basis every representation evaluates to the identity. -/
theorem representationEval_zeroBasis {ι : Type*} [Fintype ι] (coeffs : ι → F) :
    Zcash.representationEval (F := F) (fun _ : ι => (0 : G)) coeffs = 0 := by
  simp [Zcash.representationEval]

/-- An algebraic point over the all-zero basis is the identity: its carried representation
evaluates to `0`, and the representation evaluates to the point. -/
theorem _root_.Zcash.AlgebraicPoint.point_eq_zero_of_zeroBasis
    {ι : Type*} [Fintype ι] (P : Zcash.AlgebraicPoint (F := F) (fun _ : ι => (0 : G))) :
    P.point = 0 := by
  rw [← P.hEq]
  exact representationEval_zeroBasis P.coeffs

/-- Splitting an all-zero augmented basis yields the URS with zero generators and auxiliaries. -/
theorem ursOfAugmentedBasis_zeroBasis (k : ℕ) :
    ursOfAugmentedBasis (G := G) k (fun _ => 0) =
      ({ k := k, g := fun _ => 0, u := 0, w := 0 } : URS G) :=
  rfl

/-- Over a URS whose generators and auxiliaries are all `0`, MSM evaluation is the base-term sum:
the `g`, `w`, and `u` contributions vanish regardless of their scalars. -/
theorem _root_.Zcash.Arithmetic.Msm.eval_zeroURS {k : ℕ}
    (m : Msm k F G) :
    m.eval ({ k := k, g := fun _ => 0, u := 0, w := 0 } : URS G) =
      (m.other.map fun t => t.1 • t.2).sum := by
  simp [Msm.eval]

/-- A base-term sum over vanishing bases is the identity. -/
theorem _root_.Zcash.Arithmetic.Msm.otherSum_eq_zero_of_zeroBases {k : ℕ}
    (m : Msm k F G) (h : ∀ t ∈ m.other, t.2 = (0 : G)) :
    (m.other.map fun t => t.1 • t.2).sum = 0 := by
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [h t ht, smul_zero]

section DeployedAcceptance

variable {G' : Type*} [AddCommGroup G'] [Module Fp G'] [DecidableEq G'] [Inhabited G']

/-- **Acceptance at the zero basis, from assembly success and vanishing bases.**  If checked
assembly succeeds and every base of the assembled MSM is the identity — as at the all-zero
basis, where the key, instance, and proof points are all representable and therefore zero —
the deployed acceptance predicate holds.  The two hypotheses are the tracked remainder of the
accepting extractor run: assembly success at a guard-passing oracle, and the base-provenance
walk that discharges `hbases` from the input families. -/
theorem deployedAccepts_of_assembles_of_zeroBases {shape : Shape}
    (vk : VerifyingKey shape Fp G') (instanceCommitment : Fin shape.numProofs → ℕ → G')
    (ps : ProofString shape Fp G') (ch : Challenges shape.k Fp)
    {m : Msm shape.k Fp G'}
    (hassemble : assemble? vk instanceCommitment ps ch = some m)
    (hbases : ∀ t ∈ m.other, t.2 = (0 : G')) :
    DeployedAccepts shape ({ k := shape.k, g := fun _ => 0, u := 0, w := 0 } : URS G') rfl
      vk instanceCommitment ps ch := by
  unfold DeployedAccepts
  split
  · rename_i m' hm'
    rw [hassemble] at hm'
    obtain rfl : m = m' := Option.some.inj hm'
    exact (Msm.eval_zeroURS m).trans (Msm.otherSum_eq_zero_of_zeroBases m hbases)
  · rename_i hm'
    rw [hassemble] at hm'
    simp at hm'

end DeployedAcceptance

end Zcash.Snark
