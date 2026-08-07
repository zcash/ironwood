import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Multiopen.ValueCheck
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Opened

/-!
# The deployed grouping data for the value check

`Soundness.Multiopen.ValueCheck` proved the un-batching core over abstract fixed data. This module
supplies the *deployed* grouping it is instantiated at: the point sets `deployedSetPts` and their
union `deployedAllPts` come from `constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)`, and each
set's points sit inside the union (`deployedSetPts_subset`). `deployedAllPts`'s
cardinality is also the `x₃` floor threshold of the derived capstone and the floor budget. The
query-point membership bridge `deployed_query_point_mem` below is the grouping-side fact that
chain consumes.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The points of deployed point set `j`, as a finite set. -/
def deployedSetPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (j : ℕ) : Finset Fp :=
  ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD j []).toFinset

/-- The union of all the deployed point sets — the roots of the vanishing polynomial `D`. -/
def deployedAllPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Finset Fp :=
  (Finset.range (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length).biUnion
    (fun j => deployedSetPts vk instanceCommitment ps ch j)

omit [AddCommGroup G] [Module Fp G] in
/-- Each deployed point set sits inside the union of all points. -/
theorem deployedSetPts_subset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (j : ℕ) : deployedSetPts vk instanceCommitment ps ch j ⊆ deployedAllPts vk instanceCommitment ps ch := by
  rcases lt_or_ge j (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length
    with hj | hj
  · exact Finset.subset_biUnion_of_mem _ (Finset.mem_range.mpr hj)
  · rw [deployedSetPts, List.getD_eq_default _ _ hj]
    simp


omit [AddCommGroup G] [Module Fp G] in
/-- **F4 (deployed): a routed query's point is one of its set's points.** The deployed specialization
of `constructIntermediateSets_point_mem`: if `q` is one of the verifier's opening queries and its
commitment slot names member `m` of deployed point set `si` (`deployedSetCommIds`), then `q`'s
opening point lies in `deployedSetPts vk instanceCommitment ps ch si`. This is the bridge the layout hypotheses
(`hadviceLayout`/`hinstanceLayout`) feed the value check: it turns the member's slot identity into
the rotated query point being a genuine node of the set, so the per-set node binding applies there. -/
theorem deployed_query_point_mem [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {q : VerifierQuery shape.k Fp G} (hq : q ∈ assembleQueries vk instanceCommitment ps ch)
    {si m : ℕ} {d₀ : CommitmentId}
    (hlt : m < (deployedSetCommIds vk instanceCommitment ps ch si).length)
    (hid : (deployedSetCommIds vk instanceCommitment ps ch si).getD m d₀ = q.commId) :
    q.point ∈ deployedSetPts vk instanceCommitment ps ch si := by
  simp only [deployedSetCommIds] at hlt hid
  rw [deployedSetPts, List.mem_toFinset]
  exact constructIntermediateSets_point_mem (assembleQueries vk instanceCommitment ps ch) hq hlt hid

end Zcash.Snark
