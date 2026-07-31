import Zcash.Snark.Soundness.ConstraintCore
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Verifier.QueryCommitment

/-!
# Deterministic constraint routing

These are the verifier-grouping and public polynomial identities used by the rewind-free deployed
constraint decoder.  They contain no accepting-multiopen sampling or floor premise.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

open Classical CompPoly.CPolynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Acceptance supplies the duplicate-query and grouped-`u` guards. -/
theorem deployedAccepts_pipeline [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) :
    hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false ∧
    (List.ofFn ps.multiopenU).length =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
  unfold DeployedAccepts at hacc
  rcases hasm : assemble? vk instanceCommitment ps ch with _ | m
  · rw [hasm] at hacc
    exact hacc.elim
  rw [hasm] at hacc
  unfold assemble? at hasm
  by_cases hwf : proofStringWellFormed ps = true
  swap
  · rw [if_neg hwf] at hasm
    exact absurd hasm (by simp)
  rw [if_pos hwf] at hasm
  by_cases hxn : ch.x ^ vk.n = (1 : Fp)
  · rw [if_pos hxn] at hasm
    exact absurd hasm (by simp)
  rw [if_neg hxn] at hasm
  rcases hcis : constructIntermediateSets?
      (assembleQueries vk instanceCommitment ps ch) with _ | grouped
  · rw [hcis] at hasm
    exact absurd hasm (by simp)
  simp only [hcis] at hasm
  have hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false := by
    by_contra hd
    rw [Bool.not_eq_false] at hd
    rw [constructIntermediateSets?, if_pos hd] at hcis
    exact absurd hcis (by simp)
  have hgrouped : grouped =
      constructIntermediateSets (assembleQueries vk instanceCommitment ps ch) := by
    rw [constructIntermediateSets?, if_neg (by rw [hdup]; exact Bool.false_ne_true)] at hcis
    exact (Option.some.inj hcis).symm
  by_cases hx3 : multiopenPointsAvoidX3 ch.x3 grouped = true
  swap
  · rw [if_neg hx3] at hasm
    exact absurd hasm (by simp)
  rw [if_pos hx3] at hasm
  unfold assembleFinalMsm? at hasm
  rcases hop : assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
      (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k Fp G) with _ | opened
  · simp [hop] at hasm
  unfold assembleOpening? at hop
  by_cases hguard : (List.ofFn ps.multiopenU).length = grouped.sets.length ∧
      grouped.points.length = grouped.sets.length
  · exact ⟨hdup, hgrouped ▸ hguard.1⟩
  · rw [if_neg hguard] at hop
    exact absurd hop (by simp)

omit [AddCommGroup G] [Module Fp G] in
/-- A routed member retains the canonical commitment named by its slot identity. -/
theorem deployed_member_commitment_eq_assembled [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : Nat)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
    {c : CommitmentId} (c0 : CommitmentId)
    (hid : (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c)
    (d0 : CommitmentRef shape.k Fp G × List Fp) :
    ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) d0).1 =
      assembledCommitment vk instanceCommitment ps ch c := by
  have hm : (m : Nat) <
      ((constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).sets.getD i []).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using m.isLt
  have h := constructIntermediateSets_member_commitment_eq_of_id
    (assembleQueries vk instanceCommitment ps ch)
    (assembledCommitment vk instanceCommitment ps ch)
    (fun q hq => assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq)
    i (m : Nat) hm c0 (by simpa only [deployedSetCommIds] using hid) d0
  simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using h

/-- Evaluation of permutation chunks follows from their component feed bindings. -/
theorem permChunks_bind_of_feeds {shape : Shape} {G' : Type*}
    (vk : VerifyingKey shape Fp G') (ps : ProofString shape Fp G')
    (ch : Challenges shape.k Fp) (q : Fin shape.numProofs)
    (setCarriers : List (PermSetEval (CPoly)))
    (hsets : setCarriers.map (PermSetEval.map (fun r => r.eval ch.x)) =
      subProofPermSets ps q)
    (fixedF adviceF instanceF commonF : Nat → CPoly)
    (hfixedF : ∀ n, (fixedF n).eval ch.x = finFn ps.fixedEvals n)
    (hadviceF : ∀ n, (adviceF n).eval ch.x = finFn (ps.adviceEvals q) n)
    (hinstanceF : ∀ n, (instanceF n).eval ch.x = finFn (ps.instanceEvals q) n)
    (hcommonF : ∀ n, (commonF n).eval ch.x = finFn ps.permutationCommonEvals n) :
    ((setCarriers.zip vk.permutationChunks).map (fun sc =>
      (sc.1, sc.2.map (fun cr =>
        ((match cr.1 with
          | .advice i => adviceF i
          | .fixed i => fixedF i
          | .instance i => instanceF i), commonF cr.2))))).map
      (fun c => (c.1.map (fun r => r.eval ch.x),
        c.2.map (fun r => (r.1.eval ch.x, r.2.eval ch.x)))) =
      subProofPermChunks vk ps q := by
  rw [subProofPermChunks, ← hsets, List.zip_map_left, List.map_map, List.map_map]
  refine List.map_congr_left fun sc _ => ?_
  simp only [Function.comp_apply]
  refine congrArg (Prod.mk _) ?_
  rw [List.map_map]
  refine List.map_congr_left fun cr _ => ?_
  simp only [Function.comp_apply]
  refine congrArg₂ Prod.mk ?_ (hcommonF cr.2)
  rcases cr.1 with i | i | i
  · exact hadviceF i
  · exact hfixedF i
  · exact hinstanceF i

/-- The public Lagrange-basis polynomial. -/
def lagrangeBasisPoly (omega : Fp) (n : Nat) (i : Int) : CPoly :=
  C (omega ^ i / (n : Fp)) * ∑ k ∈ Finset.range n, C ((omega ^ i) ^ (n - 1 - k)) * X ^ k

/-- Closed-form evaluation of the basis polynomial away from the domain. -/
theorem lagrangeBasisPoly_eval (omega : Fp) (n : Nat) (i : Int) (x : Fp)
    (homega : omega ^ n = 1) (hn : (n : Fp) ≠ 0) (hx : x ^ n ≠ 1) :
    (lagrangeBasisPoly omega n i).eval x = lagrangeBasisValue omega n (x ^ n) x i := by
  have homega0 : omega ≠ 0 := by
    intro h0
    rw [h0] at homega
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hn (by norm_num)
    · rw [zero_pow hpos.ne'] at homega
      exact one_ne_zero homega.symm
  have han : (omega ^ i) ^ n = 1 := by
    rw [← zpow_natCast (omega ^ i) n, ← zpow_mul, _root_.mul_comm i (n : Int), zpow_mul,
      zpow_natCast, homega, one_zpow]
  have hxa : x ≠ omega ^ i := by
    intro hxe
    rw [hxe] at hx
    exact hx han
  have hgeom :
      (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k) *
        (x - omega ^ i) = x ^ n - 1 := by
    have h := geom_sum₂_mul x (omega ^ i) n
    calc
      (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k) *
          (x - omega ^ i) =
          (∑ k ∈ Finset.range n, x ^ k * (omega ^ i) ^ (n - 1 - k)) *
            (x - omega ^ i) := by
              congr 1
              exact Finset.sum_congr rfl fun k _ => _root_.mul_comm _ _
      _ = x ^ n - (omega ^ i) ^ n := h
      _ = x ^ n - 1 := by rw [han]
  have heval : (lagrangeBasisPoly omega n i).eval x =
      (omega ^ i / (n : Fp)) *
        ∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k := by
    rw [lagrangeBasisPoly]
    simp [eval_finsetSum]
  have hsub : x - omega ^ i ≠ 0 := sub_ne_zero.mpr hxa
  have hsum : (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k) =
      (x ^ n - 1) / (x - omega ^ i) := by
    rw [eq_div_iff hsub]
    exact hgeom
  rw [heval, lagrangeBasisValue, hsum]
  field_simp

/-- Evaluation commutes with the verifier's additive fold. -/
theorem eval_foldl_add (x : Fp) (acc : CPoly) (ps : List (CPoly)) :
    (ps.foldl (· + ·) acc).eval x =
      (ps.map (fun p => p.eval x)).foldl (· + ·) (acc.eval x) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih => simpa using ih (acc + p)

/-- The three verifier Lagrange values have explicit polynomial carriers. -/
theorem lagrange_bind_derived (omega : Fp) (n blinding : Nat) (x : Fp)
    (homega : omega ^ n = 1) (hn : (n : Fp) ≠ 0) (hx : x ^ n ≠ 1) :
    (lagrangeBasisPoly omega n 0).eval x =
        (lagrangeBasis omega n blinding (x ^ n) x).1 ∧
      (lagrangeBasisPoly omega n (-((blinding : Int) + 1))).eval x =
        (lagrangeBasis omega n blinding (x ^ n) x).2.1 ∧
      (((List.range blinding).map
        (fun j => lagrangeBasisPoly omega n (-((j : Int) + 1)))).foldl
          (· + ·) 0).eval x =
        (lagrangeBasis omega n blinding (x ^ n) x).2.2 := by
  refine ⟨lagrangeBasisPoly_eval omega n 0 x homega hn hx,
    lagrangeBasisPoly_eval omega n _ x homega hn hx, ?_⟩
  show _ = ((List.range blinding).map
      (fun j => lagrangeBasisValue omega n (x ^ n) x (-((j : Int) + 1)))).foldl
        (· + ·) 0
  rw [eval_foldl_add, eval_zero, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  exact lagrangeBasisPoly_eval omega n _ x homega hn hx

end Zcash.Snark
