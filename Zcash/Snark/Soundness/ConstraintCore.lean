import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Verifier.QueryCommitment

/-!
# Deterministic constraint identities

Verifier routing, the vanishing-quotient fold, and the final good-`x` implication are independent
of any accepting-multiopen rewind.  This module isolates those facts for the algebraic decoder.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

omit [AddCommGroup G] [Module Fp G] in
/-- The verifier-generated vanishing query carries the computed quotient evaluation. -/
theorem vanishing_query_mem_assembleQueries [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.vanishingH ∧ q.point = ch.x ∧
      q.eval = expectedHEval
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
        ch.y (ch.x ^ vk.n) := by
  refine ⟨{ point := ch.x
            commitment := .msm
              (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))
            eval := expectedHEval
              (allExpressions vk ps ch
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
              ch.y (ch.x ^ vk.n)
            commId := .vanishingH }, ?_, rfl, rfl, rfl⟩
  simp only [assembleQueries, vanishingQueries]
  exact List.mem_append.mpr (Or.inr List.mem_cons_self)

omit [AddCommGroup G] [Module Fp G] in
/-- Grouping routes the unique vanishing query to a singleton-point member. -/
theorem vanishing_slot_routed [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ i, i < (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).sets.length ∧
      (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x] ∧
      ∃ m, m < (deployedSetQueries vk instanceCommitment ps ch i).length ∧
        (∀ c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD m c0 =
          CommitmentId.vanishingH) ∧
        ∀ d0, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d0).2 =
          [expectedHEval
            (allExpressions vk ps ch
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
            ch.y (ch.x ^ vk.n)] := by
  obtain ⟨q, hq, hid, hpt, hev⟩ :=
    vanishing_query_mem_assembleQueries vk instanceCommitment ps ch
  have huniq : ∀ q' ∈ assembleQueries vk instanceCommitment ps ch,
      q'.commId = q.commId → q' = q := by
    intro q' hq' hq'id
    exact assembleQueries_vanishingH_unique vk instanceCommitment ps ch hq' hq
      (hq'id.trans hid) hid
  obtain ⟨i, hi, hpts, m, hm, hids, hsets⟩ :=
    constructIntermediateSets_unique_comm_routed
      (assembleQueries vk instanceCommitment ps ch) hq huniq
  refine ⟨i, hi, by rw [hpts, hpt], m, ?_, ?_, ?_⟩
  · simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using hm
  · intro c0
    simp only [deployedSetCommIds]
    rw [hids c0]
    exact hid
  · intro d0
    simp only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
    rw [hsets d0, hev]

/-- Deployed acceptance excludes the assembler's root-of-unity rejection branch. -/
theorem deployedAccepts_xn_ne_one [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) : ch.x ^ vk.n ≠ 1 := by
  intro hx
  have hnone : assemble? vk instanceCommitment ps ch = none := by
    unfold assemble?
    by_cases hwf : proofStringWellFormed ps = true
    · rw [if_pos hwf, if_pos hx]
    · rw [if_neg hwf]
  unfold DeployedAccepts at hacc
  rw [hnone] at hacc
  exact hacc

/-- Clear the verifier's computed quotient denominator. -/
theorem hfold_of_expectedHEval_binding (constraints : List Fp) (y x : Fp)
    (hpoly : CPoly) (deg : Nat) (exprs : List Fp)
    (hxn : x ^ deg ≠ 1)
    (hbind : hpoly.eval x = expectedHEval exprs y (x ^ deg))
    (hfp : constraints.foldl (fun acc v => acc * y + v) 0 =
      exprs.foldl (fun acc v => acc * y + v) 0) :
    constraints.foldl (fun acc v => acc * y + v) 0 =
      hpoly.eval x * (x ^ deg - 1) := by
  rw [hfp, hbind, expectedHEval, _root_.mul_assoc,
    inv_mul_cancel₀ (sub_ne_zero.mpr hxn), _root_.mul_one]

omit [Module Fp G] in
/-- Read the quotient fold from the routed vanishing member. -/
theorem hfold_of_vanishing_slot_binding [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (constraints : List Fp) (hpoly : CPoly) (i m : Nat)
    (hrouted : ∀ d0, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d0).2 =
      [expectedHEval
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
        ch.y (ch.x ^ vk.n)])
    (hbind : hpoly.eval ch.x =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD m
        (CommitmentRef.point 0, [])).2.getD 0 0)
    (hxn : ch.x ^ vk.n ≠ 1)
    (hfp : constraints.foldl (fun acc v => acc * ch.y + v) 0 =
      (allExpressions vk ps ch
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
          (fun acc v => acc * ch.y + v) 0) :
    constraints.foldl (fun acc v => acc * ch.y + v) 0 =
      hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
  refine hfold_of_expectedHEval_binding constraints ch.y ch.x hpoly vk.n _ hxn ?_ hfp
  rw [hbind, hrouted (CommitmentRef.point 0, [])]
  rfl

/-- Outside the quotient-difference root set, the constraint implication holds. -/
theorem hgood_of_good_challenge (numerator hq : CPoly) (n : Nat) {x : Fp}
    (hx : x ∉ szBadSet (numerator - hq * (X ^ n - 1))) :
    numerator ≠ hq * (X ^ n - 1) →
      (numerator - hq * (X ^ n - 1)).eval x ≠ 0 :=
  fun hne => (not_mem_szBadSet.mp hx) (sub_ne_zero.mpr hne)

end Zcash.Snark
