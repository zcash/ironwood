import Zcash.Snark.Soundness.AGM.ZeroFamily

/-!
# The zero family's deployed root layer

`zeroDeployedRootFamily` inhabits the deployed root interface at every shape, over the constant
zero prover.

The batch witness holds all-zero deployed batches against the run's canonical aggregate
coordinates, which are themselves zero, and the outcome provider always returns it.  So
`deployedRootBad`'s outcome match reduces definitionally, leaving six root sets that are explicit
functions of the pre-IPA reads.  `PinnedRootWitness` builds the same layer at the degenerate
shape, where five of the six sets are empty.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

local instance vestaInhabitedZeroFamilyRoots : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

section RunShape

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- The zero family's adversary is constant. -/
theorem zeroFamily_run
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    (((zeroOnlineMemberFamily vkS hfixed hperm).adversary basis).run O) =
      zeroWfProof basis vkS hfixed hperm := rfl

/-- The wrapped run of the zero family returns the zero proof. -/
theorem zeroFamily_wrapped_run
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O).1 =
      zeroWfProof basis vkS hfixed hperm := by
  rw [wrappedAdversary_run_fst]
  rfl

/-- The wrapped run's erased proof string is the zero proof string. -/
theorem zeroFamily_run_erase
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1 = zeroProofString shape Fp VestaG := by
  rw [zeroFamily_wrapped_run]
  rfl

/-- The wrapped run's aggregate witness coordinates vanish. -/
theorem zeroFamily_run_aMulti
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.aMulti
      (wrappedPreIpaReads
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) = fun _ => 0 := by
  rw [zeroFamily_wrapped_run]
  exact zeroWfProof_aMulti basis vkS hfixed hperm _

/-- The wrapped run's aggregate `U` coordinate vanishes. -/
theorem zeroFamily_run_multiU
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.multiU
      (wrappedPreIpaReads
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) = 0 := by
  rw [zeroFamily_wrapped_run]
  exact zeroWfProof_multiU basis vkS hfixed hperm _

/-- The wrapped run's aggregate blinding coordinate vanishes. -/
theorem zeroFamily_run_multiBlind
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.multiBlind
      (wrappedPreIpaReads
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) = 0 := by
  rw [zeroFamily_wrapped_run]
  exact zeroWfProof_multiBlind basis vkS hfixed hperm _

/-- The wrapped run's `x₄` column commitments are all zero. -/
theorem zeroFamily_run_x4BatchCommitments
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp)
    (j : Fin (deployedX4PairCount vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1
      (wrappedPreIpaRecord
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) + 1)) :
    x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1
      (wrappedPreIpaRecord
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) j = 0 := by
  have hps := zeroFamily_run_erase basis vkS hfixed hperm O
  revert j
  rw [hps]
  intro j
  exact x4BatchCommitments_zeroData basis vkS hfixed hperm _ j

/-- The wrapped run's routed member commitments are all zero. -/
theorem zeroFamily_run_memberCommitments
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) (i : ℕ)
    (m : Fin (deployedSetQueries vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1
      (wrappedPreIpaRecord
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) i).length) :
    deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1
      (wrappedPreIpaRecord
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O)) i m = 0 := by
  have hps := zeroFamily_run_erase basis vkS hfixed hperm O
  revert m
  rw [hps]
  intro m
  exact deployedSetMemberCommitments_zeroData basis vkS hfixed hperm _ i m

end RunShape

section BatchWitness

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)

/-- The wrapped run's member representations have zero coordinates: the covered lookups land in
the zero proof's all-zero assembly source. -/
theorem zeroFamily_run_memberRepresentations
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp)
    (hcov : DeployedMembersCovered vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.algebraicProof [zeroAlgebraicPoint basis])
    (ν : Fin 11 → Fp) (i : ℕ)
    (hi : i < deployedX4PairCount vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1 (chRecord ν (fun _ => 0)))
    (m : Fin (deployedSetQueries vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1 (chRecord ν (fun _ => 0)) i).length) :
    (deployedMemberRepresentationsOfCovered
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O).1
        [zeroAlgebraicPoint basis] hcov ν i hi).coeffs m = 0 ∧
      (deployedMemberRepresentationsOfCovered
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O).1
        [zeroAlgebraicPoint basis] hcov ν i hi).uComp m = 0 ∧
      (deployedMemberRepresentationsOfCovered
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O).1
        [zeroAlgebraicPoint basis] hcov ν i hi).wComp m = 0 := by
  have hp := zeroFamily_wrapped_run basis vkS hfixed hperm O
  refine coveredCommitmentRepresentation_zeroData basis ?_ ?_ (hcov ν i hi m)
  · intro ap hap
    rw [show ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.algebraicProof = zeroAlgebraicProofString basis from by
          rw [hp]; rfl]
      at hap
    exact zeroAlgebraicProofString_source_eq basis hap
  · have hlist : deployedSetQueries vkS (fun _ _ => 0)
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O).1.proof.1 (chRecord ν (fun _ => 0)) i =
        deployedSetQueries vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
          (chRecord ν (fun _ => 0)) i := by
      rw [zeroFamily_run_erase basis vkS hfixed hperm O]
    have hmem : (deployedSetQueries vkS (fun _ _ => 0)
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
          basis).run O).1.proof.1 (chRecord ν (fun _ => 0)) i).getD
        (m : ℕ) (.point 0, []) ∈
        deployedSetQueries vkS (fun _ _ => 0)
          (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0)) i := by
      rw [← hlist, List.getD_eq_getElem _ _ m.isLt]
      exact List.getElem_mem _
    exact deployedSetQueries_refZeroData vkS hfixed hperm _ i _ hmem

/-- **The zero family's deployed batch witness, at any shape and pair count.**  The batches are
the all-zero deployed batches against the run's provably-zero canonical aggregates, and every
per-member column equation is `0 = 0` through the covered lookup. -/
def zeroBatchWitness
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    DeployedBatchWitness (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O) where
  fixedRepresentations := [zeroAlgebraicPoint basis]
  canonical := by
    rw [zeroFamily_wrapped_run]
    exact zeroWfProof_canonical basis vkS hfixed hperm
  membersCovered := by
    rw [zeroFamily_wrapped_run]
    exact zeroFamily_membersCovered basis vkS hfixed hperm
  batches := zeroDeployedBatchesFull basis vkS (fun _ _ => 0) _ _
    (zeroFamily_run_x4BatchCommitments basis vkS hfixed hperm O)
    (zeroFamily_run_memberCommitments basis vkS hfixed hperm O)
    _ _ _
    (zeroFamily_run_aMulti basis vkS hfixed hperm O)
    (zeroFamily_run_multiU basis vkS hfixed hperm O)
    (zeroFamily_run_multiBlind basis vkS hfixed hperm O)
  x4Source :=
    { coeffs := fun _ _ => 0
      uComp := fun _ => 0
      wComp := fun _ => 0
      commitment := by
        intro i
        change _ = x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS
          (fun _ _ => 0)
          ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
            basis).run O).1.proof.1
          (wrappedPreIpaRecord
            ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
              basis).run O)) i
        rw [zeroFamily_run_x4BatchCommitments basis vkS hfixed hperm O i]
        simp [commit] }
  x4Coeffs := rfl
  x4U := rfl
  x4W := rfl
  memberCoeffs := by
    intro i hi
    funext m
    exact ((zeroFamily_run_memberRepresentations basis vkS hfixed hperm O _ _ i hi m).1).symm
  memberU := by
    intro i hi
    funext m
    exact ((zeroFamily_run_memberRepresentations basis vkS hfixed hperm O _ _ i hi m).2.1).symm
  memberW := by
    intro i hi
    funext m
    exact ((zeroFamily_run_memberRepresentations basis vkS hfixed hperm O _ _ i hi m).2.2).symm

/-- The zero family's outcome provider: always the batch branch, never a relation. -/
def zeroRootOutcome
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    DeployedRootOutcomeProvider (zeroOnlineMemberFamily vkS hfixed hperm).toFamily :=
  fun basis O => PSum.inl (zeroBatchWitness basis vkS hfixed hperm O)

end BatchWitness

/-! ## Batch-free forms of the four batched root sets

At all-zero coordinate columns each batched root set equals a formula naming no batch structure —
only the key, the instance commitments, the proof string and the challenge record.  That is what
carries the sets across the propositional equality between the wrapped run's proof string and the
zero proof string.
-/

section BatchFree

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G]
variable (urs : Zcash.Arithmetic.URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
  (ic : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
  (ch : Challenges shape.k Fp)
  {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
  (batches : DeployedAlgebraicBatches urs hk vk ic ps ch aggregate aggregateU aggregateW)

/-- The `x₄` root set at zero columns, batch-free. -/
theorem deployedX4RootSet_of_zeroCols
    (hcols : batches.x4.coeffs = fun _ _ => 0) :
    deployedX4RootSet urs hk vk ic ps ch batches =
      ↑(szBadSet (algebraicBatchErrorPolynomial (evalVector urs.k ch.x3)
        (fun _ _ => (0 : Fp)) (x4BatchEvals vk ic ps ch))) := by
  unfold deployedX4RootSet
  rw [hcols]

/-- The `x₃` root set at zero columns, batch-free. -/
theorem deployedX3RootSet_of_zeroCols
    (hcols : batches.x4.coeffs = fun _ _ => 0) :
    deployedX3RootSet urs hk vk ic ps ch batches =
      ↑(szBadSet (clearedQuotientErrorPolynomial (deployedAllPts vk ic ps ch)
          (deployedAlgebraicSetPoints vk ic ps ch)
          (fun _ => coeffsToPoly (fun _ : Fin (2 ^ urs.k) => (0 : Fp)))
          (deployedAlgebraicSetInterpolants vk ic ps ch)
          (fun j => ch.x2 ^ (j : ℕ))
          (coeffsToPoly (fun _ : Fin (2 ^ urs.k) => (0 : Fp)))) ∪
        deployedAllPts vk ic ps ch) := by
  unfold deployedX3RootSet deployedX3ErrorPolynomial deployedAlgebraicSetColumns
    deployedAlgebraicQPrime
  rw [hcols]

/-- The `x₂` root set at zero columns, batch-free. -/
theorem deployedX2RootSet_of_zeroCols
    (hcols : batches.x4.coeffs = fun _ _ => 0) :
    deployedX2RootSet urs hk vk ic ps ch batches =
      {x | ∃ node, node ∈ deployedAllPts vk ic ps ch ∧
        x ∈ szBadSet (nodeBindingErrorPolynomial (deployedAllPts vk ic ps ch)
          (deployedAlgebraicSetPoints vk ic ps ch)
          (fun _ => coeffsToPoly (fun _ : Fin (2 ^ urs.k) => (0 : Fp)))
          (deployedAlgebraicSetInterpolants vk ic ps ch) node)} := by
  unfold deployedX2RootSet deployedAlgebraicSetColumns
  rw [hcols]

/-- The `x₁` union root set at zero member columns, batch-free. -/
theorem deployedX1AllRootSet_of_zeroCols
    (hx1 : ∀ i (hi : i < deployedX4PairCount vk ic ps ch),
      (batches.x1 i hi).coeffs = fun _ _ => 0) :
    deployedX1AllRootSet urs hk vk ic ps ch batches =
      {x | ∃ i : Fin shape.numPointSets,
        ∃ _hi : (i : ℕ) < deployedX4PairCount vk ic ps ch,
        ∃ idx : ℕ,
        ∃ _hidx : idx < ((deployedSetsForEval vk ic ps ch).getD (i : ℕ) ([], [], 0)).1.length,
          x ∈ szBadSet (memberBindingErrorPolynomial
            (fun _ : Fin (deployedSetQueries vk ic ps ch (i : ℕ)).length =>
              coeffsToPoly (fun _ : Fin (2 ^ urs.k) => (0 : Fp)))
            (fun m : Fin (deployedSetQueries vk ic ps ch (i : ℕ)).length =>
              ((deployedSetQueries vk ic ps ch (i : ℕ)).getD (m : ℕ) (.point 0, [])).2.getD
                idx 0)
            (((deployedSetsForEval vk ic ps ch).getD (i : ℕ) ([], [], 0)).1.getD idx 0))} := by
  unfold deployedX1AllRootSet
  ext x
  simp only [Set.mem_setOf_eq]
  refine exists_congr fun i => ?_
  unfold deployedX1RootSet
  by_cases hi : (i : ℕ) < deployedX4PairCount vk ic ps ch
  · rw [dif_pos hi]
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨idx, hidx⟩
      refine ⟨hi, (idx : ℕ), idx.isLt, ?_⟩
      unfold deployedX1RootPolynomial at hidx
      rw [hx1 (i : ℕ) hi] at hidx
      rw [List.getD_eq_getElem _ _ idx.isLt]
      exact hidx
    · rintro ⟨_, idx, hidx0, hidx⟩
      refine ⟨⟨idx, hidx0⟩, ?_⟩
      unfold deployedX1RootPolynomial
      rw [hx1 (i : ℕ) hi]
      rw [List.getD_eq_getElem _ _ hidx0] at hidx
      exact hidx
  · rw [dif_neg hi]
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨hi', -⟩
    exact hi hi'

end BatchFree

/-! ## The six root sets, as functions of the pre-IPA reads -/

section ClosedForms

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)

/-- The `ξ` event's root set at zero data: the shifted-commitment discrepancy quadratic. -/
def zeroXiRootSet (_basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  ↑(szBadSet (ipaShiftXiPolynomial
    (commitGen (evalVector shape.k ch.x3) (fun _ : Fin (2 ^ shape.k) => (0 : Fp)) -
      multiopenValue vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)
    (commitGen (evalVector shape.k ch.x3) (fun _ : Fin (2 ^ shape.k) => (0 : Fp)))))

/-- The `z` event's root set at zero data. -/
def zeroZRootSet (_basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  ↑(szBadSet (ipaShiftZPolynomial
    (commitGen (evalVector shape.k ch.x3) (fun _ : Fin (2 ^ shape.k) => (0 : Fp)) -
      multiopenValue vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch) 0 0
    (commitGen (evalVector shape.k ch.x3) (fun _ : Fin (2 ^ shape.k) => (0 : Fp))) ch.xi))

/-- The `x₄` event's root set at zero data: the batch error over zero columns. -/
def zeroX4RootSet (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  ↑(szBadSet (algebraicBatchErrorPolynomial
    (urs := ursOfAugmentedBasis shape.k basis) (evalVector shape.k ch.x3)
    (fun _ _ => (0 : Fp))
    (x4BatchEvals vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)))

/-- The `x₃` event's root set at zero data: the cleared quotient error, plus the opening points
the `x₃` squeeze must avoid. -/
def zeroX3RootSet (_basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  ↑(szBadSet (clearedQuotientErrorPolynomial
      (deployedAllPts vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)
      (deployedAlgebraicSetPoints vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)
      (fun _ => coeffsToPoly (fun _ : Fin (2 ^ shape.k) => (0 : Fp)))
      (deployedAlgebraicSetInterpolants vkS (fun _ _ => 0)
        (zeroProofString shape Fp VestaG) ch)
      (fun j => ch.x2 ^ (j : ℕ))
      (coeffsToPoly (fun _ : Fin (2 ^ shape.k) => (0 : Fp)))) ∪
    deployedAllPts vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)

/-- The `x₂` event's root set at zero data: node binding at every opening point. -/
def zeroX2RootSet (_basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  {x | ∃ node, node ∈ deployedAllPts vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch ∧
    x ∈ szBadSet (nodeBindingErrorPolynomial
      (deployedAllPts vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)
      (deployedAlgebraicSetPoints vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch)
      (fun _ => coeffsToPoly (fun _ : Fin (2 ^ shape.k) => (0 : Fp)))
      (deployedAlgebraicSetInterpolants vkS (fun _ _ => 0)
        (zeroProofString shape Fp VestaG) ch) node)}

/-- The `x₁` event's root set at zero data: member binding within every routed point set. -/
def zeroX1RootSet (_basis : AugmentedIndex (2 ^ shape.k) → VestaG) (vkS : VerifyingKey shape Fp VestaG)
    (ch : Challenges shape.k Fp) : Set Fp :=
  {x | ∃ i : Fin shape.numPointSets,
    ∃ _hi : (i : ℕ) < deployedX4PairCount vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch,
    ∃ idx : ℕ,
    ∃ _hidx : idx < ((deployedSetsForEval vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch).getD (i : ℕ) ([], [], 0)).1.length,
      x ∈ szBadSet (memberBindingErrorPolynomial
        (fun _ : Fin (deployedSetQueries vkS (fun _ _ => 0)
          (zeroProofString shape Fp VestaG) ch (i : ℕ)).length =>
          coeffsToPoly (fun _ : Fin (2 ^ shape.k) => (0 : Fp)))
        (fun m : Fin (deployedSetQueries vkS (fun _ _ => 0)
          (zeroProofString shape Fp VestaG) ch (i : ℕ)).length =>
          ((deployedSetQueries vkS (fun _ _ => 0)
            (zeroProofString shape Fp VestaG) ch (i : ℕ)).getD (m : ℕ)
              (.point 0, [])).2.getD idx 0)
        (((deployedSetsForEval vkS (fun _ _ => 0)
          (zeroProofString shape Fp VestaG) ch).getD (i : ℕ) ([], [], 0)).1.getD idx 0))}

/-- **The zero family's six root sets in closed form**: pure functions of the challenge record,
mentioning no batch structure, no run, and no oracle.  The stages compute exactly these. -/
def zeroRootSetCh (ch : Challenges shape.k Fp) (i : Fin 6) : Set Fp :=
  if i.val = 0 then zeroXiRootSet basis vkS ch
  else if i.val = 1 then zeroZRootSet basis vkS ch
  else if i.val = 2 then zeroX4RootSet basis vkS ch
  else if i.val = 3 then zeroX3RootSet basis vkS ch
  else if i.val = 4 then zeroX2RootSet basis vkS ch
  else zeroX1RootSet basis vkS ch

@[simp] theorem zeroRootSetCh_zero (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 0 = zeroXiRootSet basis vkS ch := rfl

@[simp] theorem zeroRootSetCh_one (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 1 = zeroZRootSet basis vkS ch := rfl

@[simp] theorem zeroRootSetCh_two (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 2 = zeroX4RootSet basis vkS ch := rfl

@[simp] theorem zeroRootSetCh_three (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 3 = zeroX3RootSet basis vkS ch := rfl

@[simp] theorem zeroRootSetCh_four (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 4 = zeroX2RootSet basis vkS ch := rfl

@[simp] theorem zeroRootSetCh_five (ch : Challenges shape.k Fp) :
    zeroRootSetCh basis vkS ch 5 = zeroX1RootSet basis vkS ch := rfl

/-- The closed forms at the pre-IPA reads. -/
def zeroRootSet (ν : Fin 11 → Fp) (i : Fin 6) : Set Fp :=
  zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) i

end ClosedForms

section ClosedFormLemma

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- **Every zero-family root event is its closed form.**  The outcome match reduces on the
always-`inl` provider; the batch data is definitionally zero; the run's proof string, aggregate
coordinates, and blinding coordinates rewrite to their zero values. -/
theorem deployedRootBad_zeroFamily
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) (i : Fin 6) :
    deployedRootBad (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
      (zeroRootOutcome vkS hfixed hperm) basis
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O) O i =
    zeroRootSet basis vkS
      (wrappedPreIpaReads
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O))
      i := by
  have hps := zeroFamily_run_erase basis vkS hfixed hperm O
  have haM := zeroFamily_run_aMulti basis vkS hfixed hperm O
  have hmU := zeroFamily_run_multiU basis vkS hfixed hperm O
  have hs : ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
      basis).run O).1.s = fun _ => 0 := by
    rw [zeroFamily_wrapped_run]; rfl
  have hsU : ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
      basis).run O).1.sU = 0 := by
    rw [zeroFamily_wrapped_run]; rfl
  have hcols : ((zeroBatchWitness basis vkS hfixed hperm O).batches).x4.coeffs =
      fun _ _ => 0 := rfl
  have hx1 : ∀ j (hj : j < deployedX4PairCount vkS (fun _ _ => 0)
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        basis).run O).1.proof.1
      (wrappedPreIpaRecord
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O))),
      (((zeroBatchWitness basis vkS hfixed hperm O).batches).x1 j hj).coeffs =
        fun _ _ => 0 := fun _ _ => rfl
  fin_cases i
  · -- the `ξ` shift event
    show (↑(szBadSet (ipaShiftXiPolynomial _ _)) : Set Fp) = _
    rw [haM, hs, hps]
    rfl
  · -- the `z` shift event
    show (↑(szBadSet (ipaShiftZPolynomial _ _ _ _ _)) : Set Fp) = _
    rw [haM, hs, hsU, hmU, hps]
    rfl
  · -- the `x₄` unbatching event
    show deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      _ _ _ = _
    rw [deployedX4RootSet_of_zeroCols (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) _ _ ((zeroBatchWitness basis vkS hfixed hperm O).batches) hcols, hps]
    rfl
  · -- the `x₃` cleared-quotient event
    show deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      _ _ _ = _
    rw [deployedX3RootSet_of_zeroCols (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) _ _ ((zeroBatchWitness basis vkS hfixed hperm O).batches) hcols, hps]
    rfl
  · -- the `x₂` node-binding event
    show deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      _ _ _ = _
    rw [deployedX2RootSet_of_zeroCols (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) _ _ ((zeroBatchWitness basis vkS hfixed hperm O).batches) hcols, hps]
    rfl
  · -- the `x₁` member-binding event
    show deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl vkS (fun _ _ => 0)
      _ _ _ = _
    rw [deployedX1AllRootSet_of_zeroCols (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) _ _ ((zeroBatchWitness basis vkS hfixed hperm O).batches) hx1, hps]
    rfl

end ClosedFormLemma

/-! ## Prefix injectivity, at any shape

Each transcript stage absorbs before it squeezes, so the eleven pre-IPA prefixes have strictly
increasing lengths and the squeeze points are pairwise distinct — at every shape, not only at the
decidable witness shape.
-/

section Injectivity

/-- The pre-IPA prefix lengths are strictly increasing, at every shape. -/
theorem preIpaLen_strictMono (n₀ : ℕ) : StrictMono (preIpaLen shape n₀) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  fin_cases j <;> simp [preIpaLen]
  all_goals omega

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- The zero proof's eleven pre-IPA squeeze points are pairwise distinct. -/
theorem zeroFamily_prefixesPre_injective {i j : Fin 11} (hij : i ≠ j) :
    algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).init
        (zeroWfProof basis vkS hfixed hperm) i ≠
      algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).init
        (zeroWfProof basis vkS hfixed hperm) j := by
  intro hEq
  apply hij
  have hli := preIpaSqueezePoints_length_eq
    (zeroOnlineMemberFamily vkS hfixed hperm).init
    (zeroWfProof basis vkS hfixed hperm).proof.1
    (zeroWfProof basis vkS hfixed hperm).proof.2 i
  have hlj := preIpaSqueezePoints_length_eq
    (zeroOnlineMemberFamily vkS hfixed hperm).init
    (zeroWfProof basis vkS hfixed hperm).proof.1
    (zeroWfProof basis vkS hfixed hperm).proof.2 j
  refine (preIpaLen_strictMono (shape := shape)
    ((zeroOnlineMemberFamily vkS hfixed hperm).init.length)).injective ?_
  rw [← hli, ← hlj]
  exact congrArg (fun t : BTranscript Fp VestaG _ => t.val.length) hEq

end Injectivity

/-! ## Blindness of each closed form to its own squeeze

Every root event's set reads only the assembled queries and the challenge fields squeezed before
that event.  Each proof rewrites the one dependence they share, `assembleQueries`, and lets the
remaining projections reduce.  Comparing two whole challenge records instead is a kernel defeq
the multiopen assembly makes hopeless.
-/

section Blindness

variable {G : Type*} [Field Fp] [Inhabited G] {shapeB : Shape}
  (vk : VerifyingKey shapeB Fp G) (ic : Fin shapeB.numProofs → ℕ → G)
  (ps : ProofString shapeB Fp G) (ch : Challenges shapeB.k Fp) (v : Fp)

/-- The query assembly reads `θ, β, γ, y, x` only, so it never reads `x₁`. -/
theorem assembleQueries_x1_blind :
    assembleQueries vk ic ps {ch with x1 := v} = assembleQueries vk ic ps ch := rfl

/-- The query assembly never reads `x₂`. -/
theorem assembleQueries_x2_blind :
    assembleQueries vk ic ps {ch with x2 := v} = assembleQueries vk ic ps ch := rfl

/-- The query assembly never reads `x₄`. -/
theorem assembleQueries_x4_blind :
    assembleQueries vk ic ps {ch with x4 := v} = assembleQueries vk ic ps ch := rfl

/-- The query assembly never reads `ξ`. -/
theorem assembleQueries_xi_blind :
    assembleQueries vk ic ps {ch with xi := v} = assembleQueries vk ic ps ch := rfl

/-- The query assembly never reads `z`. -/
theorem assembleQueries_z_blind :
    assembleQueries vk ic ps {ch with z := v} = assembleQueries vk ic ps ch := rfl

end Blindness

section BlindForms

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG) (ch : Challenges shape.k Fp) (v : Fp)

/-- Changing `x₁` moves only the compressed evaluation vectors, so the point list routed to each
set is unchanged. -/
private theorem getD_setsForEval_fst
    (pts : List (List Fp)) (e e' : List (List Fp)) (u : List Fp)
    (hlen : e.length = e'.length) :
    ∀ i : ℕ,
      ((((pts.zip e).zip u).map
        (fun p : (List Fp × List Fp) × Fp => (p.1.1, p.1.2, p.2))).getD i ([], [], 0)).1 =
      ((((pts.zip e').zip u).map
        (fun p : (List Fp × List Fp) × Fp => (p.1.1, p.1.2, p.2))).getD i ([], [], 0)).1 := by
  induction pts generalizing e e' u with
  | nil => intro i; simp
  | cons p pts ih =>
      match e, e', hlen with
      | [], [], _ => intro i; simp
      | a :: e, a' :: e', hlen =>
          match u with
          | [] => intro i; simp
          | c :: u =>
              intro i
              match i with
              | 0 => simp
              | i + 1 =>
                  simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
                  exact ih e e' u (by simpa using hlen) i

/-- The `x₁` squeeze does not move the deployed pair count. -/
theorem deployedX4PairCount_x1_blind :
    deployedX4PairCount vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG)
        {ch with x1 := v} =
      deployedX4PairCount vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG) ch := by
  simp only [deployedX4PairCount, deployedX4Pairs, deployedX4Qs, List.length_zip, List.length_map]
  rw [assembleQueries_x1_blind]

/-- The `x₁` squeeze does not move a point set's routed members. -/
theorem deployedSetQueries_x1_blind (i : ℕ) :
    deployedSetQueries vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG)
        {ch with x1 := v} i =
      deployedSetQueries vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG) ch i := by
  simp only [deployedSetQueries]
  rw [assembleQueries_x1_blind]

/-- The `x₁` squeeze does not move a point set's point list. -/
theorem deployedSetsForEval_fst_x1_blind (i : ℕ) :
    ((deployedSetsForEval vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG)
        {ch with x1 := v}).getD i ([], [], 0)).1 =
      ((deployedSetsForEval vkS (fun _ _ => (0 : VestaG)) (zeroProofString shape Fp VestaG)
        ch).getD i ([], [], 0)).1 := by
  simp only [deployedSetsForEval]
  rw [assembleQueries_x1_blind]
  exact getD_setsForEval_fst _ _ _ _ (by simp) i

/-- The `ξ` event's closed form is fixed before the `ξ` squeeze. -/
theorem zeroXiRootSet_blind :
    zeroXiRootSet basis vkS {ch with xi := v} = zeroXiRootSet basis vkS ch := by
  simp only [zeroXiRootSet, multiopenValue]
  rw [assembleQueries_xi_blind]

/-- The `z` event's closed form is fixed before the `z` squeeze. -/
theorem zeroZRootSet_blind :
    zeroZRootSet basis vkS {ch with z := v} = zeroZRootSet basis vkS ch := by
  simp only [zeroZRootSet, multiopenValue]
  rw [assembleQueries_z_blind]

/-- The `x₄` event's closed form is fixed before the `x₄` squeeze. -/
theorem zeroX4RootSet_blind :
    zeroX4RootSet basis vkS {ch with x4 := v} = zeroX4RootSet basis vkS ch := by
  unfold zeroX4RootSet x4BatchEvals deployedX4PairCount deployedX4Pairs deployedX4Qs
    deployedBaseEval
  rw [assembleQueries_x4_blind]

/-- The `x₃` event's closed form is fixed before the `x₃` squeeze. -/
theorem zeroX3RootSet_blind :
    zeroX3RootSet basis vkS {ch with x3 := v} = zeroX3RootSet basis vkS ch := by
  unfold zeroX3RootSet deployedAllPts deployedAlgebraicSetPoints
    deployedAlgebraicSetInterpolants deployedSetPts deployedSetsForEval deployedX4PairCount
    deployedX4Pairs deployedX4Qs
  rw [assembleQueries_x3_blind]

/-- The `x₂` event's closed form is fixed before the `x₂` squeeze. -/
theorem zeroX2RootSet_blind :
    zeroX2RootSet basis vkS {ch with x2 := v} = zeroX2RootSet basis vkS ch := by
  unfold zeroX2RootSet deployedAllPts deployedAlgebraicSetPoints
    deployedAlgebraicSetInterpolants deployedSetPts deployedSetsForEval deployedX4PairCount
    deployedX4Pairs deployedX4Qs
  rw [assembleQueries_x2_blind]

/-- The `x₁` event's closed form is fixed before the `x₁` squeeze.  Compressing by `x₁` moves only
the evaluation vectors, which the member-binding polynomial never reads. -/
theorem zeroX1RootSet_blind :
    zeroX1RootSet basis vkS {ch with x1 := v} = zeroX1RootSet basis vkS ch := by
  have hcount := deployedX4PairCount_x1_blind vkS ch v
  have hq := fun i : ℕ => deployedSetQueries_x1_blind vkS ch v i
  have hpts := fun i : ℕ => deployedSetsForEval_fst_x1_blind vkS ch v i
  ext x
  simp only [zeroX1RootSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, idx, hidx, hx⟩
    rw [hcount] at hi
    refine ⟨i, hi, idx, ?_, ?_⟩
    · rw [← hpts (i : ℕ)]; exact hidx
    · rw [← hpts (i : ℕ), ← hq (i : ℕ)]; exact hx
  · rintro ⟨i, hi, idx, hidx, hx⟩
    rw [← hcount] at hi
    refine ⟨i, hi, idx, ?_, ?_⟩
    · rw [hpts (i : ℕ)]; exact hidx
    · rw [hpts (i : ℕ), hq (i : ℕ)]; exact hx

end BlindForms

/-! ## The six stages, the trace, and the family -/

section Stages

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- A stage reads every pre-IPA squeeze point except its own event's, re-reading index `0` in that
slot.  No root challenge index is `0`, so the dodge never returns the event's own index. -/
def rootDodge (i : Fin 6) (j : Fin 11) : Fin 11 :=
  if j = deployedRootChallengeIndex i then 0 else j

/-- The dodge never lands on the event's own squeeze index. -/
theorem rootDodge_ne (i : Fin 6) (j : Fin 11) :
    rootDodge i j ≠ deployedRootChallengeIndex i := by
  have hne : deployedRootChallengeIndex i ≠ 0 := by fin_cases i <;> decide
  unfold rootDodge
  split
  · exact fun h => hne h.symm
  · assumption

/-- **The zero family's six staged root computations.**  Stage `i` reads the pre-IPA squeeze
answers, dodging its own event's point, and computes the event's closed-form root set from them. -/
def zeroRootStage (i : Fin 6) :
    OracleComp
      (BTranscript Fp VestaG
        (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
          3 * shape.k)) Fp (Set Fp) :=
  (OracleComp.readFin (F := Fp)
    (fun j : Fin 11 =>
      algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) (rootDodge i j))).bind
    fun answers => .pure (zeroRootSet basis vkS answers i)

/-- The wrapped run's pre-IPA reads are the oracle's answers at the family's fixed squeeze
points. -/
theorem zeroFamily_reads_eq
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    wrappedPreIpaReads
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O) =
      fun j => O (algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) j) := by
  rw [wrappedPreIpaReads_run]
  rfl

/-- Dodging one read is a single-field change of the challenge record. -/
theorem chRecord_rootDodge (i : Fin 6) (ν : Fin 11 → Fp) :
    chRecord (k := shape.k) (fun j => ν (rootDodge i j)) (fun _ => 0) =
      (match i with
        | 0 => { chRecord (k := shape.k) ν (fun _ => 0) with xi := ν 0 }
        | 1 => { chRecord (k := shape.k) ν (fun _ => 0) with z := ν 0 }
        | 2 => { chRecord (k := shape.k) ν (fun _ => 0) with x4 := ν 0 }
        | 3 => { chRecord (k := shape.k) ν (fun _ => 0) with x3 := ν 0 }
        | 4 => { chRecord (k := shape.k) ν (fun _ => 0) with x2 := ν 0 }
        | _ => { chRecord (k := shape.k) ν (fun _ => 0) with x1 := ν 0 }) := by
  fin_cases i <;> simp [chRecord, rootDodge, deployedRootChallengeIndex]

/-- Every stage computes its event's actual root set. -/
theorem zeroRootStage_agrees (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    (zeroRootStage basis vkS hfixed hperm i).run O =
      deployedRootBad (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        (zeroRootOutcome vkS hfixed hperm) basis
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O)
        O i := by
  rw [deployedRootBad_zeroFamily, zeroRootStage, OracleComp.run_bind, OracleComp.run_readFin,
    OracleComp.run_pure, zeroFamily_reads_eq]
  set ν : Fin 11 → Fp := fun j =>
    O (algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).toFamily.init
      (zeroWfProof basis vkS hfixed hperm) j) with hν
  show zeroRootSet basis vkS (fun j => ν (rootDodge i j)) i = zeroRootSet basis vkS ν i
  unfold zeroRootSet
  have hrec := chRecord_rootDodge (shape := shape) i ν
  fin_cases i
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 0 j)) (fun _ => 0)) 0 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 0
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 0 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 0 ν]
    simp only [zeroRootSetCh_zero]
    exact zeroXiRootSet_blind basis vkS _ (ν 0)
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 1 j)) (fun _ => 0)) 1 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 1
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 1 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 1 ν]
    simp only [zeroRootSetCh_one]
    exact zeroZRootSet_blind basis vkS _ (ν 0)
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 2 j)) (fun _ => 0)) 2 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 2
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 2 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 2 ν]
    simp only [zeroRootSetCh_two]
    exact zeroX4RootSet_blind basis vkS _ (ν 0)
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 3 j)) (fun _ => 0)) 3 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 3
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 3 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 3 ν]
    simp only [zeroRootSetCh_three]
    exact zeroX3RootSet_blind basis vkS _ (ν 0)
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 4 j)) (fun _ => 0)) 4 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 4
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 4 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 4 ν]
    simp only [zeroRootSetCh_four]
    exact zeroX2RootSet_blind basis vkS _ (ν 0)
  · show zeroRootSetCh basis vkS (chRecord (fun j => ν (rootDodge 5 j)) (fun _ => 0)) 5 =
      zeroRootSetCh basis vkS (chRecord ν (fun _ => 0)) 5
    rw [show (chRecord (k := shape.k) (fun j => ν (rootDodge 5 j)) (fun _ => 0)) = _ from
      chRecord_rootDodge (shape := shape) 5 ν]
    simp only [zeroRootSetCh_five]
    exact zeroX1RootSet_blind basis vkS _ (ν 0)

/-- No stage queries its own event's squeeze point. -/
theorem zeroRootStage_fresh (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroOnlineMemberFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    deployedRootPoint (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
        ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O) i ∉
      (zeroRootStage basis vkS hfixed hperm i).queries O := by
  have hpoint : deployedRootPoint (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
      ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run O) i =
      algebraicFullPrefixesPre (zeroOnlineMemberFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) (deployedRootChallengeIndex i) := by
    unfold deployedRootPoint
    rw [zeroFamily_wrapped_run]
    rfl
  rw [hpoint]
  simp only [zeroRootStage, OracleComp.queries_bind, OracleComp.queries_readFin,
    OracleComp.queries, List.append_nil]
  intro hmem
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
  exact zeroFamily_prefixesPre_injective basis vkS hfixed hperm (rootDodge_ne i j) hj

/-- **The zero family's staged root trace, at any shape.** -/
def zeroRootTrace :
    DeployedRootOnlineTrace (zeroOnlineMemberFamily vkS hfixed hperm).toFamily
      (zeroRootOutcome vkS hfixed hperm) where
  stage := fun basis i => zeroRootStage basis vkS hfixed hperm i
  agrees := fun basis i O => zeroRootStage_agrees basis vkS hfixed hperm i O
  fresh := fun basis i O => zeroRootStage_fresh basis vkS hfixed hperm i O

/-- **An inhabitant of the deployed root family interface at any shape**, over any key with zero
group commitment families: the constant zero prover, the always-batch outcome, and the six-stage
root trace with live value-side root sets. -/
def zeroDeployedRootFamily :
    ComputedDeployedRootFSFamily shape where
  toComputedOnlineMemberFSFamily := zeroOnlineMemberFamily vkS hfixed hperm
  outcome := zeroRootOutcome vkS hfixed hperm
  rootTrace := zeroRootTrace vkS hfixed hperm
  outcome_source := fun basis _O witness h => by
    cases PSum.inl.inj h; rfl

end Stages

end Zcash.Snark
