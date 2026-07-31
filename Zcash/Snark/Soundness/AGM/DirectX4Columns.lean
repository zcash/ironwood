import Zcash.Snark.Soundness.AGM.DeployedX1
import Zcash.Snark.Soundness.AGM.OnlineMembers
import Zcash.Snark.Soundness.AGM.DeployedMultiopen
import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots

/-!
# Direct `x₄` column representations

The rewind-free decoder needs AGM coordinates for the `x₄` batch columns. The offline route
interpolates them out of the representation function; this module reads them off the online data
instead, so the columns feed a computable batch-or-relation decision.

Each column below the pair count is the `x₁`-compressed aggregate of one point set, so its
coordinates are that set's `x₁` power sum of member representations, which
`deployedMemberRepresentationsOfCovered` supplies. The last column is the prover's `q′`, which
carries its own representation.
-/

namespace Zcash.Snark

open scoped BigOperators

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

local instance vestaInhabitedDirectX4 : Inhabited VestaG := ⟨0⟩


/-- The set index whose compressed aggregate is `x₄` batch column `j`: the batch reads the pair
list in reverse. -/
def x4ColumnSetIndex {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (j : ℕ) : ℕ :=
  deployedX4PairCount vk instanceCommitment ps ch - 1 - j

/-- **The `x₄` batch column below the pair count is the `x₁` power sum of its set's members.**
This is the commitment identity the column representations are built against, extracted from the
`x₁` unbatch so both levels share one proof. -/
theorem x4BatchCommitments_eq_memberPowerSum {G : Type*} [AddCommGroup G] [Module Fp G]
    [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)}
    (hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch) :
    x4BatchCommitments urs hk vk instanceCommitment ps ch j
      = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch
          (x4ColumnSetIndex vk instanceCommitment ps ch
            (j : ℕ))).length,
          ch.x1 ^ (m : ℕ) •
            deployedSetMemberCommitments urs hk vk instanceCommitment ps ch
              (x4ColumnSetIndex vk instanceCommitment ps ch
                (j : ℕ)) m := by
  have hqs : x4ColumnSetIndex vk instanceCommitment ps ch (j : ℕ)
      < (deployedX4Qs vk instanceCommitment ps ch).length := by
    have hle : deployedX4PairCount vk instanceCommitment ps ch ≤
        (deployedX4Qs vk instanceCommitment ps ch).length := by
      rw [deployedX4PairCount_eq]
      simp only [deployedX4Pairs, List.length_zip]
      exact min_le_left _ _
    have : x4ColumnSetIndex vk instanceCommitment ps ch (j : ℕ)
        < deployedX4PairCount vk instanceCommitment ps ch := by
      unfold x4ColumnSetIndex
      omega
    omega
  rw [x4BatchCommitments_getD urs hk vk instanceCommitment ps ch hj]
  rw [show deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)
      = x4ColumnSetIndex vk instanceCommitment ps ch (j : ℕ) from rfl]
  rw [deployedX4Qs_getD_eval (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch hqs]
  rw [← Fin.sum_univ_eq_sum_range (fun m =>
    ch.x1 ^ m •
      ((deployedSetQueries vk instanceCommitment ps ch
        (x4ColumnSetIndex vk instanceCommitment ps ch
          (j : ℕ))).getD m (.point 0, [])).1.eval
      ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)]
  exact Finset.sum_congr rfl fun m _ => by rw [deployedSetMemberCommitments_apply]

/-! ## The direct column representations -/

/-- **AGM coordinates for every `x₄` batch column, read off the online data.** Columns below the
pair count take the `x₁` power sum of their set's member representations; the final column is the
prover's `q′`, which carries its own representation. No interpolation, no rewind. -/
def deployedX4ColumnRepresentationsOfCovered
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 → Fp) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        p.proof.1 (chRecord nu (fun _ => 0))) where
  coeffs := fun j =>
    if hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)) then
      ∑ m : Fin (deployedSetQueries vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0))
          (x4ColumnSetIndex vk instanceCommitment p.proof.1
            (chRecord nu (fun _ => 0)) (j : ℕ))).length,
        (chRecord nu (fun _ => 0)).x1 ^ (m : ℕ) •
        (deployedMemberRepresentationsOfCovered p fixed hcovered nu
          (x4ColumnSetIndex vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) (j : ℕ))
          (by unfold x4ColumnSetIndex; omega)).coeffs m
    else p.algebraicProof.multiopenQPrime.gPart
  uComp := fun j =>
    if hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)) then
      ∑ m : Fin (deployedSetQueries vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0))
          (x4ColumnSetIndex vk instanceCommitment p.proof.1
            (chRecord nu (fun _ => 0)) (j : ℕ))).length,
        (chRecord nu (fun _ => 0)).x1 ^ (m : ℕ) *
        (deployedMemberRepresentationsOfCovered p fixed hcovered nu
          (x4ColumnSetIndex vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) (j : ℕ))
          (by unfold x4ColumnSetIndex; omega)).uComp m
    else p.algebraicProof.multiopenQPrime.coeffs AugmentedIndex.u
  wComp := fun j =>
    if hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)) then
      ∑ m : Fin (deployedSetQueries vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0))
          (x4ColumnSetIndex vk instanceCommitment p.proof.1
            (chRecord nu (fun _ => 0)) (j : ℕ))).length,
        (chRecord nu (fun _ => 0)).x1 ^ (m : ℕ) *
        (deployedMemberRepresentationsOfCovered p fixed hcovered nu
          (x4ColumnSetIndex vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) (j : ℕ))
          (by unfold x4ColumnSetIndex; omega)).wComp m
    else p.algebraicProof.multiopenQPrime.coeffs AugmentedIndex.w
  commitment := by
    intro j
    by_cases hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0))
    · simp only [dif_pos hj]
      rw [(deployedMemberRepresentationsOfCovered p fixed hcovered nu
        (x4ColumnSetIndex vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) (j : ℕ))
        (by unfold x4ColumnSetIndex; omega)).power_commitment
        (chRecord nu (fun _ => 0)).x1]
      exact (x4BatchCommitments_eq_memberPowerSum _ rfl vk instanceCommitment _ _ hj).symm
    · simp only [dif_neg hj]
      rw [x4BatchCommitments, if_neg hj]
      exact (AlgebraicPoint.point_eq_components _).symm

/-- The direct column representation is transport-stable in its proof and challenge inputs.
`HEq` is the natural statement because the column index type itself contains those inputs. -/
theorem deployedX4ColumnRepresentationsOfCovered_heq
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p p' : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (hcovered' : DeployedMembersCovered vk instanceCommitment p'.algebraicProof fixed)
    (nu nu' : Fin 11 → Fp) (hp : p = p') (hnu : nu = nu') :
    HEq (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu)
      (deployedX4ColumnRepresentationsOfCovered p' fixed hcovered' nu') := by
  subst p'
  subst nu'
  have hc : hcovered = hcovered' := Subsingleton.elim _ _
  subst hcovered'
  rfl

set_option maxHeartbeats 600000 in
/-- Transport the retained-source reconstruction equation to any propositionally equal proof and
challenge vector.  Stating the transport once avoids casts at every adaptive caller. -/
theorem DeployedBatchWitness.x4CoveredSource_reconstruct
    {family : ComputedAlgebraicFSFamily shape}
    {pnu : WrappedAlgebraicOutput family basis}
    (witness : DeployedBatchWitness family basis pnu)
    (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis))
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered (family.vk basis) (family.instanceCommitment basis)
      p.algebraicProof fixed)
    (nu : Fin 11 → Fp) (hp : pnu.1 = p) (hnu : wrappedPreIpaReads pnu = nu)
    (hsource : HEq witness.x4Source
      (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu)) :
    ((∑ j : Fin (deployedX4PairCount (family.vk basis)
          (family.instanceCommitment basis) p.proof.1 (chRecord nu (fun _ => 0)) + 1),
        nu 8 ^ (j : Nat) •
          (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu).coeffs j) =
        p.aMulti nu) ∧
      ((∑ j : Fin (deployedX4PairCount (family.vk basis)
          (family.instanceCommitment basis) p.proof.1 (chRecord nu (fun _ => 0)) + 1),
        nu 8 ^ (j : Nat) *
          (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu).uComp j) =
        p.multiU nu) := by
  subst p
  subst nu
  have hs : witness.x4Source =
      deployedX4ColumnRepresentationsOfCovered pnu.1 fixed hcovered
        (wrappedPreIpaReads pnu) := eq_of_heq hsource
  constructor
  · rw [← hs]
    exact witness.x4Source_reconstruct
  · rw [← hs]
    exact witness.x4Source_reconstructU

/-! ## The direct batch, without interpolation -/

/-- The aggregate coordinates an `AlgebraicWfProof` declares open to the deployed commitment. -/
theorem aggregate_opens_deployedCommitment
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (p.aMulti nu)
        + p.multiU nu • (ursOfAugmentedBasis shape.k basis).u
        + p.multiBlind nu • (ursOfAugmentedBasis shape.k basis).w
      = deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
          p.proof.1 (chRecord nu (fun _ => 0)) := by
  rw [p.multiopen_repr nu]
  exact (deployedCommitment_eq_multiopen vk instanceCommitment p.proof.1 _).symm

/-- **The deployed `x₄` batch, decoded directly.** The columns are read off the online coverage
and the aggregate equation comes from the proof's own multiopen representation, so the
batch-or-relation decision needs no offline interpolation — the drop-in replacement for the
Vandermonde compatibility adapter. -/
def deployedX4BatchOfCoveredOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 → Fp) :
    AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
        (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
          p.proof.1 (chRecord nu (fun _ => 0)))
        (p.aMulti nu) (p.multiU nu) (p.multiBlind nu)
        (chRecord (k := shape.k) nu (fun _ => 0)).x4 ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w :=
  deployedX4AlgebraicBatchOrRelation (ursOfAugmentedBasis shape.k basis) rfl vk
    instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))
    (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu)
    (p.aMulti nu) (p.multiU nu) (p.multiBlind nu)
    (aggregate_opens_deployedCommitment p nu)

/-- Provenance-preserving form of the direct deployed `x₄` batch. -/
def deployedX4BatchOfCoveredWithSourceOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 → Fp) :
    AlgebraicPowerBatchWithSource (ursOfAugmentedBasis shape.k basis)
        (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu)
        (p.aMulti nu) (p.multiU nu) (p.multiBlind nu)
        (chRecord (k := shape.k) nu (fun _ => 0)).x4 ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w :=
  deployedX4AlgebraicBatchWithSourceOrRelation (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))
    (deployedX4ColumnRepresentationsOfCovered p fixed hcovered nu)
    (p.aMulti nu) (p.multiU nu) (p.multiBlind nu)
    (aggregate_opens_deployedCommitment p nu)

/-! ## The direct outcome provider

The same batch-or-relation walk as the compatibility adapter, with the `x₄` level supplied by the
direct decode above instead of the offline interpolation. The `x₄` columns come from online
coverage, the per-set `x₁` columns from the same member representations, and every disagreement
returns explicit relation coefficients.
-/

/-
The explicit polynomial total-cost model for this postprocessing — field operations and data
traversal, separate from the black-box adversary call count — is
`Composition.DirectPathCost.deployedDirectDecodeOps` with its shape-polynomial bound
`deployedDirectDecodeOps_le` and the captured-shape evaluations in `Fixtures.MaxShapeBounds`.
-/

/-- The coverage certificate transported to the wrapped run. -/
theorem ComputedOnlineMemberFSFamily.membersCovered_wrapped
    (family : ComputedOnlineMemberFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    DeployedMembersCovered (family.vk basis) (family.instanceCommitment basis)
      ((wrappedAdversary family.toFamily basis).run O).1.algebraicProof
      (family.fixedRepresentations basis) := by
  rw [wrappedAdversary_run_fst family.toFamily basis O]
  exact family.membersCovered basis O

/-- The canonicity certificate transported to the wrapped run. -/
theorem ComputedOnlineMemberFSFamily.canonical_wrapped
    (family : ComputedOnlineMemberFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    CanonicalOnlineMultiopenCoordinates
      ((wrappedAdversary family.toFamily basis).run O).1
      (family.fixedRepresentations basis) := by
  rw [wrappedAdversary_run_fst family.toFamily basis O]
  exact family.canonical basis O

/-- **The deployed root outcome, decoded directly.** It needs no field-capacity hypothesis,
because it never chooses ghost evaluation points. -/
def deployedRootOutcomeOfCovered
    (family : ComputedOnlineMemberFSFamily shape) :
    DeployedRootOutcomeProvider family.toFamily := fun basis O =>
  match deployedX4BatchOfCoveredWithSourceOrRelation
      ((wrappedAdversary family.toFamily basis).run O).1
      (family.fixedRepresentations basis) (family.membersCovered_wrapped basis O)
      (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O)) with
  | PSum.inr relation => PSum.inr relation
  | PSum.inl x4Result =>
      let x4Batch := x4Result.batch
      match finForallOrRelationWitness (fun i :
          Fin (deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
            ((wrappedAdversary family.toFamily basis).run O).1.proof.1
            (wrappedPreIpaRecord ((wrappedAdversary family.toFamily basis).run O))) =>
          deployedX1BatchOfCoveredWithSourceOrRelation
            ((wrappedAdversary family.toFamily basis).run O).1
            (family.fixedRepresentations basis) (family.membersCovered_wrapped basis O)
            (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
            x4Batch i i.isLt) with
      | PSum.inr relation => PSum.inr relation
      | PSum.inl results =>
          PSum.inl
            { fixedRepresentations := family.fixedRepresentations basis
              canonical := family.canonical_wrapped basis O
              membersCovered := family.membersCovered_wrapped basis O
              batches :=
                { x4 := x4Batch
                  x1 := fun i hi => (results ⟨i, hi⟩).batch }
              x4Source := deployedX4ColumnRepresentationsOfCovered
                ((wrappedAdversary family.toFamily basis).run O).1
                (family.fixedRepresentations basis) (family.membersCovered_wrapped basis O)
                (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
              x4Coeffs := x4Result.coeffs_eq
              x4U := x4Result.uComp_eq
              x4W := x4Result.wComp_eq
              memberCoeffs := fun i hi => (results ⟨i, hi⟩).coeffs_eq
              memberU := fun i hi => (results ⟨i, hi⟩).uComp_eq
              memberW := fun i hi => (results ⟨i, hi⟩).wComp_eq }

/-- A successful generated outcome retains exactly the direct online `x₄` source used to
construct it. -/
theorem deployedRootOutcomeOfCovered_x4Source
    (family : ComputedOnlineMemberFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family basis O = PSum.inl witness) :
    HEq witness.x4Source (deployedX4ColumnRepresentationsOfCovered
      (runProof family.toFamily basis O) (family.fixedRepresentations basis)
      (family.membersCovered basis O) (runReads family.toFamily basis O)) := by
  unfold deployedRootOutcomeOfCovered at hout
  split at hout
  · exact absurd hout (by simp)
  · dsimp only at hout
    split at hout
    · exact absurd hout (by simp)
    · cases PSum.inl.inj hout
      have hp := wrappedAdversary_run_fst family.toFamily basis O
      have hnu := wrappedPreIpaReads_run family.toFamily basis O
      exact deployedX4ColumnRepresentationsOfCovered_heq _ _ _ _ _ _ _ hp hnu

/-- A successful generated outcome retains exactly the family's fixed representations. -/
theorem deployedRootOutcomeOfCovered_fixedRepresentations
    (family : ComputedOnlineMemberFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family basis O = PSum.inl witness) :
    witness.fixedRepresentations = family.fixedRepresentations basis := by
  unfold deployedRootOutcomeOfCovered at hout
  split at hout
  · exact absurd hout (by simp)
  · dsimp only at hout
    split at hout
    · exact absurd hout (by simp)
    · cases PSum.inl.inj hout
      rfl

/-- **A deployed root family on the direct route.** The outcome is decoded from online coverage,
so no field-capacity hypothesis is needed and no ghost evaluation points are chosen. Its
chronology input is the staged root trace; exact leave-one-squeeze invariance is derived from that
trace. Reverse unbatching may depend on later challenges. -/
def ComputedDeployedRootFSFamily.ofCovered
    (family : ComputedOnlineMemberFSFamily shape)
    (trace : DeployedRootOnlineTrace family.toFamily
      (deployedRootOutcomeOfCovered family)) :
    ComputedDeployedRootFSFamily shape where
  toComputedOnlineMemberFSFamily := family
  outcome := deployedRootOutcomeOfCovered family
  rootTrace := trace
  outcome_source := fun basis O witness h => by
    unfold deployedRootOutcomeOfCovered at h
    split at h
    · exact absurd h (by simp)
    · dsimp only at h
      split at h
      · exact absurd h (by simp)
      · cases PSum.inl.inj h
        rfl

end Zcash.Snark
