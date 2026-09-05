import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots
import Zcash.Snark.Soundness.FiatShamir.Adversary.Provenance

/-!
# Constraint supply from retained online AGM provenance

This adapter builds the pre-`x` constraint polynomial from the exact representation list carried by
`DeployedBatchWitness`.  Plain members agree definitionally with the successful `x1` unbatch; the
only remaining disagreement branch is the explicit quotient-piece collision returned by
`decodedQuotientEqReassembledOrRelationWitness`.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm.otherPoints)

open Classical CompPoly.CPolynomial

universe u v

variable {shape : Shape}

local instance vestaInhabitedOnlineConstraint : Inhabited VestaG := ⟨0⟩

/-- Forget the success branch while retaining explicit relation data. -/
private def relationOption {A : Sort u} {R : Type v} : A ⊕' R → Option R
  | PSum.inl _ => none
  | PSum.inr relation => some relation

private theorem eq_inr_of_relationOption_eq_some {A : Sort u} {R : Type v}
    {outcome : A ⊕' R} {relation : R}
    (h : relationOption outcome = some relation) : outcome = PSum.inr relation := by
  cases outcome with
  | inl value => simp [relationOption] at h
  | inr found => simpa [relationOption] using h

/-- The relation projection of the coordinate comparison is invariant under coordinate equality;
the collision proofs themselves are proposition-valued and therefore irrelevant. -/
private theorem relationOption_separateOrRelationWitness_congr {n : Nat}
    (g : Fin n → VestaG) (U W : VestaG)
    {a₁ a₂ b₁ b₂ : Fin n → Fp} {α₁ α₂ α₁' α₂' β₁ β₂ β₁' β₂' : Fp}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hα : α₁ = α₂) (hα' : α₁' = α₂')
    (hβ : β₁ = β₂) (hβ' : β₁' = β₂')
    (e₁ : commitGen g a₁ + α₁ • U + β₁ • W =
      commitGen g b₁ + α₁' • U + β₁' • W)
    (e₂ : commitGen g a₂ + α₂ • U + β₂ • W =
      commitGen g b₂ + α₂' • U + β₂' • W) :
    relationOption (separateOrRelationWitness g U W a₁ b₁ α₁ α₁' β₁ β₁' e₁) =
      relationOption (separateOrRelationWitness g U W a₂ b₂ α₂ α₂' β₂ β₂' e₂) := by
  subst a₂
  subst b₂
  subst α₂
  subst α₂'
  subst β₂
  subst β₂'
  have he : e₂ = e₁ := Subsingleton.elim _ _
  cases he
  rfl

/-- **The total pre-`x` representation source**: the run's pre-`x₁` assembly
commitments over the family's own retained representation list.  No witness, decode, or outcome
is consulted, so the source — and everything the constraint layer builds from it — is defined on
every run. -/
def deployedConstraintSource (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis) :
    List (AlgebraicPoint (F := Fp) basis) :=
  pnu.1.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)

/-- Polynomial of the first online representation of a committed point.  The first matching
representation is selected by the online source's executable list search, and coefficient
conversion is finite arithmetic over `Fp`. -/
def deployedConstraintPointPolynomial
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis) (P : VestaG) : CPoly :=
  onlinePointPolynomial (deployedConstraintSource family basis pnu) P

/-- Coordinates of one quotient-piece commitment from the same deterministic source. -/
def deployedConstraintPieceCoordinates
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (i : Fin shape.numQuotientPieces) : (Fin (2 ^ shape.k) -> Fp) × Fp × Fp :=
  onlinePointCoordinates (deployedConstraintSource family basis pnu)
    (pnu.1.algebraicProof.hPieces i).point

/-- Every quotient piece is covered by the retained pre-`x` source. -/
theorem deployedConstraintPieceCovered
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (i : Fin shape.numQuotientPieces) :
    CommitmentRefCovered (deployedConstraintSource family basis pnu)
      (.point (pnu.1.algebraicProof.hPieces i).point) :=
  ⟨pnu.1.algebraicProof.hPieces i,
    pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource (family.fixedRepresentations basis) i,
    rfl⟩

/-- The online quotient-piece coordinates open the emitted quotient-piece commitment. -/
theorem deployedConstraintPieceCoordinates_open
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (i : Fin shape.numQuotientPieces) :
    commit (ursOfAugmentedBasis shape.k basis)
        (deployedConstraintPieceCoordinates family basis pnu i).1 +
      (deployedConstraintPieceCoordinates family basis pnu i).2.1 •
          (ursOfAugmentedBasis shape.k basis).u +
      (deployedConstraintPieceCoordinates family basis pnu i).2.2 •
          (ursOfAugmentedBasis shape.k basis).w = pnu.1.proof.1.hPieces i := by
  simpa [deployedConstraintPieceCoordinates, deployedConstraintSource] using
    onlinePointCoordinates_commitment
      (deployedConstraintSource family basis pnu)
      (pnu.1.algebraicProof.hPieces i).point
      (deployedConstraintPieceCovered family basis pnu i)

/-- The reassembled quotient MSM is covered directly by the pre-`x` quotient-piece
representations.  This proof does not select a routed member or an opening witness. -/
theorem deployedConstraintVanishingCovered
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis) :
    CommitmentRefCovered (deployedConstraintSource family basis pnu)
      (.msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces))) := by
  intro pr hpr
  have hpoint : pr.2 ∈ (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces)).otherPoints := by
    rw [Msm.otherPoints]
    exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
  have hpiece := mem_otherPoints_vanishingHCommitment
    ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
    (List.ofFn pnu.1.proof.1.hPieces) pr.2 hpoint
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
  refine ⟨pnu.1.algebraicProof.hPieces i,
    pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource (family.fixedRepresentations basis) i, ?_⟩
  change (pnu.1.algebraicProof.hPieces i).point = pr.2 at hi
  exact hi

/-- Quotient-piece representations retained in the online pre-`x` source. -/
def deployedConstraintPieceRepresentations
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      pnu.1.proof.1.hPieces :=
  { coeffs := fun i => (deployedConstraintPieceCoordinates family basis pnu i).1
    uComp := fun i => (deployedConstraintPieceCoordinates family basis pnu i).2.1
    wComp := fun i => (deployedConstraintPieceCoordinates family basis pnu i).2.2
    commitment := deployedConstraintPieceCoordinates_open family basis pnu }

/-- Computed comparison between the online representation of the reassembled quotient MSM and
the power sum of the online quotient-piece representations.  A disagreement returns its actual
augmented-basis coefficients; it is never recovered from an ∃-closed relation or `Nonempty`. -/
def deployedConstraintQuotientAgreementOrRelation
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis) :
    let urs := ursOfAugmentedBasis shape.k basis
    let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
    let represented := coveredCommitmentRepresentation
      (deployedConstraintSource family basis pnu)
      (.msm (vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)))
      (deployedConstraintVanishingCovered family basis pnu)
    let pieces := deployedConstraintPieceRepresentations family basis pnu
    (represented.coeffs = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) • pieces.coeffs i ∧
      represented.uComp = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) * pieces.uComp i ∧
      represented.wComp = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) * pieces.wComp i) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let urs := ursOfAugmentedBasis shape.k basis
  let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
  let msm := vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)
  let represented := coveredCommitmentRepresentation
    (deployedConstraintSource family basis pnu) (.msm msm)
    (deployedConstraintVanishingCovered family basis pnu)
  let pieces := deployedConstraintPieceRepresentations family basis pnu
  let pieceCoeffs := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) • pieces.coeffs i
  let pieceU := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) * pieces.uComp i
  let pieceW := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) * pieces.wComp i
  have hvanishing : msm.eval urs =
      ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i := by
    calc
      _ = ∑ i ∈ Finset.range (List.ofFn pnu.1.proof.1.hPieces).length,
          xn ^ i • (List.ofFn pnu.1.proof.1.hPieces).getD i 0 :=
        vanishingHCommitment_eval urs xn (List.ofFn pnu.1.proof.1.hPieces)
      _ = _ := by
        rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
          List.getElem_ofFn]
  have hrepresented : commit urs represented.coeffs + represented.uComp • urs.u +
      represented.wComp • urs.w =
        ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    represented.commitment.trans hvanishing
  have hpieces : commit urs pieceCoeffs + pieceU • urs.u + pieceW • urs.w =
      ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    pieces.power_commitment xn
  have hcollision : commitGen urs.g represented.coeffs + represented.uComp • urs.u +
      represented.wComp • urs.w =
      commitGen urs.g pieceCoeffs + pieceU • urs.u + pieceW • urs.w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen, hrepresented, hpieces]
  exact separateOrRelationWitness urs.g urs.u urs.w represented.coeffs pieceCoeffs
    represented.uComp pieceU represented.wComp pieceW hcollision

/-- Relation-only projection of the online quotient comparison.  This is the executable finder
charged to DLOG by the composite theorem; success certificates and bad-`x` proofs are deliberately
absent from its input. -/
def deployedConstraintQuotientFinder
    (family : ComputedDeployedRootFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    let pnu := (wrappedAdversary family.toFamily basis).run coins
    match family.outcome basis coins with
    | PSum.inr _ => none
    | PSum.inl _ =>
        match deployedConstraintQuotientAgreementOrRelation family basis pnu with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸ relation)

/-- Representation extraction only reads the list, so equal lists extract equal
representations. -/
private theorem coveredCommitmentRepresentation_list_congr
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {L₁ L₂ : List (AlgebraicPoint (F := Fp) basis)} (hL : L₁ = L₂)
    (c : CommitmentRef shape.k Fp VestaG)
    (h₁ : CommitmentRefCovered L₁ c) (h₂ : CommitmentRefCovered L₂ c) :
    coveredCommitmentRepresentation L₁ c h₁ =
      coveredCommitmentRepresentation L₂ c h₂ := by
  cases hL; rfl

/-- Retained source provenance pins every plain decoded member to its pre-`x` polynomial without a
new relation branch.  The outcome witness's list is identified with the family's by `hsrc`. -/
theorem deployedConstraint_memberPoly_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    {i : Nat} (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (m : Fin (deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length) {P : VestaG}
    (hP : ((deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD (m : Nat) (.point 0, [])).1 =
      .point P) :
    decoded.memberPoly i hi m =
      deployedConstraintPointPolynomial family basis pnu P := by
  unfold DeployedAlgebraicDecode.memberPoly deployedConstraintPointPolynomial
    deployedConstraintSource
  rw [← hsrc]
  rw [hbatches]
  rw [congrFun (witness.memberCoeffs i hi) m]
  exact congrArg coeffsToPoly
    (deployedMemberRepresentationsOfCovered_coeffs_point pnu.1
      witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu)
      i hi m P hP)

/-- At the routed vanishing-quotient slot, the decoded batch retains all three deterministic
online coordinates, not just the polynomial coefficients. -/
theorem deployedConstraint_vanishing_components_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    {i : Nat} (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (m : Fin (deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length)
    (hcommit : ((deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD (m : Nat) (.point 0, [])).1 =
      .msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces))) :
    let represented := coveredCommitmentRepresentation
      (deployedConstraintSource family basis pnu)
      (.msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces)))
      (deployedConstraintVanishingCovered family basis pnu)
    (decoded.batches.x1 i hi).coeffs m = represented.coeffs ∧
      (decoded.batches.x1 i hi).uComp m = represented.uComp ∧
      (decoded.batches.x1 i hi).wComp m = represented.wComp := by
  have hsource : deployedConstraintSource family basis pnu =
      pnu.1.algebraicProof.preX1AssemblySource witness.fixedRepresentations := by
    unfold deployedConstraintSource
    rw [hsrc]
  have hcovW : CommitmentRefCovered
      (pnu.1.algebraicProof.preX1AssemblySource witness.fixedRepresentations)
      (.msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces))) :=
    hsource ▸ deployedConstraintVanishingCovered family basis pnu
  rw [coveredCommitmentRepresentation_list_congr hsource
    (.msm (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces)))
    (deployedConstraintVanishingCovered family basis pnu) hcovW]
  have hmember := deployedMemberRepresentationsOfCovered_components pnu.1
    witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu) i hi m
    (.msm (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces))) hcommit hcovW
  refine ⟨?_, ?_, ?_⟩
  · rw [hbatches]
    exact (congrFun (witness.memberCoeffs i hi) m).trans hmember.1
  · rw [hbatches]
    exact (congrFun (witness.memberU i hi) m).trans hmember.2.1
  · rw [hbatches]
    exact (congrFun (witness.memberW i hi) m).trans hmember.2.2

/-- Any quotient relation returned by the decoded constraint adapter is the same relation returned
by the standalone online quotient comparison.  This is the bridge that lets the probability layer
charge the relation-only executable finder rather than the success-certificate provider. -/
theorem deployedConstraint_quotient_relation_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    {i : Nat} (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (m : Fin (deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length)
    (hcommit : ∀ d₀, ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD
        (m : Nat) d₀).1 = .msm (vanishingHCommitment shape.k
          ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
          (List.ofFn pnu.1.proof.1.hPieces)))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hrelation : decoded.quotientEvalEqCommittedPreXOrRelationWitness
      (fun j => (deployedConstraintPieceCoordinates family basis pnu j).1)
      (fun j => (deployedConstraintPieceCoordinates family basis pnu j).2.1)
      (fun j => (deployedConstraintPieceCoordinates family basis pnu j).2.2)
      (fun j => coeffsToPoly
        (deployedConstraintPieceCoordinates family basis pnu j).1)
      (deployedConstraintPieceCoordinates_open family basis pnu) (fun _ => rfl)
      hi m hcommit = PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis pnu =
      PSum.inr relation := by
  have hcomponents := deployedConstraint_vanishing_components_eq_online family basis pnu witness
    hsrc decoded hbatches hi m (hcommit (.point 0, []))
  unfold DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness at hrelation
  unfold decodedQuotientEqReassembledOrRelationWitness at hrelation
  simp only at hrelation
  split at hrelation
  · rename_i innerOutcome quotientRelation hinner
    have hreln : quotientRelation = relation := PSum.inr.inj hrelation
    split at hinner
    · rename_i separateRelation hseparate
      have hinnerRel : separateRelation = quotientRelation := PSum.inr.inj hinner
      unfold deployedConstraintQuotientAgreementOrRelation
      simp only
      apply eq_inr_of_relationOption_eq_some
      have hseparate' := congrArg relationOption hseparate
      simp only [relationOption] at hseparate'
      rw [hinnerRel, hreln] at hseparate'
      calc
        _ = relationOption (separateOrRelationWitness
            (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u
            (ursOfAugmentedBasis shape.k basis).w
            ((decoded.batches.x1 i hi).coeffs m)
            (∑ j : Fin shape.numQuotientPieces,
              ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n) ^ (j : Nat) •
                (deployedConstraintPieceCoordinates family basis pnu j).1)
            ((decoded.batches.x1 i hi).uComp m)
            (∑ j : Fin shape.numQuotientPieces,
              ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n) ^ (j : Nat) *
                (deployedConstraintPieceCoordinates family basis pnu j).2.1)
            ((decoded.batches.x1 i hi).wComp m)
            (∑ j : Fin shape.numQuotientPieces,
              ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n) ^ (j : Nat) *
                (deployedConstraintPieceCoordinates family basis pnu j).2.2) _) := by
              apply relationOption_separateOrRelationWitness_congr
              · exact hcomponents.1.symm
              · rfl
              · exact hcomponents.2.1.symm
              · rfl
              · exact hcomponents.2.2.symm
              · rfl
        _ = some relation := hseparate'
    · cases hinner
  · cases hrelation

/-- Executable polynomial-witness adapter built from the actual online AGM source.  No arbitrary
opening is chosen: its relation branch agrees with the separately executable
`deployedConstraintQuotientFinder`, and its polynomial branch is finite arithmetic over `Fp`. -/
def deployedOnlineConstraintOutcomeOfDecode
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    (checks : DeployedConstraintChecks (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (hAdvLen : shape.numAdviceQueries <= (family.vk basis).adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries <= (family.vk basis).instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries <= (family.vk basis).fixedQueryLayout.length)
    (homega : (family.vk basis).omega ^ (family.vk basis).n = 1)
    (hn : ((family.vk basis).n : Fp) ≠ 0)
    (hxgood : (wrappedPreIpaRecord pnu).x ∉ szBadSet
      (committedPreXConstraintDifference
        (deployedConstraintPointPolynomial family basis pnu)
        (fun i => coeffsToPoly
          (deployedConstraintPieceCoordinates family basis pnu i).1)
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu))) :
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w :=
  deployedConstraintOutcomeOfDecode (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu) decoded
    (deployedConstraintPointPolynomial family basis pnu)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu i).1)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu i).2.1)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu i).2.2)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family basis pnu i).1)
    (deployedConstraintPieceCoordinates_open family basis pnu) (fun _ => rfl)
    (deployedConstraint_memberPoly_eq_online family basis pnu witness hsrc decoded hbatches)
    checks hAdvLen hInstLen hFixedLen homega hn hxgood

/-- Project any relation branch of the full constraint outcome onto the standalone online
quotient comparison. -/
theorem deployedOnlineConstraintOutcome_relation_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    (checks : DeployedConstraintChecks (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (hAdvLen : shape.numAdviceQueries <= (family.vk basis).adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries <= (family.vk basis).instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries <= (family.vk basis).fixedQueryLayout.length)
    (homega : (family.vk basis).omega ^ (family.vk basis).n = 1)
    (hn : ((family.vk basis).n : Fp) ≠ 0)
    (hxgood : (wrappedPreIpaRecord pnu).x ∉ szBadSet
      (committedPreXConstraintDifference
        (deployedConstraintPointPolynomial family basis pnu)
        (fun i => coeffsToPoly
          (deployedConstraintPieceCoordinates family basis pnu i).1)
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu)))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hout : deployedOnlineConstraintOutcomeOfDecode family basis pnu witness hsrc decoded
      hbatches checks hAdvLen hInstLen hFixedLen homega hn hxgood = PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis pnu =
      PSum.inr relation := by
  simp only [deployedOnlineConstraintOutcomeOfDecode, deployedConstraintOutcomeOfDecode,
    bindOrRelationWitness] at hout
  split at hout
  · simp_all only [reduceCtorEq]
  · rename_i quotientRelation hquotient
    have honline := deployedConstraint_quotient_relation_eq_online family basis pnu witness
      hsrc decoded hbatches _ _ _ quotientRelation hquotient
    injection hout with hreln
    exact hreln ▸ honline

/-- Run-level provider shape consumed by the composite probability theorem.  `none` means the
decode or pre-`x` premises were unavailable; `some` retains either the constraint witness or the
explicit relation produced by the online adapter. -/
abbrev DeployedConstraintOutcomeProvider (family : ComputedDeployedRootFSFamily shape) :=
  forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins),
    let pnu := (wrappedAdversary family.toFamily basis).run coins
    Option (DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)

/-- Explicit algebraic relation finder induced by the right branch of a constraint provider. -/
def deployedConstraintFinderOfOutcome (family : ComputedDeployedRootFSFamily shape)
    (provider : DeployedConstraintOutcomeProvider family) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match provider basis coins with
    | some (PSum.inr relation) =>
        some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸ relation)
    | _ => none


end Zcash.Snark
