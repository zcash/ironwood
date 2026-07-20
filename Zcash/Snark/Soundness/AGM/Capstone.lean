import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.Forking.Rewind

/-!
# Deployed AGM opening or relation

`Soundness.AGM.Peel` computes a relation from algebraic prover data. This module connects that result
to the deployed opening. The result is either a multiopen IPA opening or an explicit relation, with
no `Classical.choice`.

## The boundary with the Fiat–Shamir/forking layer

Once the transcript and its representations are supplied, both result branches are computed data.
The Fiat–Shamir/forking layer must provide those inputs and connect its acceptance probability to
this execution. `deployedAlgebraicRelationWitness` returns the relation type used by the DL proof.

The vectors in `hP` use only `g`. Real halo2 commitments are blinded, so the Vesta endpoints first
remove their declared `U` and `W` components. The algebraic prover supplies representations of those
adjusted points.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute a deployed IPA opening or relation from an algebraic fork certificate.

Erasing the coefficients gives the certificate checked by `DeployedForkValid`. The relation branch
uses the form expected by the fixed-slot DL reduction. -/
def deployedAlgebraicForkingRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployed_forking_relation urs b v ξ z blind aMulti aDep s cert.toDForkCert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel =>
      PSum.inr (AugmentedRelationWitness.toAlgebraicRelationWitness hrel)

/-- Run the deployed certificate and then the fixed-slot DL reduction.

The result is an IPA opening, a DL solution, or proof that the returned relation missed the fixed
challenge slot. -/
def deployedAlgebraicForkingFixedSlot [DecidableEq G] [Inhabited G] (urs : URS G)
    (B : G) (challenge : AugmentedIndex (2 ^ urs.k))
    (embedding : FixedSlotEmbedding (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' FixedSlotRelationOutcome (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge :=
  match deployedAlgebraicForkingRelation urs b v ξ z blind aMulti aDep s cert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel => PSum.inr (fixedSlotExtractOrMiss B _ challenge embedding hrel)

/-! ## Concrete relation producer for the probability experiment -/

/-- Inputs needed to run the deployed algebraic kernel on one augmented public basis.

The basis determines the URS through `ursOfAugmentedBasis`, so the instance cannot use unrelated
generators. -/
structure DeployedAlgebraicForkingInstance (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) where
  b : Fin (2 ^ k) → Fp
  v : Fp
  ξ : Fp
  z : Fp
  blind : Fp
  aMulti : Fin (2 ^ k) → Fp
  aDep : Fin (2 ^ k) → Fp
  s : Fin (2 ^ k) → Fp
  cert : AlgebraicDForkCert (F := Fp)
    (augmentedBasis (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w) k
  hz : z ≠ 0
  hb0 : b 0 = 1
  hP : commit (ursOfAugmentedBasis k basis) aDep =
    commit (ursOfAugmentedBasis k basis) aMulti - v • (ursOfAugmentedBasis k basis).g 0 +
      ξ • commit (ursOfAugmentedBasis k basis) s
  hvalid : DeployedForkValid (ursOfAugmentedBasis k basis).g b
    (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w z
    (commit (ursOfAugmentedBasis k basis) aDep + (z * 0) • (ursOfAugmentedBasis k basis).u +
      blind • (ursOfAugmentedBasis k basis).w) cert.toDForkCert

namespace DeployedAlgebraicForkingInstance

/-- The opening branch produced by one deployed algebraic instance. -/
abbrev Opening {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Type _ :=
  Σ' a, IpaRelation (ursOfAugmentedBasis k basis)
    (commit (ursOfAugmentedBasis k basis) x.aMulti) x.b
    (x.v - x.ξ * innerProduct x.s x.b) a

/-- Run one deployed instance and return its opening or relation on the supplied basis. -/
def run [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) :
    x.Opening ⊕' AlgebraicRelationWitness (F := Fp) basis := by
  letI : Inhabited G := ⟨0⟩
  cases deployedAlgebraicForkingRelation (ursOfAugmentedBasis k basis) x.b x.v x.ξ x.z
      x.blind x.aMulti x.aDep x.s x.cert x.hz x.hb0 x.hP x.hvalid with
  | inl hopen => exact PSum.inl hopen
  | inr hrel =>
      rw [augmentedBasis_ursOfAugmentedBasis] at hrel
      exact PSum.inr hrel

/-- Whether running this instance returns the relation branch. -/
def ProducesRelation [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Prop :=
  ∃ r, x.run = PSum.inr r

end DeployedAlgebraicForkingInstance

/-- Whether the supplied instance for this basis exists and returns a relation. -/
def deployedAlgebraicRelationProduced [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) : Prop :=
  ∃ x, instances basis = some x ∧ x.ProducesRelation

/-- Bases on which the supplied instance computes a relation. -/
def deployedAlgebraicRelationEvent [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    Set (AugmentedIndex (2 ^ k) → G) :=
  { basis | deployedAlgebraicRelationProduced instances basis }

/-- The relation finder used by the probability proof.

It runs the supplied instance for each basis and returns only its computed relation branch. Missing
instances and valid openings return `none`. -/
def deployedAlgebraicRelationFinder [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    (basis : AugmentedIndex (2 ^ k) → G) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis =>
    match instances basis with
    | none => none
    | some x =>
      match x.run with
      | PSum.inl _ => none
      | PSum.inr hrel => some hrel

/-- The finder succeeds exactly when the supplied instance returns a relation. -/
theorem deployedAlgebraicRelationFinder_isSome_iff [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) :
    (deployedAlgebraicRelationFinder instances basis).isSome ↔
      deployedAlgebraicRelationProduced instances basis := by
  unfold deployedAlgebraicRelationProduced deployedAlgebraicRelationFinder
  cases hinst : instances basis with
  | none => simp
  | some x =>
    cases hrun : x.run with
    | inl hopen => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]
    | inr hrel => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]

/-- Compute an IPA opening or explicit relation from an accepting deployed algebraic tree. -/
def deployedAlgebraicRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  cases deployedToAcceptVWitness hz urs.g b (commit urs aDep) 0 blind t ht with
  | inl hclean =>
    obtain ⟨a, ha⟩ := ipaRelation_extract urs b (commit urs aDep) 0 (projTree t) hclean
    have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
      (by rw [add_sub_cancel_right]; exact ha)
    have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
      rw [hP]; abel
    rw [h2] at h1
    exact PSum.inl ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _ h1⟩
  | inr hrel => exact PSum.inr hrel

/-- As `deployedAlgebraicRelation`, with the relation converted for the probability proof. -/
def deployedAlgebraicRelationWitness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployedAlgebraicRelation urs b v ξ z blind aMulti aDep s t hz hb0 hP ht with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
