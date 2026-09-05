import Zcash.Snark.Soundness.Composition.StraightLineDeployed
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# Straight-line AGM composition through the deployed constraint relation

This module lifts the one-table straight-line IPA/root extractor through the online constraint
adapter.  Every branch of the relation finder reads a single accepting execution and rewinds
nothing.
-/

namespace Zcash.Snark

open Classical
open scoped ENNReal

local instance vestaInhabitedStraightLineConstraint : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedConstraintDifferencePreX

variable {shape : Shape}

namespace ComputedStraightLineDeployedFSFamily

/-- A data-wrapped equality certificate whose check is executable whenever equality is. -/
def equalityCertificate? {A : Type*} [DecidableEq A] (x y : A) : Option (PLift (x = y)) :=
  if h : x = y then some ⟨h⟩ else none

theorem algebraicPoint_eq_of_point_coeffs {k : Nat}
    {basis : AugmentedIndex (2 ^ k) → VestaG}
    (P Q : AlgebraicPoint (F := Fp) basis)
    (hpoint : P.point = Q.point) (hcoeffs : P.coeffs = Q.coeffs) : P = Q := by
  cases P with
  | mk pointP reprP =>
    cases Q with
    | mk pointQ reprQ =>
      dsimp only [AlgebraicPoint.point] at hpoint
      subst pointQ
      cases reprP with
      | mk coeffsP eqP =>
        cases reprQ with
        | mk coeffsQ eqQ =>
          dsimp only [AlgebraicPoint.coeffs, GroupRepresentation.coeffs] at hcoeffs
          subst coeffsQ
          rfl

/-- Executable equality for AGM points: compare the point and the finite coefficient vector;
the representation equation is a proof field and is therefore irrelevant to equality. -/
def algebraicPointDecidableEq {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG) :
    DecidableEq (AlgebraicPoint (F := Fp) basis) := fun P Q =>
  if hpoint : P.point = Q.point then
    if hcoeffs : P.coeffs = Q.coeffs then
      isTrue (algebraicPoint_eq_of_point_coeffs P Q hpoint hcoeffs)
    else isFalse fun h => hcoeffs (congrArg AlgebraicPoint.coeffs h)
  else isFalse fun h => hpoint (congrArg AlgebraicPoint.point h)

def fixedRepresentationsEqualityCertificate? {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (xs ys : List (AlgebraicPoint (F := Fp) basis)) : Option (PLift (xs = ys)) :=
  letI := algebraicPointDecidableEq basis
  equalityCertificate? xs ys

/-- The total pre-`x` constraint difference on a straight-line oracle table. This is the same
polynomial as `deployedConstraintDifferencePreX`, evaluated directly from the represented
execution. -/
def straightLineConstraintDifferencePreX
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : CPoly :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  committedPreXConstraintDifference
    (deployedConstraintPointPolynomial family.toRootFamily basis pnu)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family.toRootFamily basis pnu i).1)
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)

set_option maxHeartbeats 800000 in
/-- Reconstruct a deployed decode by checking the finite equations carried by a computed batch
outcome.  This deliberately checks the data fields themselves instead of selecting a proof-only
`DeployedRootDecodeWitness`: if the equations hold, the returned decode contains exactly the
batch coordinates emitted by `family.outcome`. -/
def straightLineDecodeOfOutcome?
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) :
    Option { decoded : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (wrappedPreIpaRecord ((wrappedAdversary family.toFamily basis).run O))
      (((wrappedAdversary family.toFamily basis).run O).1.aMulti
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O)))
      (((wrappedAdversary family.toFamily basis).run O).1.multiU
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O)))
      (((wrappedAdversary family.toFamily basis).run O).1.multiBlind
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))) //
      decoded.batches = witness.batches } := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  let x4Check := fun j : Fin (deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch + 1) =>
    equalityCertificate?
      (commitGen (evalVector shape.k ch.x3) (witness.batches.x4.coeffs j))
      (x4BatchEvals (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch j)
  match finForallOption x4Check with
  | none => exact none
  | some hx4Values =>
      let memberCheck := fun i : Fin (deployedX4PairCount (family.vk basis)
          (family.instanceCommitment basis) pnu.1.proof.1 ch) =>
        let points := ((deployedSetsForEval (family.vk basis)
          (family.instanceCommitment basis) pnu.1.proof.1 ch).getD
            i.1 ([], [], 0)).1
        let queries := deployedSetQueries (family.vk basis)
          (family.instanceCommitment basis) pnu.1.proof.1 ch i.1
        finForallOption (fun idx : Fin points.length =>
          finForallOption (fun m : Fin queries.length => equalityCertificate?
            ((coeffsToPoly ((witness.batches.x1 i.1 i.2).coeffs m)).eval points[idx])
            ((queries.getD (m : Nat) (.point 0, [])).2.getD (idx : Nat) 0)))
      match finForallOption memberCheck with
      | none => exact none
      | some hmemberValues => exact some ⟨
          ⟨witness.batches,
            (fun j => (hx4Values j).down),
            (fun i hi idx m => (hmemberValues ⟨i, hi⟩ idx m).down)⟩,
          rfl⟩

/-- Executable acceptance certificate for the exact run consumed by the constraint adapter. -/
def straightLineAccepts?
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    let pnu := (wrappedAdversary family.toFamily basis).run O
    Option (PLift (DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)))) := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let fullCh := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
  match hassemble : assemble? (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 fullCh with
  | none => exact none
  | some msm =>
      if hzero : msm.eval (ursOfAugmentedBasis shape.k basis) = 0 then
        exact some ⟨by
          unfold DeployedAccepts
          rw [hassemble]
          exact hzero⟩
      else exact none

theorem straightLineAccepts?_isSome_of
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (haccepts : let pnu := (wrappedAdversary family.toFamily basis).run O
      DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))) :
    (family.straightLineAccepts? basis O).isSome := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let fullCh := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
  change DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 fullCh at haccepts
  unfold DeployedAccepts at haccepts
  unfold straightLineAccepts?
  dsimp only
  split
  · rename_i hassemble
    rw [hassemble] at haccepts
    exact False.elim haccepts
  · rename_i msm hassemble
    rw [hassemble] at haccepts
    simp [haccepts]

/-- Successful computed constraint data, paired with the deployed acceptance proof checked on the
same run and its complete IPA-round record. -/
structure StraightLineConstraintSuccess
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) where
  witness : let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu))
  accepts : let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))

/-- Total executable constraint adapter for one straight-line run.  It consumes only the run,
the family's computed batch outcome, finite equation checks, deployed acceptance, and the total
pre-`x` difference.  No `Nonempty`, `Classical.choice`, recursive tape, or imported fixture is on
the returned-data path. -/
def straightLineConstraintOutcome?
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    let _pnu := (wrappedAdversary family.toFamily basis).run O
    Option (StraightLineConstraintSuccess family basis O ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w) := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  let fullCh := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
  match family.outcome basis O with
  | PSum.inr relation => exact some (PSum.inr relation)
  | PSum.inl witness =>
      match fixedRepresentationsEqualityCertificate? basis witness.fixedRepresentations
          (family.fixedRepresentations basis) with
      | none => exact none
      | some hsource =>
        match family.straightLineDecodeOfOutcome? basis O witness with
        | none => exact none
        | some decoded =>
          match family.straightLineAccepts? basis O with
          | none => exact none
          | some hacceptsProof =>
            let haccepts := hacceptsProof.down
            let checks := DeployedConstraintChecks.of_accepts_chRecord
              (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1
              (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O) haccepts
            match hxgood : szBadSetAvoidance?
                (family.straightLineConstraintDifferencePreX basis O) ch.x with
            | some hxgoodProof =>
              match deployedOnlineConstraintOutcomeOfDecode family.toRootFamily basis pnu
                  witness hsource.down decoded.1 decoded.2
                  checks (static.adviceLength basis) (static.instanceLength basis)
                  (static.fixedLength basis) (static.omegaOrder basis)
                  (static.characteristic basis) hxgoodProof.down with
              | PSum.inl constraint => exact some (PSum.inl
                  { witness := constraint, accepts := haccepts })
              | PSum.inr relation => exact some (PSum.inr relation)
            | none => exact none

/-- Successful constraint witness projected as data from the total straight-line adapter. -/
def straightLineConstraintSuccess?
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :=
  match family.straightLineConstraintOutcome? static basis O with
  | some (PSum.inl witness) => some witness
  | _ => none

/-- Relation-only projection of the existing online quotient comparison on the one-run table. -/
def straightLineConstraintQuotientFinder
    (family : ComputedStraightLineDeployedFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let pnu := (wrappedAdversary family.toFamily basis).run O
    match family.outcome basis O with
    | PSum.inr _ => none
    | PSum.inl _ =>
        match deployedConstraintQuotientAgreementOrRelation
            family.toRootFamily basis pnu with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸ relation)

/-- Complete straight-line relation finder: IPA, deployed unbatching, then quotient collision.
Every branch returns explicit relation coefficients and no branch rewinds the adversary. -/
def straightLineConstraintRelationFinder
    (family : ComputedStraightLineDeployedFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.straightLineDeployedRelationFinder basis O with
    | some relation => some relation
    | none => family.straightLineConstraintQuotientFinder basis O

/-- Modeled black-box invocations of the straight-line combined finder.  The IPA branch costs one
run.  If it returns no relation, the direct-coordinate outcome costs one more; on its witness
branch the quotient comparison repeats the wrapped output and outcome, for a worst case of four.
Algebraic postprocessing and group work are accounted for separately by the finite-security
profile. -/
def straightLineConstraintRelationFinderCalls
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Nat :=
  match family.toIpaFamily.straightLineIpaRelationFinder basis O with
  | some _ => 1
  | none =>
      match family.outcome basis O with
      | PSum.inr _ => 2
      | PSum.inl _ => 4

/-- The new combined finder has a pointwise four-invocation bound — independent of the field, `k`,
and the adversary's success distribution. -/
theorem straightLineConstraintRelationFinderCalls_le_four
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    family.straightLineConstraintRelationFinderCalls basis O <= 4 := by
  unfold straightLineConstraintRelationFinderCalls
  cases hipa : family.toIpaFamily.straightLineIpaRelationFinder basis O
  · cases hout : family.outcome basis O <;> simp
  · simp

/-- Fixed-call hardness for the straight-line finder is exactly ordinary hardness plus the proved
pointwise call budget; no truncation or expected-time conversion is needed. -/
theorem straightLineConstraint_fixedCalls_iff
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal} :
    TextbookDLWithCoinsFixedCallsAdvantageLE B
        family.straightLineConstraintRelationFinder
        family.straightLineConstraintRelationFinderCalls 4 bound <->
      TextbookDLWithCoinsAdvantageLE B
        family.straightLineConstraintRelationFinder bound := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨family.straightLineConstraintRelationFinderCalls_le_four, h⟩

/-- The computed constraint decode on one oracle table.  The proposition is merely the `isSome`
view of `straightLineConstraintSuccess?`; consumers recover the exact retained success data with
`Option.get`, never with `Classical.choice`. -/
def straightLineConstraintDecoded
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Prop :=
  (family.straightLineConstraintSuccess? static basis O).isSome

/-- A decoded run exposes the exact successful branch of the executable outcome. -/
theorem straightLineConstraintOutcome?_eq_some_of_decoded
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    ∃ success, family.straightLineConstraintOutcome? static basis O =
      some (PSum.inl success) := by
  unfold straightLineConstraintDecoded straightLineConstraintSuccess? at hdecoded
  cases hout : family.straightLineConstraintOutcome? static basis O with
  | none => simp [hout] at hdecoded
  | some outcome =>
      cases outcome with
      | inl success => exact ⟨success, rfl⟩
      | inr relation => simp [hout] at hdecoded

/-- The `Option.get` success is the same value exposed by the outcome branch. -/
theorem straightLineConstraintSuccess_eq_of_outcome
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (success : StraightLineConstraintSuccess family basis O)
    (hout : family.straightLineConstraintOutcome? static basis O =
      some (PSum.inl success)) :
    (family.straightLineConstraintSuccess? static basis O).get hdecoded = success := by
  simp [straightLineConstraintSuccess?, hout]

set_option maxHeartbeats 800000 in
/-- The root-containment construction lands in the same computed success option. This bridges the
root-event probability decomposition to the value returned by `straightLineConstraintOutcome?`. -/
theorem straightLineConstraintDecoded_of_root
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O)
    (root : DeployedRootDecodeWitness family.toRootFamily basis O)
    (hxgood : (wrappedPreIpaRecord
        (deployedRootRunOutput family.toRootFamily basis O)).x ∉
      szBadSet (deployedConstraintDifferencePreX family.toRootFamily basis
        O))
    (constraint : DeployedConstraintWitness
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis)
      (deployedRootRunOutput family.toRootFamily basis
        O).1.proof.1
      (wrappedPreIpaRecord (deployedRootRunOutput family.toRootFamily basis
        O))
      ((deployedRootRunOutput family.toRootFamily basis
        O).1.aMulti
          (wrappedPreIpaReads (deployedRootRunOutput family.toRootFamily basis
            O)))
      ((deployedRootRunOutput family.toRootFamily basis
        O).1.multiU
          (wrappedPreIpaReads (deployedRootRunOutput family.toRootFamily basis
            O)))
      ((deployedRootRunOutput family.toRootFamily basis
        O).1.multiBlind
          (wrappedPreIpaReads (deployedRootRunOutput family.toRootFamily basis
            O))))
    (hout : deployedConstraintOutcomeOfRoot family.toRootFamily static basis
      O haccept root hxgood = PSum.inl constraint) :
    family.straightLineConstraintDecoded static basis O := by
  rcases root with ⟨batchWitness, outcome_eq, decoded, batches_eq⟩
  cases decoded with
  | mk batches x4Values memberValues =>
      dsimp only [DeployedAlgebraicDecode.batches] at batches_eq
      cases batches_eq
      have hdecode : family.straightLineDecodeOfOutcome? basis O batchWitness =
          some ⟨⟨batchWitness.batches, x4Values, memberValues⟩, rfl⟩ := by
        let pnu := (wrappedAdversary family.toFamily basis).run O
        let ch := wrappedPreIpaRecord pnu
        let x4Check := fun j : Fin (deployedX4PairCount (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch + 1) =>
          equalityCertificate?
            (commitGen (evalVector shape.k ch.x3) (batchWitness.batches.x4.coeffs j))
            (x4BatchEvals (family.vk basis) (family.instanceCommitment basis)
              pnu.1.proof.1 ch j)
        have hx4Some : (finForallOption x4Check).isSome :=
          finForallOption_isSome_of _ fun j => by
            simp [x4Check, equalityCertificate?]
            simpa using x4Values j
        obtain ⟨hx4Certificates, hx4Eq⟩ := Option.isSome_iff_exists.mp hx4Some
        let memberCheck := fun i : Fin (deployedX4PairCount (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch) =>
          let points := ((deployedSetsForEval (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch).getD
              i.1 ([], [], 0)).1
          let queries := deployedSetQueries (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch i.1
          finForallOption (fun idx : Fin points.length =>
            finForallOption (fun m : Fin queries.length => equalityCertificate?
              ((coeffsToPoly ((batchWitness.batches.x1 i.1 i.2).coeffs m)).eval points[idx])
              ((queries.getD (m : Nat) (.point 0, [])).2.getD (idx : Nat) 0)))
        have hmemberSome : (finForallOption memberCheck).isSome :=
          finForallOption_isSome_of _ fun i =>
            finForallOption_isSome_of _ fun idx =>
              finForallOption_isSome_of _ fun m => by
                simp [equalityCertificate?]
                simpa [pnu, ch, deployedRootRunOutput] using
                  memberValues i.1 i.2 idx m
        obtain ⟨memberCertificates, hmemberEq⟩ :=
          Option.isSome_iff_exists.mp hmemberSome
        simp only [straightLineDecodeOfOutcome?]
        rw [hx4Eq, hmemberEq]
      have haccepts := deployedAccepts_of_fsWinsFull family.toFamily basis O haccept
      have haccepts' : let pnu := (wrappedAdversary family.toFamily basis).run O
          DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
            (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
            (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) := by
        simpa [runProof, runRecord, wrappedAdversary_run_fst, wrappedPreIpaReads_run]
          using haccepts
      have hacceptsSome := family.straightLineAccepts?_isSome_of basis O haccepts'
      obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
      have hxgood' : (wrappedPreIpaRecord
          ((wrappedAdversary family.toFamily basis).run O)).x ∉
          szBadSet (family.straightLineConstraintDifferencePreX basis O) := by
        simpa [straightLineConstraintDifferencePreX, deployedConstraintDifferencePreX,
          deployedRootRunOutput] using hxgood
      have hxgoodSome : (szBadSetAvoidance?
          (family.straightLineConstraintDifferencePreX basis O)
          (wrappedPreIpaRecord
            ((wrappedAdversary family.toFamily basis).run O)).x).isSome :=
        (szBadSetAvoidance?_isSome_iff _ _).2 hxgood'
      obtain ⟨hxgoodProof, hxgoodEq⟩ := Option.isSome_iff_exists.mp hxgoodSome
      have hxgoodEq' := hxgoodEq
      simp only [straightLineConstraintDifferencePreX] at hxgoodEq'
      have outcome_eq' : family.outcome basis O = PSum.inl batchWitness := by
        simpa [deployedRootRunOutput] using outcome_eq
      have hsource := family.outcome_source basis O batchWitness outcome_eq'
      have hsourceSome : (fixedRepresentationsEqualityCertificate? basis
          batchWitness.fixedRepresentations (family.fixedRepresentations basis)).isSome := by
        simp [fixedRepresentationsEqualityCertificate?, equalityCertificate?, hsource]
      obtain ⟨hsourceProof, hsourceEq⟩ := Option.isSome_iff_exists.mp hsourceSome
      have hout' := hout
      simp only [deployedConstraintOutcomeOfRoot] at hout'
      unfold straightLineConstraintDecoded straightLineConstraintSuccess?
      unfold straightLineConstraintOutcome?
      simp +zetaDelta only [outcome_eq']
      simp +zetaDelta only [hsourceEq]
      simp +zetaDelta only [hdecode]
      simp +zetaDelta only [hacceptsEq]
      rw [hxgoodEq]
      simp [deployedRootRunOutput, hout']

/-- Basis/oracle pairs on which the one-run endpoint accepts but does not return the concrete
constraint witness. -/
def straightLineConstraintFailureEvent
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    ¬family.straightLineConstraintDecoded static q.1 q.2}

/-- Basis/oracle pairs on which an arbitrary executable relation finder returns data. -/
def straightLineRelationEvent
    (family : ComputedStraightLineDeployedFSFamily shape)
    (finder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | (finder q.1 q.2).isSome}

/-- Scalar-basis form used by the textbook-DLOG reduction. -/
def straightLineConstraintFailureSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  (fun q => (scalarBasis B q.1, q.2)) ⁻¹'
    family.straightLineConstraintFailureEvent static

/-- Transfer the complete straight-line failure event across a uniform-URS identification. -/
theorem straightLineConstraintFailure_prob_eq_of_uniformURS
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
          (BTranscript Fp VestaG
            (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) := by
  let oraclePMF := PMF.uniformOfFintype
    (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          oraclePMF := congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) =>
      p.toOuterMeasure (family.straightLineConstraintFailureEvent static)) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure
        (family.straightLineConstraintFailureEvent static) =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          (family.straightLineConstraintFailureEvent static) at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
            family.straightLineConstraintFailureEvent static) := hmeasure
    _ = _ := by
      rw [independentProductPMF_uniform]
      rfl

/-- Uniform-URS transfer for the union of compressed failure and one executable relation event.
Keeping the union intact is what lets a downstream semantic capstone charge a combined finder
only once. -/
theorem straightLineConstraintFailure_union_relation_prob_eq_of_uniformURS
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (finder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent finder)) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
          (BTranscript Fp VestaG
            (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static ∪ relSetWithCoins B finder) := by
  let oraclePMF := PMF.uniformOfFintype
    (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          oraclePMF := congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) =>
      p.toOuterMeasure (family.straightLineConstraintFailureEvent static ∪
        family.straightLineRelationEvent finder)) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure _ =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure _ at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
            (family.straightLineConstraintFailureEvent static ∪
              family.straightLineRelationEvent finder)) := hmeasure
    _ = _ := by
      rw [independentProductPMF_uniform]
      have hsets :
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
              (family.straightLineConstraintFailureEvent static ∪
                family.straightLineRelationEvent finder)) =
            family.straightLineConstraintFailureSet B static ∪
              relSetWithCoins B finder := by
        ext q
        simp [straightLineConstraintFailureSet, straightLineRelationEvent, relSetWithCoins]
      rw [hsets]

/-- The exact pre-`x` bad event, restricted to the fixed proof-only tape used by the straight-line
decode. -/
def straightLineConstraintBadXSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | (scalarBasis B q.1, q.2) ∈
    deployedConstraintBadXEvent family.toRootFamily}

/-- Deterministic straight-line constraint containment.  Failure is covered by the root-layer
zero and pinned-root events, the one combined relation finder, or the single constraint-`x` root.
-/
theorem straightLineConstraintFailureSet_subset
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    family.straightLineConstraintFailureSet B static <=
      family.straightLineRootZeroSet B ∪
        ({q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2} ∪
          ({q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2} ∪
            ((relSetWithCoins B family.straightLineConstraintRelationFinder :
                Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
                  (BTranscript Fp VestaG
                    (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))) ∪
              family.straightLineConstraintBadXSet B))) := by
  intro q hfailure
  let basis := scalarBasis B q.1
  let coins : family.toFamily.Coins := q.2
  by_cases hroot : family.straightLineRootDecoded basis q.2
  · let root := Classical.choice hroot
    by_cases hxgood : (wrappedPreIpaRecord
        (deployedRootRunOutput family.toRootFamily basis coins)).x ∉
        szBadSet (deployedConstraintDifferencePreX family.toRootFamily basis coins)
    · cases hout : deployedConstraintOutcomeOfRoot family.toRootFamily static basis coins
          hfailure.1 root hxgood with
      | inl witness =>
          exfalso
          apply hfailure.2
          exact family.straightLineConstraintDecoded_of_root static basis q.2
            hfailure.1 root hxgood witness hout
      | inr relation =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inl
          simp only [relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
            true_and]
          unfold straightLineConstraintRelationFinder
          cases hbase : family.straightLineDeployedRelationFinder basis q.2 with
          | some baseRelation => simp
          | none =>
              have hrelation := deployedConstraintOutcomeOfRoot_relation_eq_online
                family.toRootFamily static basis coins hfailure.1 root hxgood relation hout
              -- Restate both equations with the `let`s expanded so `simp` can use them.
              have houtcome : family.outcome (scalarBasis B q.1) q.2 =
                PSum.inl root.batchWitness := root.outcome_eq
              have hrel : deployedConstraintQuotientAgreementOrRelation family.toRootFamily
                  (scalarBasis B q.1)
                  ((wrappedAdversary family.toFamily (scalarBasis B q.1)).run q.2) =
                  PSum.inr relation := hrelation
              simp [straightLineConstraintQuotientFinder, houtcome, hrel]
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      change (wrappedPreIpaRecord
          (deployedRootRunOutput family.toRootFamily basis coins)).x ∈
        szBadSet (deployedConstraintDifferencePreX family.toRootFamily basis coins)
      exact Classical.not_not.mp hxgood
  · by_cases hrelation :
        (family.straightLineDeployedRelationFinder basis q.2).isSome
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      simp only [relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold straightLineConstraintRelationFinder
      cases hbase : family.straightLineDeployedRelationFinder basis q.2 with
      | none => simp [hbase] at hrelation
      | some relation => simp
    · have hnotExtracted : ¬family.straightLineRootExtracted basis q.2 := by
        rintro (hfound | hdecoded)
        · exact hrelation hfound
        · exact hroot hdecoded
      have hplain : fsWinsFull (family.adversary basis)
          (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 := by
        exact fullAlgebraicAccept_of_deployed basis (family.vk basis)
          (family.instanceCommitment basis) ((family.adversary basis).run q.2) _ _ hfailure.1
      rcases family.straightLineRootFailure basis q.2 hplain hnotExtracted with
        hzero | hipa | hdeployed
      · exact Or.inl ⟨hplain, hzero⟩
      · exact Or.inr (Or.inl hipa)
      · exact Or.inr (Or.inr (Or.inl hdeployed))

/-- The constraint-`x` slice retains the direct `(Q+1) * epsilonX` pinned-squeeze price. -/
theorem straightLineConstraintBadX_prob_le
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintBadXSet B) <=
      (family.Q + 1 : Nat) * epsilonX := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs =>
      {O | (scalarBasis B logs, O) ∈
        deployedConstraintBadXEvent family.toRootFamily})
  intro logs
  refine le_trans (MeasureTheory.measure_mono
    (show {O | (scalarBasis B logs, O) ∈
          deployedConstraintBadXEvent family.toRootFamily} <=
        {O | (deployedConstraintXPinnedEvent family.toRootFamily schedule
          (scalarBasis B logs)).Landing O}
      from fun O hbad => deployedConstraintBadX_subset_landing family.toRootFamily schedule
        (scalarBasis B logs) hbad)) ?_
  exact (deployedConstraintXPinnedEvent family.toRootFamily schedule
    (scalarBasis B logs)).landing_measure_le (family.queryBound (scalarBasis B logs))

/-- The complete straight-line constraint relation event reduces to textbook DLOG with only the
programmed-slot loss. -/
theorem straightLineConstraintRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineConstraintRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (relSetWithCoins B family.straightLineConstraintRelationFinder) <=
      bound + 1 / Fintype.card Fp :=
  relationWithCoins_prob_le_of_textbookDL B family.straightLineConstraintRelationFinder hDL

/-- Prices any computed relation finder that pointwise extends the constraint finder. -/
theorem straightLineConstraintFailure_union_relation_prob_le_of_relationSupersetTextbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (finder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hextends : ∀ basis O,
      (family.straightLineConstraintRelationFinder basis O).isSome →
        (finder basis O).isSome)
    {epsilonX bound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B finder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static ∪ relSetWithCoins B finder) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  let zeroSet := family.straightLineRootZeroSet B
  let ipaSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2}
  let rootSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2}
  let oldRelationSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    relSetWithCoins B family.straightLineConstraintRelationFinder
  let relationSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    relSetWithCoins B finder
  let badXSet := family.straightLineConstraintBadXSet B
  have hrelationSubset : oldRelationSet ⊆ relationSet := by
    intro q hq
    have hq' :
        (family.straightLineConstraintRelationFinder (scalarBasis B q.1) q.2).isSome := by
      simpa only [oldRelationSet, relSetWithCoins, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] using hq
    simpa only [oldRelationSet, relationSet, relSetWithCoins, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and] using
      hextends (scalarBasis B q.1) q.2 hq'
  have hcontain : family.straightLineConstraintFailureSet B static ∪ relationSet <=
      zeroSet ∪ (ipaSet ∪ (rootSet ∪ (relationSet ∪ badXSet))) :=
    fun q hq => by
      rcases hq with hfailure | hrelation
      · rcases family.straightLineConstraintFailureSet_subset B static hfailure with
          hzero | hipa | hroot | hold | hbad
        · exact Or.inl hzero
        · exact Or.inr (Or.inl hipa)
        · exact Or.inr (Or.inr (Or.inl hroot))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hrelationSubset hold))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hbad)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hrelation)))
  have hzero := family.straightLineRootZero_prob_le B
  have hipa : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ipaSet <=
      (family.Q + 1 : Nat) *
        (shape.k * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B logs)).Landing O})
    intro logs
    exact family.toIpaFamily.pinnedIpaRoots_landing_measure_le (scalarBasis B logs)
  have hroot := family.straightLineDeployedRoots_prob_le B
  have hrelation : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        relationSet <= bound + 1 / Fintype.card Fp :=
    relationWithCoins_prob_le_of_textbookDL B finder hDL
  have hbadX := family.straightLineConstraintBadX_prob_le B schedule
  refine le_trans (MeasureTheory.measure_mono hcontain) ?_
  refine le_trans (MeasureTheory.measure_union_le zeroSet
    (ipaSet ∪ (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add hzero
    (MeasureTheory.measure_union_le ipaSet (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add hipa
    (MeasureTheory.measure_union_le rootSet (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add hroot (MeasureTheory.measure_union_le relationSet badXSet)))) ?_
  calc
    _ <= (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          ((family.Q + 1 : Nat) *
              (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
            ((family.Q + (11 + shape.k) + 1 : Nat) *
                algebraicRootBudget shape shape.k +
              ((bound + 1 / Fintype.card Fp) +
                (family.Q + 1 : Nat) * epsilonX))) :=
      add_le_add le_rfl (add_le_add le_rfl
        (add_le_add le_rfl (add_le_add hrelation hbadX)))
    _ = _ := by ring

/-- Straight-line AGM deployed-constraint capstone.  The bound is linear in `Q`, uses a fixed
finite relation finder, and contains no expectation or Markov term. -/
theorem straightLineConstraintFailure_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX bound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineConstraintRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  let zeroSet := family.straightLineRootZeroSet B
  let ipaSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2}
  let rootSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2}
  let relationSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    relSetWithCoins B family.straightLineConstraintRelationFinder
  let badXSet := family.straightLineConstraintBadXSet B
  have hzero := family.straightLineRootZero_prob_le B
  have hipa : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ipaSet <=
      (family.Q + 1 : Nat) *
        (shape.k * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs =>
        {O | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B logs)).Landing O})
    intro logs
    exact family.toIpaFamily.pinnedIpaRoots_landing_measure_le (scalarBasis B logs)
  have hroot := family.straightLineDeployedRoots_prob_le B
  have hrelation := family.straightLineConstraintRelation_prob_le_of_textbookDL B hDL
  have hbadX := family.straightLineConstraintBadX_prob_le B schedule
  refine le_trans (MeasureTheory.measure_mono
    (family.straightLineConstraintFailureSet_subset B static)) ?_
  refine le_trans (MeasureTheory.measure_union_le zeroSet
    (ipaSet ∪ (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add hzero
    (MeasureTheory.measure_union_le ipaSet (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add hipa
    (MeasureTheory.measure_union_le rootSet (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add hroot (MeasureTheory.measure_union_le relationSet badXSet)))) ?_
  calc
    _ <= (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          ((family.Q + 1 : Nat) *
              (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
            ((family.Q + (11 + shape.k) + 1 : Nat) *
                algebraicRootBudget shape shape.k +
              ((bound + 1 / Fintype.card Fp) +
                (family.Q + 1 : Nat) * epsilonX))) :=
      add_le_add le_rfl (add_le_add le_rfl
        (add_le_add le_rfl (add_le_add hrelation hbadX)))
    _ = _ := by ring

/-- Runtime-aware spelling of the capstone using the proved fixed four-call budget. -/
theorem straightLineConstraintFailure_prob_le_of_fixedCallsTextbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX bound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (hDL : TextbookDLWithCoinsFixedCallsAdvantageLE B
      family.straightLineConstraintRelationFinder
      family.straightLineConstraintRelationFinderCalls 4 bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX :=
  family.straightLineConstraintFailure_prob_le_of_textbookDL B static schedule hDL.2

/-! ## Promotion from the compressed identity to circuit semantics

The one-run decode proves the verifier's compressed constraint identity, exactly as on the
recursive side.  Row-level semantics additionally price collisions at the four earlier squeezes:
the caller supplies the semantic predicate, the four failure events, and a proof that a compressed
witness outside them has the intended semantics.
-/

/-- Outside the four challenge-failure events, the one-run compressed constraint decode upgrades
to the caller's row-level semantic predicate. -/
def StraightLineConstraintSemanticUpgradeContained
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))) : Prop :=
  {q | family.straightLineConstraintDecoded static q.1 q.2 ∧ ¬ semanticDecoded q.1 q.2} <=
    badY ∪ (badBeta ∪ (badGamma ∪ badTheta))

/-- Basis/oracle pairs on which the one-run endpoint accepts but the caller's semantic predicate
fails. -/
def straightLineConstraintSemanticFailureEvent
    (family : ComputedStraightLineDeployedFSFamily shape)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    ¬ semanticDecoded q.1 q.2}

/-- One-run semantic failure is compressed-identity failure or one of the four explicitly priced
challenge surfaces. -/
theorem straightLineConstraintSemanticFailure_subset_union
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)))
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained static
      semanticDecoded badY badBeta badGamma badTheta) :
    family.straightLineConstraintSemanticFailureEvent semanticDecoded <=
      family.straightLineConstraintFailureEvent static ∪
        (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))) := by
  rintro q ⟨haccept, hnotSemantic⟩
  by_cases hcompressed : family.straightLineConstraintDecoded static q.1 q.2
  · exact Or.inr (hsemantic ⟨hcompressed, hnotSemantic⟩)
  · exact Or.inl ⟨haccept, hcompressed⟩

/-- The four-budget straight-line semantic promotion, factored over an arbitrary bound for the
compressed-identity failure event in the generator-random-oracle model. -/
theorem straightLineConstraintSemanticFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)))
    {compressedBound yBound betaBound gammaBound thetaBound : ENNReal}
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained static
      semanticDecoded badY badBeta badGamma badTheta)
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) <= compressedBound)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent semanticDecoded)
      <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) := by
  let mu := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
  let basisOracle : ((↥(Set.range query) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) ->
      ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    fun p => (orchardGeneratorROBasis query p.1, p.2)
  change mu (basisOracle ⁻¹'
      family.straightLineConstraintSemanticFailureEvent semanticDecoded) <= _
  have hsubset : basisOracle ⁻¹'
        family.straightLineConstraintSemanticFailureEvent semanticDecoded <=
      basisOracle ⁻¹'
        (family.straightLineConstraintFailureEvent static ∪
          (badY ∪ (badBeta ∪ (badGamma ∪ badTheta)))) :=
    Set.preimage_mono
      (family.straightLineConstraintSemanticFailure_subset_union static semanticDecoded
        badY badBeta badGamma badTheta hsemantic)
  calc
    mu (basisOracle ⁻¹'
        family.straightLineConstraintSemanticFailureEvent semanticDecoded)
        <= mu (basisOracle ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))))) :=
      MeasureTheory.measure_mono hsubset
    _ = mu ((basisOracle ⁻¹' family.straightLineConstraintFailureEvent static) ∪
        ((basisOracle ⁻¹' badY) ∪
          ((basisOracle ⁻¹' badBeta) ∪
            ((basisOracle ⁻¹' badGamma) ∪ (basisOracle ⁻¹' badTheta))))) := by
      simp only [Set.preimage_union]
    _ <= mu (basisOracle ⁻¹' family.straightLineConstraintFailureEvent static) +
        (mu (basisOracle ⁻¹' badY) +
          (mu (basisOracle ⁻¹' badBeta) +
            (mu (basisOracle ⁻¹' badGamma) + mu (basisOracle ⁻¹' badTheta)))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
            (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))))
    _ <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) :=
      add_le_add hcompressed (add_le_add hY (add_le_add hBeta (add_le_add hGamma hTheta)))

end ComputedStraightLineDeployedFSFamily

end Zcash.Snark
