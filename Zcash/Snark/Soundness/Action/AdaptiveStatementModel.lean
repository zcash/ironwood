import Zcash.Circuits.Integration.ActionCorrectness
import Zcash.Snark.Soundness.AGM.AdaptiveOnline
import Zcash.Snark.Verifier.Deployed

/-!
# Adaptive-statement Action soundness model

The existing Action capstones fix the public inputs outside the random-oracle experiment.  This
module introduces the stronger deployed game in which one online-AGM adversary returns the public
inputs and proof together.  Its verifier transcript is not a free `init`: it is reconstructed from
the basis-dependent VK transcript representation and the instance commitments derived from the
adversary's output.

This file defines the game and its load-bearing pre-`theta` invariant.  Probability composition is
kept in later modules so the existing fixed-statement capstones remain unchanged.

## Intended instantiation

`vkHash` supplies the opaque transcript representation of the fixed canonical key at position
zero.  The theorems quantify over every such function, including a constant fixture digest, and do
not claim cross-key binding.  A deployed claim that distinct verifying keys cannot share this
representation requires collision resistance of the concrete key hash below this abstraction
boundary; global mathematical injectivity is neither assumed nor needed by this game.

## Trust boundary

These are online-AGM, random-oracle results.  Representation coverage — `OnlineMemberProofData`
with `fixedRepresented` and `permutationCommonRepresented` — is part of the adversary type; the
AGM basis is heuristically instantiated by fixed hash-to-curve generators (the book's
Security Models page); the Lean verifier is checked to correspond to deployed Halo 2 by the
fingerprint fixtures; and the bridge from extracted circuit witnesses to the abstract ledger
relation is tracked separately (the definitions page's high-level-relation entry).

A deployed byte-level prover is not confined to this adversary type: it can place a fresh point —
a hash-to-curve output, say — in a proof slot without knowing coefficients over the enumerated
basis.  That exclusion is the accepted algebraic-group floor of these results; the known
strengthening models hash-to-curve as an adversary-queryable oracle whose fresh outputs extend
the basis.
-/

namespace Zcash.Snark

open Zcash.Common

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

local instance adaptiveStatementVestaInhabited : Inhabited VestaG := ⟨0⟩

/-- The Action verifier shape used by an adaptive-statement experiment. -/
abbrev AdaptiveActionStatementShape (pp : ProofParams) : Shape :=
  actionCircuit.shape.withProofParams pp

/-- The deployed Action circuit has exactly one configured instance column. -/
theorem adaptiveActionStatement_numInstanceColumns (pp : ProofParams) :
    (AdaptiveActionStatementShape pp).numInstanceColumns = 1 := by
  rw [actionCircuit.shape.withProofParams_numInstanceColumns pp,
    actionCircuit.shape_numInstanceColumns]
  exact actionCircuit_numInstanceColumns_eq

/-- A zero public-instance column commits only to its blinding generator, for any verifier URS. -/
theorem adaptiveCommitInstance_of_rows_zero {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {omega : Fp} (key : LagrangeCommitmentKey urs omega)
    {values : List Fp} (hzero : ∀ i, values.getD i 0 = 0) (blind : Fp) :
    key.commitInstance values blind = blind • urs.w := by
  rw [LagrangeCommitmentKey.commitInstance, LagrangeCommitmentKey.commitRows,
    show zeroPaddedRows (n := 2 ^ urs.k) values = 0 from funext fun i => hzero (i : ℕ)]
  rw [show commitGen key.generators (0 : Fin (2 ^ urs.k) → Fp) = 0 by
    simp [commitGen], zero_add]

/-- The canonical Action verifying key at one AGM basis. -/
abbrev adaptiveActionStatementVk (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    VerifyingKey (AdaptiveActionStatementShape pp) Fp VestaG :=
  actionCircuit.toVerifierKey
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)

/-- Public inputs determine the complete instance-commitment family used by the verifier. -/
abbrev adaptiveActionStatementInstanceCommitment (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG :=
  actionCircuit.instanceCommitment
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) inputs

/-- Normalize the total verifier function outside the configured Action instance-column range.
Those indices are never absorbed or queried; using the URS blind generator matches the commitment
of Action's all-zero unconfigured columns. -/
def boundedAdaptiveStatementInstanceCommitment (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG) :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG :=
  fun p column =>
    if column < (AdaptiveActionStatementShape pp).numInstanceColumns then
      instanceCommitment p column
    else (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w

/-- The Action circuit's derived commitment family is already equal to its bounded normalization. -/
theorem adaptiveActionStatementInstanceCommitment_eq_bounded (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    adaptiveActionStatementInstanceCommitment pp basis inputs =
      boundedAdaptiveStatementInstanceCommitment pp basis
        (adaptiveActionStatementInstanceCommitment pp basis inputs) := by
  funext p column
  unfold boundedAdaptiveStatementInstanceCommitment
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · rw [if_pos hcolumn]
  · rw [if_neg hcolumn]
    have hne : column ≠ 0 := by
      intro hzero
      subst column
      apply hcolumn
      rw [adaptiveActionStatement_numInstanceColumns]
      omega
    change (actionCircuit.instanceCommitmentKey
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).commitInstance
          (actionCircuit.publicInputRows
            (inputs (Fin.cast (actionCircuit.shape.withProofParams_numProofs pp) p)) ⟨column⟩) 1 =
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w
    rw [adaptiveCommitInstance_of_rows_zero _
      (actionCircuit_publicInputRows_ne_zero _ hne)]
    simp

/-- Canonical initial-transcript length, independent of the selected statement's values. -/
def adaptiveStatementInitLength (shape : Shape) : ℕ :=
  1 + shape.numProofs * shape.numInstanceColumns

/-- One common finite oracle domain for every statement and AGM basis. -/
abbrev AdaptiveActionStatementTranscript (pp : ProofParams) :=
  BTranscript Fp VestaG
    (preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (AdaptiveActionStatementShape pp).k)

/-- Instance representations in the same proof-major, column-major order as the transcript. -/
def adaptiveStatementInstanceRepresentationList {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (representations : Fin shape.numProofs → Fin shape.numInstanceColumns →
      AlgebraicPoint (F := Fp) basis) : List (AlgebraicPoint (F := Fp) basis) :=
  (List.ofFn fun p => List.ofFn fun column => representations p column).flatten

/-- The flattened instance-representation list has one entry per proof and instance column, so its
length is fixed by the shape. -/
theorem adaptiveStatementInstanceRepresentationList_length {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (representations : Fin shape.numProofs → Fin shape.numInstanceColumns →
      AlgebraicPoint (F := Fp) basis) :
    (adaptiveStatementInstanceRepresentationList representations).length =
      shape.numProofs * shape.numInstanceColumns := by
  simp [adaptiveStatementInstanceRepresentationList, Function.comp_def]

/-- The canonical augmented-basis coordinates of one selected public-instance commitment.
Unlike an adversary-supplied representation, these coefficients are computed from the actual
public-input rows and the verifier's default instance blind. -/
def canonicalAdaptiveStatementInstanceRepresentation (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    AlgebraicPoint (F := Fp) basis :=
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let proofIndex : Fin pp.numProofs :=
    Fin.cast (actionCircuit.shape.withProofParams_numProofs pp) p
  let instanceColumn : Column .instance := ⟨column⟩
  let coeffs := instanceCoefficients (2 ^ urs.k) actionCircuit.omega
    (actionCircuit.publicInputRows (inputs proofIndex) instanceColumn)
  { point := adaptiveActionStatementInstanceCommitment pp basis inputs p column
    repr :=
      { coeffs := augmentedCoeffs coeffs ![0, 1]
        hEq := by
          calc
            representationEval basis (augmentedCoeffs coeffs ![0, 1]) =
                representationEval (augmentedBasis urs.g ![urs.u, urs.w])
                  (augmentedCoeffs coeffs ![0, 1]) := by
              exact congrArg (fun b => representationEval b (augmentedCoeffs coeffs ![0, 1]))
                (augmentedBasis_ursOfAugmentedBasis
                  (AdaptiveActionStatementShape pp).k basis).symm
            _ = commitGen urs.g coeffs + (0 • urs.u + 1 • urs.w) := by
              rw [representationEval_augmentedBasis, Fin.sum_univ_two]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
              rfl
            _ = commit urs coeffs + urs.w := by
              simp only [zero_smul, zero_add, one_smul, commit]
              rfl
            _ = adaptiveActionStatementInstanceCommitment pp basis inputs p column := by
              change commit urs coeffs + urs.w =
                actionCircuit.instanceCommitment urs inputs proofIndex instanceColumn.index
              exact (actionCircuit.instanceCommitment_column_eq_commit
                pp urs inputs proofIndex instanceColumn).symm } }

/-- An online-AGM output that selects both the Action public statement and its proof. -/
structure AdaptiveActionStatementOutput (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)) where
  inputs : Fin pp.numProofs → PublicInputs Fp
  instanceRepresentations :
    Fin (AdaptiveActionStatementShape pp).numProofs →
      Fin (AdaptiveActionStatementShape pp).numInstanceColumns →
        AlgebraicPoint (F := Fp) basis
  instanceRepresented : ∀ p column,
    (instanceRepresentations p column).point =
      adaptiveActionStatementInstanceCommitment pp basis inputs p column
  proofData : OnlineMemberProofData
    (vk := adaptiveActionStatementVk pp basis)
    (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis inputs)
    basis
    (adaptiveStatementInstanceRepresentationList instanceRepresentations ++
      fixedRepresentations)

namespace AdaptiveActionStatementOutput

/-- Erase the member-coverage wrapper to the algebraic proof consumed by verifier reductions. -/
def toAlgebraicWfProof {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    AlgebraicWfProof basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs) :=
  output.proofData.toAlgebraicWfProof

/-- The verifier-controlled transcript prefix for the output statement. -/
def init {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    List (TranscriptElt Fp VestaG) :=
  initialTranscript vkTranscriptRepr
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)

@[simp] theorem init_length {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    (output.init vkTranscriptRepr).length =
      adaptiveStatementInitLength (AdaptiveActionStatementShape pp) := by
  simp [init, adaptiveStatementInitLength]

/-- The eleven statement-bound pre-IPA query points in the common oracle domain. -/
def prefixesPre {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    Fin 11 → AdaptiveActionStatementTranscript pp :=
  fun i =>
    let t := algebraicFullPrefixesPre (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof i
    ⟨t.val, by simpa using t.prop⟩

/-- The statement-bound IPA-round query points in the common oracle domain. -/
def prefixes {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    Fin (AdaptiveActionStatementShape pp).k → AdaptiveActionStatementTranscript pp :=
  fun j =>
    let t := algebraicFullPrefixes (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof j
    ⟨t.val, by simpa using t.prop⟩

/-- Taking a pre-IPA-length prefix of an actual IPA point recovers the corresponding pre-IPA
point in the common adaptive-statement domain. -/
theorem prefixes_take_pre {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) (n : Fin 11) :
    (output.prefixes vkTranscriptRepr j).val.take
        (preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n) =
      (output.prefixesPre vkTranscriptRepr n).val := by
  change (roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j).take
        (preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n) =
    preIpaSqueezePoints (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof.proof.1 n
  have hpre : preIpaSqueezePoints (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof.proof.1 n <+:
    roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j :=
    (preIpaSqueezePoints_prefix (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof.proof.1 n).trans (by
        rw [roundTranscriptFin]
        exact List.prefix_append _ _)
  have htake := List.prefix_iff_eq_take.mp hpre
  rw [preIpaSqueezePoints_length_eq (output.init vkTranscriptRepr)
    output.toAlgebraicWfProof.proof.1 output.proofData.wellFormed] at htake
  simpa using htake.symm

/-- Taking a strict earlier-round length from an actual IPA point recovers that earlier point. -/
theorem prefixes_take_round {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j i : Fin (AdaptiveActionStatementShape pp).k) (hij : i.val < j.val) :
    (output.prefixes vkTranscriptRepr j).val.take
        (preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (i.val + 1)) =
      (output.prefixes vkTranscriptRepr i).val := by
  change (roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j).take
        (preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (i.val + 1)) =
    roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds i
  rw [← output.init_length]
  rw [← preIpaTranscript_length_eq (output.init vkTranscriptRepr)
    output.toAlgebraicWfProof.proof.1 output.proofData.wellFormed]
  exact roundTranscriptFin_take _ _ hij.le

/-- The first oracle query is exactly VK, instances, advice commitments, then the challenge marker. -/
theorem prefixesPre_zero_val {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    (output.prefixesPre vkTranscriptRepr 0).val =
      preThetaTranscriptForStatement vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof.1 := by
  rfl

/-- The basis-dependent VK transcript representation is present before `theta`. -/
theorem vkTranscriptRepr_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    TranscriptElt.scalar vkTranscriptRepr ∈
      (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact vkTranscriptRepr_mem_preThetaTranscriptForStatement _ _ _

/-- Every commitment derived from the adversary-selected public inputs is present before `theta`. -/
theorem instanceCommitment_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    TranscriptElt.point
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs p column) ∈
        (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact instanceCommitment_mem_preThetaTranscriptForStatement _ _ _ p column

/-- Recover a query-time AGM representation for an instance commitment from the `theta` label. -/
def queryInstanceRepresentation {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (label : AlgebraicTranscriptQuery (F := Fp) basis
      (output.prefixesPre vkTranscriptRepr 0))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    AlgebraicPoint (F := Fp) basis :=
  label.representationOfPoint
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs p column)
    (mem_transcriptGroupPoints_of_mem_point
      (output.instanceCommitment_mem_prefixesPre_zero vkTranscriptRepr p column))

@[simp] theorem queryInstanceRepresentation_point {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (label : AlgebraicTranscriptQuery (F := Fp) basis
      (output.prefixesPre vkTranscriptRepr 0))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    (output.queryInstanceRepresentation vkTranscriptRepr label p column).point =
      adaptiveActionStatementInstanceCommitment pp basis output.inputs p column := by
  exact AlgebraicTranscriptQuery.representationOfPoint_point _ _ _

/-- All final instance representations denote points already absorbed at the first squeeze. -/
theorem instanceRepresentations_coveredAtTheta {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixesPre vkTranscriptRepr 0).val := by
  intro ap hap
  rw [adaptiveStatementInstanceRepresentationList] at hap
  obtain ⟨row, hrow, hapRow⟩ := List.mem_flatten.mp hap
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp hrow
  obtain ⟨column, hcolumn⟩ := List.mem_ofFn.mp (hp ▸ hapRow)
  rw [← hcolumn, output.instanceRepresented p column]
  exact mem_transcriptGroupPoints_of_mem_point
    (output.instanceCommitment_mem_prefixesPre_zero vkTranscriptRepr p column)

/-- Final instance representations remain covered at every later pre-IPA squeeze. -/
theorem instanceRepresentations_coveredPre {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixesPre vkTranscriptRepr n).val := by
  intro ap hap
  have hzero := output.instanceRepresentations_coveredAtTheta vkTranscriptRepr ap hap
  apply (transcriptGroupPoints_prefix ?_).mem hzero
  exact preIpaSqueezePoints_prefix_of_le
    (output.init vkTranscriptRepr) output.toAlgebraicWfProof.proof.1
    output.toAlgebraicWfProof.proof.2 0 n (by omega)

/-- Final instance representations also remain covered throughout the IPA round chain. -/
theorem instanceRepresentations_coveredRound {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixes vkTranscriptRepr j).val := by
  intro ap hap
  have hzero := output.instanceRepresentations_coveredAtTheta vkTranscriptRepr ap hap
  apply (transcriptGroupPoints_prefix ?_).mem hzero
  change preIpaSqueezePoints (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof.proof.1 0 <+:
    roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j
  exact (preIpaSqueezePoints_prefix
    (output.init vkTranscriptRepr) output.toAlgebraicWfProof.proof.1 0).trans (by
      unfold roundTranscriptFin
      exact List.prefix_append _ _)

/-- Every proof-controlled advice commitment follows the statement prefix and precedes `theta`. -/
theorem adviceCommitment_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numAdviceColumns) :
    TranscriptElt.point
      (output.toAlgebraicWfProof.proof.1.adviceCommitments p column) ∈
        (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact adviceCommitment_mem_preThetaTranscriptForStatement _ _ _ p column

end AdaptiveActionStatementOutput

/-- Generous structural cap on the verifier-known representation table traversed by decoding. -/
def adaptiveStatementFixedRepresentationLimit : Nat := 2 ^ 89

/-- A basis-indexed online-AGM adversary that chooses its public statement and proof together.

The fixed representation table is part of the statement family rather than the selected proof,
but it is traversed by direct-coordinate decoding.  Bounding its length here makes that input-size
resource structural: every family carries the proof needed to derive the endpoint's decode-work
bound, instead of restating a numerical decode premise in each security profile.  `2^89` is a
deliberately generous interface cap (the captured Orchard key needs only its fixed and permutation
commitments) and leaves room for the shape-indexed proof data inside the existing `2^90` deployed
source envelope. -/
structure ComputedAdaptiveActionStatementFSFamily (pp : ProofParams) where
  /-- The key digest absorbed at transcript position zero, as a function of the verifying key.
  The game always applies it to its canonical basis-dependent key.  Fixtures may instantiate a
  constant digest for faithfulness checks; cross-key collision resistance is an external deployed
  assumption, not a premise of the adaptive-statement theorem. -/
  vkHash :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      VerifyingKey (AdaptiveActionStatementShape pp) Fp VestaG → Fp
  fixedRepresentations :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      List (AlgebraicPoint (F := Fp) basis)
  /-- Family-construction obligation, not a theorem about an unspecified deployed table.  Once a
  concrete family supplies this invariant, the capstone derives its direct-decode work bound
  without accepting a separate numeric work premise. -/
  fixedRepresentations_length_le : ∀ basis,
    (fixedRepresentations basis).length ≤ adaptiveStatementFixedRepresentationLimit
  fixedRepresented : ∀ basis i,
    (∃ rotation, (i, rotation) ∈ (adaptiveActionStatementVk pp basis).fixedQueryLayout) →
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (adaptiveActionStatementVk pp basis).fixedCommitment i
  permutationCommonRepresented : ∀ basis
      (column : Fin (AdaptiveActionStatementShape pp).numPermutationColumns),
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (adaptiveActionStatementVk pp basis).permutationCommonCommitment column
  adversary :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      LabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (fixedRepresentations basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAdaptiveActionStatementFSFamily

/-- The digest scalar the family absorbs for the canonical key at one basis.  Every transcript
definition reads the digest through this abbreviation, so the digest parameterization is a
one-field change. -/
abbrev vkTranscriptRepr {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) : Fp :=
  family.vkHash basis (adaptiveActionStatementVk pp basis)

/-- One adaptive-statement random-oracle table. -/
abbrev Coins {pp : ProofParams} (_family : ComputedAdaptiveActionStatementFSFamily pp) :=
  AdaptiveActionStatementTranscript pp → Fp

/-- Run the adversary once and retain its jointly selected statement and proof. -/
def runOutput {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis) :=
  (family.adversary basis).run O

/-- Materialize a finite family of challenge reads.  Reduction entry points retain this vector
before exposing its lookup function, which makes the one-read-per-index cost visible in generated
code rather than relying on compiler sharing of a function-valued `let`. -/
def challengeReadVector {n : Nat} (read : Fin n → Fp) : Vector Fp n :=
  Vector.ofFn read

@[simp] theorem challengeReadVector_get {n : Nat} (read : Fin n → Fp) (i : Fin n) :
    (challengeReadVector read).get i = read i := by
  simp [challengeReadVector]

/-- Materialized pre-IPA challenge vector for one retained output. -/
def preIpaReadVectorOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Vector Fp 11 :=
  challengeReadVector fun i =>
    O (output.prefixesPre (family.vkTranscriptRepr basis) i)

/-- Materialized IPA-round challenge vector for one retained output. -/
def ipaReadVectorOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Vector Fp (AdaptiveActionStatementShape pp).k :=
  challengeReadVector fun j =>
    O (output.prefixes (family.vkTranscriptRepr basis) j)

/-- Extensional lookup view of the pre-IPA challenge vector.  Executable caches retain the vector
itself before exposing this lookup behavior. -/
def preIpaReadsOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Fin 11 → Fp :=
  fun i => (family.preIpaReadVectorOfOutput basis O output).get i

/-- Extensional lookup view of the IPA-round challenge vector. -/
def ipaReadsOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Fin (AdaptiveActionStatementShape pp).k → Fp :=
  fun j => (family.ipaReadVectorOfOutput basis O output).get j

/-- Read every challenge once from the canonical prefixes determined by the retained output. -/
def runRecord {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Challenges (AdaptiveActionStatementShape pp).k Fp :=
  let output := family.runOutput basis O
  let pre := family.preIpaReadVectorOfOutput basis O output
  let rounds := family.ipaReadVectorOfOutput basis O output
  chRecord
    (fun i => pre.get i)
    (fun j => rounds.get j)

/-- The table-read record is exactly the canonical statement-bound Fiat--Shamir execution. -/
theorem runRecord_eq_roChallenges {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.runRecord basis O =
      roChallenges (extendO O)
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof.proof.1 := by
  let output := family.runOutput basis O
  let init := output.init (family.vkTranscriptRepr basis)
  let ps := output.toAlgebraicWfProof.proof.1
  have hpre : ∀ i : Fin 11,
      (preIpaSqueezePoints init ps i).length ≤
        preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (AdaptiveActionStatementShape pp).k := by
    intro i
    exact (output.prefixesPre (family.vkTranscriptRepr basis) i).prop
  have hround : ∀ j : Fin (AdaptiveActionStatementShape pp).k,
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j).length ≤
        preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (AdaptiveActionStatementShape pp).k := by
    intro j
    exact (output.prefixes (family.vkTranscriptRepr basis) j).prop
  have h := roChallenges_extendO_eq_chRecord O init ps hpre hround
  rw [h]
  unfold runRecord
  apply congrArg₂ chRecord
  · funext i
    simp [preIpaReadVectorOfOutput]
    rfl
  · funext j
    simp [ipaReadVectorOfOutput]
    rfl

/-- Checked Halo2 acceptance for the adversary-selected public statement and proof. -/
def accepts {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Prop :=
  let output := family.runOutput basis O
  DeployedAccepts (AdaptiveActionStatementShape pp)
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    output.toAlgebraicWfProof.proof.1 (family.runRecord basis O)

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
