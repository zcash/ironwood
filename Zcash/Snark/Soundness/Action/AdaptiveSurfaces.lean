import Zcash.Snark.Soundness.Action.AdaptiveTerminal
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.AGM.AdaptiveSurfaces

/-!
# Action semantic surfaces for arbitrary adaptive online-AGM adversaries

The first five deployed squeezes are `theta`, `beta`, `gamma`, `y`, and `x`.  At each point an
online-AGM annotation fixes exactly the prover commitments already absorbed into that prefix.
This file records those stage-local representation lists before constructing the corresponding
finite bad sets.
-/

namespace Zcash.Snark

open Classical
open Halo2 CompPoly CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveActionSurfaces : Inhabited VestaG := ⟨0⟩

set_option maxRecDepth 10000

/-- Prover-emitted AGM representations available at one of the five Action semantic squeezes.
The definition follows the deployed transcript order literally. -/
def AlgebraicProofString.actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    List (AlgebraicPoint (F := Fp) basis) :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
      [aps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn aps.hPieces

/-- Advice commitments precede every semantic squeeze. -/
theorem AlgebraicProofString.adviceCommitment_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numAdviceColumns) :
    aps.adviceCommitments p i ∈ aps.actionRepresentationsBefore n := by
  have hadvice : aps.adviceCommitments p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · exact hadvice
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

/-- The permuted lookup inputs precede every squeeze from the second on (`1 ≤ n`). -/
theorem AlgebraicProofString.lookupPermutedInput_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 1 ≤ (n : Nat)) :
    aps.lookupPermutedInput p i ∈ aps.actionRepresentationsBefore n := by
  have hinput : aps.lookupPermutedInput p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

/-- The permuted lookup tables precede every squeeze from the second on (`1 ≤ n`). -/
theorem AlgebraicProofString.lookupPermutedTable_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 1 ≤ (n : Nat)) :
    aps.lookupPermutedTable p i ∈ aps.actionRepresentationsBefore n := by
  have htable : aps.lookupPermutedTable p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

/-- The permutation product commitments precede every squeeze from the fourth on (`3 ≤ n`). -/
theorem AlgebraicProofString.permutationProduct_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numPermutationSets)
    (hn : 3 ≤ (n : Nat)) :
    aps.permutationProduct p i ∈ aps.actionRepresentationsBefore n := by
  have hproduct : aps.permutationProduct p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · omega
    · split <;> simp only [List.mem_append, List.mem_singleton] <;> tauto

/-- The lookup product commitments precede every squeeze from the fourth on (`3 ≤ n`). -/
theorem AlgebraicProofString.lookupProduct_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 3 ≤ (n : Nat)) :
    aps.lookupProduct p i ∈ aps.actionRepresentationsBefore n := by
  have hproduct : aps.lookupProduct p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · omega
    · split <;> simp only [List.mem_append, List.mem_singleton] <;> tauto

/-- Coordinate-free counterpart of `actionRepresentationsBefore`. -/
def ProofString.actionCommitmentPointsBefore {G : Type*}
    (ps : ProofString shape Fp G) (n : Fin 5) : List G :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => ps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => ps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupProduct p i).flatten ++
      [ps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn ps.hPieces

/-- Erasing stage representations yields the corresponding commitment-point prefix. -/
@[simp] theorem AlgebraicProofString.actionRepresentationsBefore_points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    (aps.actionRepresentationsBefore n).map AlgebraicPoint.point =
      aps.erase.actionCommitmentPointsBefore n := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      ProofString.actionCommitmentPointsBefore, AlgebraicProofString.erase,
      Function.comp_def, List.map_flatten]

/-- At the final Action squeeze, the stage source is the complete pre-`x1` assembly source. -/
theorem AlgebraicProofString.actionRepresentationsBefore_four_append
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    aps.actionRepresentationsBefore (4 : Fin 5) ++ fixed =
      aps.preX1AssemblySource fixed := by
  simp [AlgebraicProofString.actionRepresentationsBefore,
    AlgebraicProofString.preX1AssemblySource, AlgebraicProofString.preX1Points,
    List.append_assoc]

/-- Every representation used by an Action semantic surface occurs in the complete pre-`x`
online source. -/
theorem AlgebraicProofString.actionRepresentationsBefore_mem_preX1Points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap ∈ aps.preX1Points := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      AlgebraicProofString.preX1Points] at hap ⊢ <;> aesop

/-- Appending verifier-fixed representations preserves inclusion in the complete pre-`x`
assembly source. -/
theorem AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n ++ fixed) :
    ap ∈ aps.preX1AssemblySource fixed := by
  unfold AlgebraicProofString.preX1AssemblySource
  rw [List.mem_append] at hap ⊢
  exact hap.imp (aps.actionRepresentationsBefore_mem_preX1Points n ap) id

/-- Every stage-local prover representation is already present in that stage's actual query
transcript. -/
theorem AlgebraicProofString.actionRepresentationsBefore_covered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap.point ∈ transcriptGroupPoints
      (preIpaSqueezePoints init aps.erase (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init aps.erase i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init aps.erase hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 0)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    obtain ⟨p, i, h⟩ := hap
    rw [← h]
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 1)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 2)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 3)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 4)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
    · obtain ⟨i, h⟩ := hpiece
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init aps.erase i)

/-- Ordinary commitment points in the stage view are covered by the same exact prefix. -/
theorem ProofString.actionCommitmentPointsBefore_covered
    (init : List (TranscriptElt Fp VestaG))
    (ps : ProofString shape Fp VestaG) (hwf : PsWellFormed ps) (n : Fin 5)
    (P : VestaG) (hP : P ∈ ps.actionCommitmentPointsBefore n) :
    P ∈ transcriptGroupPoints
      (preIpaSqueezePoints init ps (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init ps i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init ps hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 0)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    obtain ⟨p, i, rfl⟩ := hP
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 1)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 2)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 3)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 4)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
    · obtain ⟨i, rfl⟩ := hpiece
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init ps i)

/-- Query-local stage source: first pre-answer representations of exactly the Action commitments
already absorbed at this squeeze, followed by verifier-fixed representations. -/
def adaptiveActionQuerySource
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    {t : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedPreIpaPrefix (shape := shape) init (Fin.castLE (by omega) n) t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.actionCommitmentPointsBefore_covered
          init decoded.proof.2 n P hP) ++ fixed

/-- Canonical polynomial carried by a stage-local AGM source. -/
def adaptiveActionPointPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    VestaG → CPoly :=
  onlinePointPolynomial source

/-- Commitment slots actually consumed by the constraint model.  Returning zero outside this
finite layout makes the stage resolver agree with canonical routing on absent identities. -/
def adaptiveActionCommitmentActive
    (proofShape : Shape) {G : Type*}
    (vk : VerifyingKey proofShape Fp G) : CommitmentId → Prop
  | .instanceCol p i => p < proofShape.numProofs ∧
      ∃ rotation, (i, rotation) ∈ vk.instanceQueryLayout
  | .adviceCol p i => p < proofShape.numProofs ∧ i < proofShape.numAdviceColumns ∧
      ∃ rotation, (i, rotation) ∈ vk.adviceQueryLayout
  | .fixedCol i => ∃ rotation, (i, rotation) ∈ vk.fixedQueryLayout
  | .permProduct p s => p < proofShape.numProofs ∧ s < proofShape.numPermutationSets
  | .lookupProduct p l | .lookupPermInput p l | .lookupPermTable p l =>
      p < proofShape.numProofs ∧ l < proofShape.numLookups
  | .permCommon c => c < proofShape.numPermutationColumns
  | .vanishingH | .randomPoly => False

/-- Executable finite-list check for whether a query layout names a column. -/
def adaptiveActionLayoutContainsColumn
    (layout : List (Nat × Int)) (column : Nat) : Bool :=
  layout.any fun entry => entry.1 == column

/-- The executable layout check succeeds exactly when the column occurs at some rotation. -/
theorem adaptiveActionLayoutContainsColumn_iff
    (layout : List (Nat × Int)) (column : Nat) :
    adaptiveActionLayoutContainsColumn layout column = true ↔
      ∃ rotation, (column, rotation) ∈ layout := by
  simp only [adaptiveActionLayoutContainsColumn, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨candidate, rotation⟩, hmem, heq⟩
    dsimp only at heq
    subst candidate
    exact ⟨rotation, hmem⟩
  · rintro ⟨rotation, hmem⟩
    exact ⟨(column, rotation), hmem, rfl⟩

instance adaptiveActionLayoutColumnMem_decidable
    (layout : List (Nat × Int)) (column : Nat) :
    Decidable (∃ rotation, (column, rotation) ∈ layout) :=
  decidable_of_iff (adaptiveActionLayoutContainsColumn layout column = true)
    (adaptiveActionLayoutContainsColumn_iff layout column)

instance adaptiveActionCommitmentActive_decidable
    (proofShape : Shape) {G : Type*}
    (vk : VerifyingKey proofShape Fp G) (id : CommitmentId) :
    Decidable (adaptiveActionCommitmentActive proofShape vk id) := by
  cases id <;> simp only [adaptiveActionCommitmentActive] <;> infer_instance

/-- The derived Action advice layout never names an out-of-range advice column. -/
theorem adaptiveActionAdviceLayout_column_lt
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (column : ℕ) (rotation : ℤ)
    (hmem : (column, rotation) ∈ (ActionTerminal.vkAt basis).adviceQueryLayout) :
    column < actionCircuit.adviceColumnCount := by
  rw [actionCircuit.adviceColumnCount_eq_constraintSystem]
  apply List.forall_iff_forall_mem.mp
    actionCircuit.adviceQueryLayout_columns_lt (column, rotation)
  simpa only [ActionTerminal.vkAt,
    actionCircuit.toVerifierKey_adviceQueryLayout] using hmem

/-- Every active Action commitment identity has a concrete query in the deployed assembly. -/
theorem adaptiveActionActive_query
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id) :
    ∃ q ∈ assembleQueries (ActionTerminal.vkAt basis)
        (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) ps ch,
      q.commId = id := by
  let vk := ActionTerminal.vkAt basis
  let ic := actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs
  have hadviceCount :
      vk.adviceQueryLayout.length =
        (actionCircuit.shape.withProofParams pp).numAdviceQueries := by
    simpa only [vk, Halo2.CircuitShape.withProofParams_numAdviceQueries,
      TopLevelCircuit.adviceQueryCount] using
        actionCircuit.toVerifierKey_adviceQueryCount
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hinstanceCount :
      vk.instanceQueryLayout.length =
        (actionCircuit.shape.withProofParams pp).numInstanceQueries := by
    simpa only [vk, Halo2.CircuitShape.withProofParams_numInstanceQueries,
      TopLevelCircuit.instanceQueryCount] using
        actionCircuit.toVerifierKey_instanceQueryCount
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hfixedCount :
      vk.fixedQueryLayout.length =
        (actionCircuit.shape.withProofParams pp).numFixedQueries := by
    simpa only [vk, Halo2.CircuitShape.withProofParams_numFixedQueries,
      TopLevelCircuit.fixedQueryCount] using
        actionCircuit.toVerifierKey_fixedQueryCount
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  cases id with
  | instanceCol p column =>
      rcases hactive with ⟨hp, rotation, hlayout⟩
      obtain ⟨q, hq, hqid⟩ := instanceQuery_of_layout vk ic ps ch
        ⟨p, hp⟩ column rotation hinstanceCount hlayout
      exact ⟨q, hq, hqid⟩
  | adviceCol p column =>
      rcases hactive with ⟨hp, hcolumn, rotation, hlayout⟩
      obtain ⟨j, hj, hentry⟩ := List.mem_iff_getElem.mp hlayout
      have hje : j < (actionCircuit.shape.withProofParams pp).numAdviceQueries := by
        simpa only [← hadviceCount] using hj
      obtain ⟨q, hq, hqid, -⟩ := advice_query_mem_assembleQueries_eval
        vk ic ps ch ⟨p, hp⟩ hj hje
      refine ⟨q, hq, ?_⟩
      rw [List.getD_eq_getElem _ _ hj, hentry] at hqid
      exact hqid
  | fixedCol column =>
      rcases hactive with ⟨rotation, hlayout⟩
      obtain ⟨q, hq, hqid⟩ := fixedQuery_of_layout vk ic ps ch
        column rotation hfixedCount hlayout
      exact ⟨q, hq, hqid⟩
  | permProduct p s =>
      rcases hactive with ⟨hp, hs⟩
      obtain ⟨q, hq, hqid, -⟩ := perm_product_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨s, hs⟩
      exact ⟨q, hq, hqid⟩
  | lookupProduct p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_product_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | lookupPermInput p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_permInput_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | lookupPermTable p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_permTable_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | permCommon c =>
      obtain ⟨q, hq, hqid, -⟩ := permCommon_query_mem_assembleQueries
        vk ic ps ch ⟨c, hactive⟩
      exact ⟨q, hq, hqid⟩
  | vanishingH => exact False.elim hactive
  | randomPoly => exact False.elim hactive

/-- Every non-terminal identity emitted by the deployed query assembler is one of the active
Action commitment slots. -/
theorem adaptiveActionQuery_active_or_terminal
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (q : VerifierQuery (actionCircuit.shape.withProofParams pp).k Fp VestaG)
    (hq : q ∈ assembleQueries (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) ps ch) :
    adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) q.commId ∨
      q.commId = .vanishingH ∨ q.commId = .randomPoly := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ := List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ := List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with ((hinstance | hadvice) | hpermutation) | hlookup
    · rw [columnQueries, List.mem_map] at hinstance
      obtain ⟨entry, hentry, rfl⟩ := hinstance
      left
      exact ⟨proofIndex.isLt, entry.1.2, (List.of_mem_zip hentry).1⟩
    · rw [columnQueries, List.mem_map] at hadvice
      obtain ⟨entry, hentry, rfl⟩ := hadvice
      have hlayout : entry.1 ∈ (ActionTerminal.vkAt basis).adviceQueryLayout :=
        (List.of_mem_zip hentry).1
      left
      exact ⟨proofIndex.isLt,
        by
          simpa only [Halo2.CircuitShape.withProofParams_numAdviceColumns,
            TopLevelCircuit.adviceColumnCount] using
              adaptiveActionAdviceLayout_column_lt basis entry.1.1 entry.1.2 hlayout,
        entry.1.2, hlayout⟩
    · simp only [permutationQueries, List.mem_append] at hpermutation
      rcases hpermutation with hregular | hlast
      · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hregular
        obtain ⟨entry, hentry, hq | hq⟩ := hregular <;> subst q <;> left
        all_goals
          exact ⟨proofIndex.isLt, by
            have := (List.of_mem_zip hentry).2
            simpa using this⟩
      · rw [List.mem_filterMap] at hlast
        obtain ⟨entry, hentry, hentryMap⟩ := hlast
        cases hlastEval : entry.1.2.lastEval with
        | none => simp [hlastEval] at hentryMap
        | some lastEval =>
            simp [hlastEval] at hentryMap
            subst q
            left
            refine ⟨proofIndex.isLt, ?_⟩
            have hindexed : entry ∈
                (List.ofFn (fun s =>
                  (ps.permutationProduct proofIndex s,
                    ps.permutationSetEvals proofIndex s))).zip
                  (List.range (List.ofFn (fun s =>
                    (ps.permutationProduct proofIndex s,
                      ps.permutationSetEvals proofIndex s))).length) := by
              exact List.mem_reverse.mp (List.mem_of_mem_drop hentry)
            have := (List.of_mem_zip hindexed).2
            simpa using this
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, hentry, hq | hq | hq | hq | hq⟩ := hlookup <;> subst q <;> left
      all_goals
        exact ⟨proofIndex.isLt, by
          have := (List.of_mem_zip hentry).2
          simpa using this⟩
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, hentry, rfl⟩ := hfixed
    left
    exact ⟨entry.1.2, (List.of_mem_zip hentry).1⟩
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨entry, hentry, rfl⟩ := hcommon
    left
    have := (List.of_mem_zip hentry).2
    simpa only [adaptiveActionCommitmentActive,
      List.mem_range, List.length_ofFn,
      Halo2.CircuitShape.withProofParams_numPermutationColumns,
      actionCircuit_shape_eq] using this
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- Whether a commitment class has already been absorbed at an Action semantic squeeze. -/
def adaptiveActionCommitmentAvailable (n : Fin 5) : CommitmentId → Prop
  | .instanceCol _ _ | .adviceCol _ _ | .fixedCol _ | .permCommon _ => True
  | .lookupPermInput _ _ | .lookupPermTable _ _ => 1 ≤ (n : Nat)
  | .permProduct _ _ | .lookupProduct _ _ => 3 ≤ (n : Nat)
  | .vanishingH | .randomPoly => False

/-- An active identity available at stage `n` has an explicit point representation in that
stage's source. -/
theorem adaptiveActionActive_point_mem_stage
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (n : Fin 5) (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id)
    (havailable : adaptiveActionCommitmentAvailable n id) :
    let data := (family.adversary basis).run O
    let ch := ActionTerminal.adaptiveActionRunRecord family basis O
    ∃ P,
      assembledCommitment (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          data.algebraicProof.erase ch id = .point P ∧
        ∃ ap ∈ data.algebraicProof.actionRepresentationsBefore n ++
            family.fixedRepresentations basis,
          ap.point = P := by
  simp only
  let data := (family.adversary basis).run O
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let ic := actionCircuit.instanceCommitment urs inputs
  have hvkAt : family.vk basis = ActionTerminal.vkAt basis := by
    simpa only [ActionTerminal.vkAt, Halo2.CircuitShape.withProofParams_k] using hvk basis
  cases id with
  | instanceCol p column =>
      rcases hactive with ⟨hp, rotation, hlayout⟩
      have hlayout' : ∃ rotation,
          (column, rotation) ∈ (family.vk basis).instanceQueryLayout := by
        rw [hvk basis]
        exact ⟨rotation, hlayout⟩
      obtain ⟨ap, hap, hpoint⟩ := family.instanceRepresented basis ⟨p, hp⟩ column
        hlayout'
      refine ⟨ic ⟨p, hp⟩ column, ?_, ap, ?_, ?_⟩
      · rw [assembledCommitment, dif_pos hp]
        apply congrArg CommitmentRef.point
        apply congrArg (fun proof : Fin pp.numProofs => ic proof column)
        exact Fin.ext rfl
      · exact List.mem_append.mpr (Or.inr hap)
      · change ap.point = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs ⟨p, hp⟩ column
        rw [← hI basis]
        exact hpoint
  | adviceCol p column =>
      rcases hactive with ⟨hp, hcolumn, rotation, hlayout⟩
      have hcolumn' : column < actionCircuit.adviceColumnCount := by
        simpa only [Halo2.CircuitShape.withProofParams_numAdviceColumns,
          TopLevelCircuit.adviceColumnCount] using hcolumn
      let ap := data.algebraicProof.adviceCommitments ⟨p, hp⟩ ⟨column, hcolumn⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hcolumn]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        simpa only [ap] using
          data.algebraicProof.adviceCommitment_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨column, hcolumn⟩
  | fixedCol column =>
      rcases hactive with ⟨rotation, hlayout⟩
      have hlayout' : ∃ rotation,
          (column, rotation) ∈ (family.vk basis).fixedQueryLayout := by
        rw [hvk basis]
        exact ⟨rotation, hlayout⟩
      obtain ⟨ap, hap, hpoint⟩ := family.fixedRepresented basis column
        hlayout'
      refine ⟨(ActionTerminal.vkAt basis).fixedCommitment column, rfl,
        ap, List.mem_append.mpr (Or.inr hap), ?_⟩
      rw [← hvkAt]
      exact hpoint
  | permProduct p s =>
      rcases hactive with ⟨hp, hs⟩
      let ap := data.algebraicProof.permutationProduct ⟨p, hp⟩ ⟨s, hs⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hs]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 3 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.permutationProduct_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨s, hs⟩ hn
  | lookupProduct p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupProduct ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 3 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupProduct_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | lookupPermInput p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedInput ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 1 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupPermutedInput_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | lookupPermTable p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedTable ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 1 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupPermutedTable_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | permCommon c =>
      have hactive' :
          c < (actionCircuit.shape.withProofParams pp).numPermutationColumns := by
        simpa only [adaptiveActionCommitmentActive] using hactive
      have hc : c < actionCircuit.permutationColumnCount := by
        simpa only [Halo2.CircuitShape.withProofParams_numPermutationColumns] using
          hactive'
      obtain ⟨ap, hap, hpoint⟩ :=
        family.permutationCommonRepresented basis ⟨c, hactive'⟩
      refine ⟨(ActionTerminal.vkAt basis).permutationCommonCommitment ⟨c, hc⟩,
        ?_, ap, List.mem_append.mpr (Or.inr hap), ?_⟩
      · simp only [assembledCommitment, finFnG, dif_pos hactive']
        congr 2
      · rw [← hvkAt]
        exact hpoint
  | vanishingH => exact False.elim hactive
  | randomPoly => exact False.elim hactive

/-- Executable commitment-ID resolver induced by stage-local point coordinates and explicit
verifier data.  Passing the key and instance commitment as data keeps the terminal finder free of
the noncomputable key-generation wrapper. -/
def adaptiveActionCommitmentPolynomialOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp) :
    CommitmentId → CPoly :=
  let pointPoly := adaptiveActionPointPolynomial source
  fun id =>
    if adaptiveActionCommitmentActive shape vk id then
        match assembledCommitment vk ic ps ch id with
        | .point P => pointPoly P
        | .msm _ => 0
    else 0

/-- Action specialization of the executable commitment resolver. -/
def adaptiveActionCommitmentPolynomial
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    CommitmentId → CPoly :=
  adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch

/-- Supplying the deployed Action key and instance commitment to the executable commitment
resolver recovers the Action-specialized resolver. -/
theorem adaptiveActionCommitmentPolynomialOf_action
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (vk : VerifyingKey actionCircuit.shape Fp VestaG)
    (ic : Fin pp.numProofs → Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hvk : vk = ActionTerminal.vkAt basis)
    (hI : ic = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) :
    adaptiveActionCommitmentPolynomialOf vk ic ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch := by
  subst vk
  subst ic
  simp only [adaptiveActionCommitmentPolynomialOf, adaptiveActionCommitmentPolynomial]
  congr

/-- Every nonterminal commitment resolver is independent of the challenge record; only the
separately handled reassembled quotient slot can depend on `x`. -/
theorem adaptiveActionCommitmentPolynomial_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (id : CommitmentId) (hvanishing : id ≠ .vanishingH) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch₁ id =
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch₂ id := by
  cases id <;>
    simp_all only [adaptiveActionCommitmentPolynomial, adaptiveActionCommitmentPolynomialOf,
      adaptiveActionCommitmentActive,
      adaptiveActionPointPolynomial, assembledCommitment, ne_eq, not_true_eq_false]

/-- The constraint model determined before `y`/`x` by the commitments already in the transcript. -/
def adaptiveActionCommittedModelOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) :
    ConstraintPolyModel shape.numProofs :=
  vk.constraintModel ch
    (adaptiveActionCommitmentPolynomialOf vk ic ps source ch) hblinding

/-- `adaptiveActionCommittedModelOf` at the deployed Action verifying key. -/
def adaptiveActionCommittedModel
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    ConstraintPolyModel (actionCircuit.shape.withProofParams pp).numProofs :=
  adaptiveActionCommittedModelOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- Executable fixed pre-`x` constraint difference.  Every coefficient is computed from the
explicit key, instance commitment, proof, and online AGM coordinate source supplied as data. -/
def adaptiveActionPreXDifferenceOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) : CPoly :=
  let model := adaptiveActionCommittedModelOf vk ic ps source ch hblinding
  combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
      model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta ch.y
      model.chunkLen model.l0 model.lLast model.lBlind
    - committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i))
        * (X ^ vk.n - 1)

/-- Action specialization of the executable fixed pre-`x` difference. -/
def adaptiveActionPreXDifference
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) : CPoly :=
  adaptiveActionPreXDifferenceOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- Supplying the deployed Action key and instance commitment to the executable resolver recovers
the Action-specialized pre-`x` difference. -/
theorem adaptiveActionPreXDifferenceOf_action
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (vk : VerifyingKey (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ic : Fin pp.numProofs → Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hblinding : vk.blindingFactors < vk.n)
    (hvk : vk = ActionTerminal.vkAt basis)
    (hI : ic = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) :
    adaptiveActionPreXDifferenceOf vk ic ps source ch hblinding =
      adaptiveActionPreXDifference pp basis inputs ps source ch := by
  subst vk
  subst ic
  rfl

/-- The executable pre-`x` difference unfolds to the committed constraint identity. -/
theorem adaptiveActionPreXDifferenceOf_eq
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) :
    let model := adaptiveActionCommittedModelOf vk ic ps source ch hblinding
    adaptiveActionPreXDifferenceOf vk ic ps source ch hblinding =
      combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind -
        committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i)) *
          (X ^ vk.n - 1) := rfl

/-- The stage-`x` difference is exactly the constraint difference of the stage-local canonical
model with the genuinely pre-`x` quotient polynomial. -/
theorem adaptiveActionPreXDifference_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    let vk := ActionTerminal.vkAt basis
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    adaptiveActionPreXDifference pp basis inputs ps source ch =
      combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind -
        committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i)) *
          (X ^ vk.n - 1) := by
  exact adaptiveActionPreXDifferenceOf_eq (shape := actionCircuit.shape.withProofParams pp)
    (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- The stage-local model reads only `theta`, `beta`, and `gamma`; later challenge fields do not
affect its constraint polynomials. -/
theorem adaptiveActionCommittedModel_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (hgamma : ch₁.gamma = ch₂.gamma) :
    adaptiveActionCommittedModel pp basis inputs ps source ch₁ =
      adaptiveActionCommittedModel pp basis inputs ps source ch₂ := by
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
  have hpoly : adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps source ch₁ =
    adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps source ch₂ := by
    funext id
    by_cases hvanishing : id = .vanishingH
    · subst id
      simp [adaptiveActionCommitmentPolynomialOf,
        adaptiveActionCommitmentActive]
    · exact adaptiveActionCommitmentPolynomial_challenge_congr
        pp basis inputs ps source ch₁ ch₂ id hvanishing
  unfold VerifyingKey.constraintModel constraintModelOfResolver
  dsimp only
  rw [hpoly, htheta, hbeta, hgamma]

/-- The canonical constraint model never reads the quotient or random-polynomial terminal slots,
so pointwise agreement on every other identity determines the whole model. -/
theorem VerifyingKey.constraintModel_congr_nonterminal
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly₁ poly₂ : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
      poly₁ id = poly₂ id) :
    vk.constraintModel (numProofs := numProofs) ch poly₁ hblinding =
      vk.constraintModel (numProofs := numProofs) ch poly₂ hblinding := by
  have hcolumn : ∀ id, id.isColumnInput → poly₁ id = poly₂ id := by
    intro id hid
    apply hpoly id <;> cases id <;> simp_all [CommitmentId.isColumnInput]
  have hpermutation : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id := by
    intro id hid
    apply hpoly id <;> cases id <;> simp_all [CommitmentId.isPermutationInput]
  have hfixed : fixedQueryFeedOfResolver vk poly₁ =
      fixedQueryFeedOfResolver vk poly₂ :=
    fixedQueryFeedOfResolver_congr vk hcolumn
  have hadvice : adviceQueryFeedOfResolver vk poly₁ =
      adviceQueryFeedOfResolver vk poly₂ := by
    funext p
    exact adviceQueryFeedOfResolver_congr vk p hcolumn
  have hinstance : instanceQueryFeedOfResolver vk poly₁ =
      instanceQueryFeedOfResolver vk poly₂ := by
    funext p
    exact instanceQueryFeedOfResolver_congr vk p hcolumn
  have hsets : permutationSetsOfResolver (numProofs := numProofs) vk poly₁ =
      permutationSetsOfResolver (numProofs := numProofs) vk poly₂ := by
    funext p
    unfold permutationSetsOfResolver
    apply congrArg List.ofFn
    funext s
    unfold permutationSetOfResolver
    rw [hpoly (.permProduct p s) (by simp) (by simp)]
  have hchunks : permutationChunksOfResolver (numProofs := numProofs) vk poly₁ =
      permutationChunksOfResolver (numProofs := numProofs) vk poly₂ := by
    funext p
    unfold permutationChunksOfResolver
    rw [hsets]
    apply List.map_congr_left
    intro sc hsc
    apply Prod.ext
    · rfl
    · apply List.map_congr_left
      intro cr hcr
      exact Prod.ext
        (permutationColumnPolynomialOfResolver_congr vk p
          (fun id hid => hpermutation id hid.toPermutation) cr.1)
        (hpoly (.permCommon cr.2) (by simp) (by simp))
  have hlookups : lookupEntriesOfResolver vk poly₁ =
      lookupEntriesOfResolver vk poly₂ := by
    funext p
    unfold lookupEntriesOfResolver
    apply congrArg List.ofFn
    funext l
    rw [hpoly (.lookupProduct p l) (by simp) (by simp),
      hpoly (.lookupPermInput p l) (by simp) (by simp),
      hpoly (.lookupPermTable p l) (by simp) (by simp)]
  unfold VerifyingKey.constraintModel constraintModelOfResolver
  dsimp only
  rw [hfixed, hadvice, hinstance, hsets, hchunks, hlookups]

/-- A plain commitment routed by an accepting adaptive decode carries the polynomial fixed by
the run's online pre-`x` AGM source. -/
theorem adaptiveAcceptedPolynomial_eq_online_of_query
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (rounds : Fin shape.k → Fp)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (witness : DeployedBatchWitness family basis pnu)
    (hsrc : witness.fixedRepresentations = fixed)
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) < Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds))
    (id : CommitmentId) (q : VerifierQuery shape.k Fp VestaG)
    (hq : q ∈ assembleQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds))
    (hqid : q.commId = id) (P : VestaG)
    (hpoint : assembledCommitment (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) id = .point P) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => (decode.reRound rounds).toMemberDecode hchar i hi)
        haccepts id =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis)
    pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds) haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := family.instanceCommitment basis)
    (family.vk basis) pnu.1.proof.1
    (chRecord (wrappedPreIpaReads pnu) rounds) routing.1 routing.2 q hq
  have hmemberPoint : ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) routed.slot.setIndex).getD
        (routed.slot.memberIndex : Nat) (.point 0, [])).1 = .point P := by
    rw [deployed_member_commitment_eq_assembled
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) rounds) routed.slot.setIndex
        routed.slot.memberIndex CommitmentId.vanishingH
        (assembledQueryMemberRoute_id
          (instanceCommitment := family.instanceCommitment basis)
          (family.vk basis) pnu.1.proof.1
          (chRecord (wrappedPreIpaReads pnu) rounds)
          routing.1 routing.2 id routed.slot
          (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid]
            using routed.route_eq)) (.point 0, [])]
    exact hpoint
  have hmember : (decode.reRound rounds).memberPoly
        routed.slot.setIndex routed.slot.setIndex_lt
        routed.slot.memberIndex =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
    change decode.memberPoly routed.slot.setIndex routed.slot.setIndex_lt
      routed.slot.memberIndex = _
    unfold DeployedAlgebraicDecode.memberPoly onlinePointPolynomial
    rw [hbatches, ← hsrc]
    rw [congrFun (witness.memberCoeffs routed.slot.setIndex routed.slot.setIndex_lt)
      routed.slot.memberIndex]
    exact congrArg coeffsToPoly
      (deployedMemberRepresentationsOfCovered_coeffs_point
        pnu.1
        witness.fixedRepresentations witness.membersCovered
        (wrappedPreIpaReads pnu)
        routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex P hmemberPoint)
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts id =
      some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  exact hmember

/-- Compare one stage-local representation with the deterministic first representation of the
same point in the complete pre-`x` source. -/
def representationAgainstSourceMismatch?
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ap : AlgebraicPoint (F := Fp) basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match hfound : source.find? (fun candidate => candidate.point = ap.point) with
  | none => none
  | some first => representationMismatchRelation? first ap (by
      simpa using List.find?_some hfound)

/-- Return the first mismatch between a stage source and the complete pre-`x` source. -/
def representationSourceMismatchFinder
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (target.map (representationAgainstSourceMismatch? source))

/-- With no source-collision relation, deterministic point lookup gives the same polynomial in
the stage source and the complete pre-`x` source. -/
theorem onlinePointPolynomial_eq_of_sourceMismatch_none
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis))
    (hsub : ∀ ap ∈ target, ap ∈ source)
    (hnone : representationSourceMismatchFinder source target = none)
    (P : VestaG) (hP : ∃ ap ∈ target, ap.point = P) :
    onlinePointPolynomial source P = onlinePointPolynomial target P := by
  obtain ⟨ap, hap, rfl⟩ := hP
  have htargetSome : (target.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨ap, hap, by simp⟩
  obtain ⟨stage, hstage⟩ := Option.isSome_iff_exists.mp htargetSome
  have hstageMem : stage ∈ target := List.mem_of_find?_eq_some hstage
  have hstagePoint : stage.point = ap.point := by
    simpa using List.find?_some hstage
  have hsourceSome : (source.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨stage, hsub stage hstageMem, by simp [hstagePoint]⟩
  obtain ⟨first, hfirst⟩ := Option.isSome_iff_exists.mp hsourceSome
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  have hmismatch : representationAgainstSourceMismatch? source stage = none := by
    apply hall
    exact List.mem_map.mpr ⟨stage, hstageMem, rfl⟩
  have hfirstStage : source.find? (fun candidate => candidate.point = stage.point) =
      some first := by
    simpa only [hstagePoint] using hfirst
  have hcoeff : first.coeffs = stage.coeffs := by
    unfold representationAgainstSourceMismatch? at hmismatch
    split at hmismatch
    · rename_i hnone
      rw [hfirstStage] at hnone
      contradiction
    · rename_i found hfound
      have hfoundEq : found = first := Option.some.inj (hfound.symm.trans hfirstStage)
      subst found
      exact (representationMismatchRelation?_eq_none_iff first stage (by
        simpa using List.find?_some hfirstStage)).1 hmismatch
  unfold onlinePointPolynomial onlinePointCoordinates
  rw [hfirst, hstage]
  apply congrArg coeffsToPoly
  funext i
  exact congrFun hcoeff (AugmentedIndex.gen i)

/-- One of the five exact Action semantic bad sets, reconstructed only from the stage prefix,
earlier oracle answers, and stage-local AGM coordinates. -/
def adaptiveActionSurfaceAt
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch := chRecord nu (fun _ => 0)
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let vk := ActionTerminal.vkAt basis
  let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
  if _h0 : (n : Nat) = 0 then
    ↑(TopLevelLookup.thetaBadSet
      actionCircuit pp urs poly)
  else if _h1 : (n : Nat) = 1 then
    ↑(allResolverPermutationBetaBadSet pp.numProofs vk poly actionActiveRows) ∪
      ↑(allResolverLookupBetaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k)) poly
        (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h2 : (n : Nat) = 2 then
    ↑(allResolverPermutationGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) poly actionActiveRows) ∪
      ↑(allResolverLookupGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) poly
          (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h3 : (n : Nat) = 3 then
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    ⋃ j, ↑(szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
  else
    ↑(szBadSet (adaptiveActionPreXDifference pp basis inputs ps source ch))

/-- Equality of one exact semantic prefix pins precisely the ordinary commitment list used by
that stage. -/
theorem actionCommitmentPointsBefore_eq_of_prefix
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 5)
    (ps ps' : ProofString shape Fp VestaG)
    (hprefix : preIpaSqueezePoints init ps (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n)) :
    ps.actionCommitmentPointsBefore n = ps'.actionCommitmentPointsBefore n := by
  fin_cases n
  · have h := preThetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, h]
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr]
  · obtain ⟨ha, hi, ht, hp, hl, hr, hh⟩ := preXSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr, hh]

/-- Equal sources and advice commitments agree on every active column input. -/
theorem adaptiveActionCommitmentPolynomial_column_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isColumnInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isColumnInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

/-- Equal pre-lookup data agree on every active lookup input. -/
theorem adaptiveActionCommitmentPolynomial_lookup_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable) :
    ∀ id, id.isLookupInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isLookupInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

/-- Equal sources and advice commitments agree on every permutation input. -/
theorem adaptiveActionCommitmentPolynomial_permutation_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isPermutationInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isPermutationInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

/-- The pre-`y` proof fields determine the complete Action commitment resolver. -/
theorem adaptiveActionCommitmentPolynomial_eq_of_preY_fields
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source')
    (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable)
    (hperm : ps.permutationProduct = ps'.permutationProduct)
    (hlookup : ps.lookupProduct = ps'.lookupProduct)
    (hrandom : ps.vanishingRandom = ps'.vanishingRandom) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch := by
  funext id
  subst source'
  cases id <;>
    simp [adaptiveActionCommitmentPolynomial, adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial,
      assembledCommitment, hadvice, hinput, htable, hperm, hlookup, hrandom]

/-- Equal exact prefixes and equal stage-local coordinates define the same semantic bad set. -/
theorem adaptiveActionSurfaceAt_congr
    (pp : ProofParams)
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (_hwf : PsWellFormed ps) (_hwf' : PsWellFormed ps')
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp)
    (hprefix : preIpaSqueezePoints init ps
        (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n))
    (hsource : source = source') :
    adaptiveActionSurfaceAt pp basis inputs n ps source earlier =
      adaptiveActionSurfaceAt pp basis inputs n ps' source' earlier := by
  subst source'
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord nu (fun _ => 0)
  fin_cases n
  · have ha := preThetaSqueezePoint_inj init hprefix
    have hp := adaptiveActionCommitmentPolynomial_column_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hs := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (TopLevelLookup.thetaBadSet_congr
        actionCircuit pp
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) hp)
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationBetaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupBetaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationGammaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupGammaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      change adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps source ch =
        adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps' source ch at hpoly
      unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      rw [hpoly]
    have hs := congrArg (fun model : ConstraintPolyModel
        pp.numProofs =>
      ⋃ j, (↑(szBadSet (foldSplitWitness model.constraints
        actionCircuit.n j)) : Set Fp)) hmodel
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht, hp, hl, _hr, hh⟩ := preXSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl _hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      change adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps source ch =
        adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps' source ch at hpoly
      unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      rw [hpoly]
    have hdifference :
        adaptiveActionPreXDifference pp basis inputs ps source ch =
          adaptiveActionPreXDifference pp basis inputs ps' source ch := by
      rw [adaptiveActionPreXDifference_eq, adaptiveActionPreXDifference_eq]
      rw [hmodel, hh]
    have hs := congrArg
      (fun polynomial : CPoly => (↑(szBadSet polynomial) : Set Fp)) hdifference
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs

theorem adaptiveActionPreXDifference_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (hgamma : ch₁.gamma = ch₂.gamma) (hy : ch₁.y = ch₂.y) :
    adaptiveActionPreXDifference pp basis inputs ps source ch₁ =
      adaptiveActionPreXDifference pp basis inputs ps source ch₂ := by
  have hmodel := adaptiveActionCommittedModel_challenge_congr
    pp basis inputs ps source ch₁ ch₂ htheta hbeta hgamma
  rw [adaptiveActionPreXDifference_eq, adaptiveActionPreXDifference_eq]
  rw [hmodel, hy]

end Zcash.Snark
