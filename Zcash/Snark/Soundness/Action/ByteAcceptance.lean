import Zcash.Snark.Soundness.Action.AdaptiveStatementTerminal
import Zcash.Snark.Verifier.KeyDigest
import Zcash.Snark.Verifier.ProofBytes

/-!
# Byte acceptance for the adaptive Action family

This module connects the concrete Lean byte reader and BLAKE2b transcript to the typed acceptance
predicate used by the adaptive-statement soundness capstone.  It deliberately stops at Lean's raw
entry point: identifying an independently compiled Rust verifier with this predicate is stated in
`DeploymentRecord.lean` as a separate refinement assumption.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

local instance byteAcceptanceVestaInhabited : Inhabited VestaG := ⟨0⟩

/-- The exact Action public-instance columns selected by an adaptive-statement output. -/
def adaptiveActionStatementRawInstances (pp : ProofParams)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    RawInstances (AdaptiveActionStatementShape pp) Fp :=
  fun p ↦ List.ofFn fun column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns ↦
    actionCircuit.publicInputRows (inputs p) ⟨column⟩

/-- The Lagrange-basis commitment operation used for those raw columns. -/
def adaptiveActionStatementCommitColumn (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (rows : List Fp) : VestaG :=
  (actionCircuit.instanceCommitmentKey
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).commitInstance rows 1

/-- Canonical Action raw instances contain exactly the one configured instance column. -/
theorem adaptiveActionStatementRawInstances_have_expected_column_count (pp : ProofParams)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    InstancesHaveExpectedColumnCount (adaptiveActionStatementRawInstances pp inputs) := by
  intro p
  simp [adaptiveActionStatementRawInstances]

/-- Canonical Action raw instances fit inside Halo2's usable row prefix. -/
theorem adaptiveActionStatementRawInstances_columns_fit (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    InstanceColumnsFit (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementRawInstances pp inputs) := by
  intro p column
  have hlen : (adaptiveActionStatementRawInstances pp inputs p).length = 1 :=
    (adaptiveActionStatementRawInstances_have_expected_column_count pp inputs p).trans
      (adaptiveActionStatement_numInstanceColumns pp)
  have hcolumnVal : column.val = 0 := by
    have hlt := column.isLt
    omega
  have hzeroLt : 0 < (adaptiveActionStatementRawInstances pp inputs p).length := by omega
  have hcolumn : column = ⟨0, hzeroLt⟩ :=
    Fin.ext hcolumnVal
  rw [hcolumn]
  simp only [adaptiveActionStatementRawInstances, List.get_ofFn]
  change (actionCircuit.publicInputRows (inputs p) ⟨0⟩).length ≤
    instanceUsableRows (adaptiveActionStatementVk pp basis)
  rw [actionCircuit_publicInputRows_zero]
  norm_num [instanceUsableRows, adaptiveActionStatementVk,
    actionCircuit.toVerifierKey_n, actionCircuit.toVerifierKey_blindingFactors,
    actionCircuit.n_eq_two_pow_domainExponent,
    actionCircuit_domainExponent_eq, actionCircuit_blindingFactors_eq]
  change 10 ≤ 2042
  norm_num

/-- The validator's canonical successful result for Action public inputs. -/
def adaptiveActionStatementValidatedInstances (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    ValidatedInstances (adaptiveActionStatementVk pp basis) :=
  ⟨adaptiveActionStatementRawInstances pp inputs,
    adaptiveActionStatementRawInstances_have_expected_column_count pp inputs,
    adaptiveActionStatementRawInstances_columns_fit pp basis inputs⟩

/-- Validation returns the canonical validated Action columns. -/
theorem validate_adaptiveActionStatementRawInstances (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    validateInstances? (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementRawInstances pp inputs) =
      some (adaptiveActionStatementValidatedInstances pp basis inputs) := by
  simp [validateInstances?, adaptiveActionStatementValidatedInstances,
    adaptiveActionStatementRawInstances_have_expected_column_count,
    adaptiveActionStatementRawInstances_columns_fit]

/-- Commitments derived from the validated raw columns are exactly the typed commitment family
used by `ComputedAdaptiveActionStatementFSFamily.accepts`, including total-function indices beyond
the one configured column. -/
theorem adaptiveActionStatementValidatedInstances_commitments (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    (adaptiveActionStatementValidatedInstances pp basis inputs).commitments
        (adaptiveActionStatementCommitColumn pp basis) =
      adaptiveActionStatementInstanceCommitment pp basis inputs := by
  funext p column
  change adaptiveActionStatementCommitColumn pp basis
      ((adaptiveActionStatementRawInstances pp inputs p).getD column []) =
    actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) inputs p column
  by_cases hcolumn : column = 0
  · subst column
    have hrows : (adaptiveActionStatementRawInstances pp inputs p).getD 0 [] =
        actionCircuit.publicInputRows (inputs p) ⟨0⟩ := by
      simp [adaptiveActionStatementRawInstances, actionCircuit_numInstanceColumns_eq]
    rw [hrows]
    exact (actionCircuit.instanceCommitment_column pp
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) inputs p ⟨0⟩).symm
  · have hget :
        ((adaptiveActionStatementRawInstances pp inputs p).getD column []) = [] := by
      apply List.getD_eq_default
      simp only [adaptiveActionStatementRawInstances, List.length_ofFn]
      rw [adaptiveActionStatement_numInstanceColumns]
      exact Nat.one_le_iff_ne_zero.mpr hcolumn
    rw [hget]
    change (actionCircuit.instanceCommitmentKey
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).commitInstance [] 1 =
      (actionCircuit.instanceCommitmentKey
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).commitInstance
        (actionCircuit.publicInputRows (inputs p) ⟨column⟩) 1
    rw [adaptiveCommitInstance_of_rows_zero _ (fun _ ↦ by simp),
      adaptiveCommitInstance_of_rows_zero _
        (actionCircuit_publicInputRows_ne_zero _ hcolumn)]

/-- The bounded random-oracle table obtained by evaluating Halo2's concrete BLAKE2b squeeze. -/
def ComputedAdaptiveActionStatementFSFamily.halo2Coins {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : family.Coins :=
  fun transcript ↦ halo2Transcript.squeeze transcript.val

/-- At `halo2Coins`, the family's materialized challenge record is exactly the concrete deployed
BLAKE2b schedule, provided its opaque canonical-key representation is the pinned-key digest. -/
theorem ComputedAdaptiveActionStatementFSFamily.runRecord_halo2Coins
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (pinnedVkDescription : String)
    (hdigest : family.vkTranscriptRepr basis = keyDigest pinnedVkDescription) :
    family.runRecord basis family.halo2Coins =
      deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
        (adaptiveActionStatementInstanceCommitment pp basis
          (family.runOutput basis family.halo2Coins).inputs)
        (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1 := by
  rw [family.runRecord_eq_roChallenges]
  rw [← hdigest]
  change roChallenges (extendO family.halo2Coins)
      ((family.runOutput basis family.halo2Coins).init (family.vkTranscriptRepr basis))
      (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1 =
    roChallenges halo2Transcript.squeeze
      ((family.runOutput basis family.halo2Coins).init (family.vkTranscriptRepr basis))
      (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1
  rw [roChallenges_eq_chRecord, roChallenges_eq_chRecord]
  apply congrArg₂ chRecord
  · funext i
    simp only [extendO]
    have hpre := ((family.runOutput basis family.halo2Coins).prefixesPre
      (family.vkTranscriptRepr basis) i).prop
    change (preIpaSqueezePoints
        ((family.runOutput basis family.halo2Coins).init (family.vkTranscriptRepr basis))
        (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1 i).length ≤
      preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (AdaptiveActionStatementShape pp).k at hpre
    rw [dif_pos hpre]
    rfl
  · funext j
    simp only [extendO]
    have hround := ((family.runOutput basis family.halo2Coins).prefixes
      (family.vkTranscriptRepr basis) j).prop
    change (roundTranscriptFin
        (preIpaTranscript
          ((family.runOutput basis family.halo2Coins).init (family.vkTranscriptRepr basis))
          (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1)
        (family.runOutput basis family.halo2Coins).toAlgebraicWfProof.proof.1.ipaRounds
          j).length ≤
      preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (AdaptiveActionStatementShape pp).k at hround
    rw [dif_pos hround]
    rfl

/-- Lean byte acceptance specialized to the exact raw statement and typed algebraic proof selected
by a family run.  The explicit parse equality is the byte-to-AGM representation edge: it says that
the universally quantified bytes decode to this run's represented proof, not merely to some typed
proof. -/
def ComputedAdaptiveActionStatementFSFamily.acceptsBytes {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (pinnedVkDescription : String) (proofBytes : List UInt8) : Prop :=
  let output := family.runOutput basis family.halo2Coins
  DeployedAcceptsRawBytes (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis) (adaptiveActionStatementVk pp basis)
      pinnedVkDescription (adaptiveActionStatementRawInstances pp output.inputs)
      (adaptiveActionStatementCommitColumn pp basis) proofBytes ∧
    (readProof? (AdaptiveActionStatementShape pp)).run proofBytes =
      some (output.toAlgebraicWfProof.proof.1, [])

/-- **Lean byte acceptance implies the existing typed family acceptance.**  No replacement or
second definition of `family.accepts` is introduced: validation derives the same commitments,
exact parsing identifies the proof, and the concrete BLAKE2b table derives the same challenges. -/
theorem ComputedAdaptiveActionStatementFSFamily.accepts_of_acceptsBytes
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (pinnedVkDescription : String) (proofBytes : List UInt8)
    (hdigest : family.vkTranscriptRepr basis = keyDigest pinnedVkDescription)
    (hbytes : family.acceptsBytes basis pinnedVkDescription proofBytes) :
    family.accepts basis family.halo2Coins := by
  let output := family.runOutput basis family.halo2Coins
  rcases hbytes with ⟨hraw, hreadOutput⟩
  rcases deployedAcceptsRawBytes_canonical hraw with
    ⟨valid, hvalid, _hdesc, _hne, ps, hread, _hserialize, haccepts⟩
  have hvalidCanonical := validate_adaptiveActionStatementRawInstances pp basis output.inputs
  have hvalidEq : valid = adaptiveActionStatementValidatedInstances pp basis output.inputs := by
    rw [hvalidCanonical] at hvalid
    exact Option.some.inj hvalid.symm
  subst valid
  have hps : ps = output.toAlgebraicWfProof.proof.1 := by
    rw [hreadOutput] at hread
    exact (congrArg Prod.fst (Option.some.inj hread)).symm
  subst ps
  rw [adaptiveActionStatementValidatedInstances_commitments] at haccepts
  rw [← family.runRecord_halo2Coins basis pinnedVkDescription hdigest] at haccepts
  exact haccepts

end Zcash.Snark
