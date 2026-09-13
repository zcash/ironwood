import Zcash.Snark.ZeroKnowledge.ActionDigest
import Zcash.Snark.ZeroKnowledge.PlonkOracle
import Zcash.Common.Probability.SimulationAgreement

/-!
# One Action-bundle attempt against a cached raw random oracle

The public initialization is the existing verifier's key representative and
compiler-generated instance commitments. Private fields follow the original
wide-reduced law. Fresh oracle answers are independent uniform 512-bit words;
cached answers are reused. The witness-free simulator recovers raw digests and
programs only previously unanswered addresses.

These experiments expose the retained attempt result and final oracle cache.
The simulator's programming failure is represented by `none`; the real bounded
execution always has enough reply slots. The numerical conflict bound and
adversarial preprocessing/postprocessing are added separately.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The existing verifier's common-input prefix, with the actual Action instance commitments. -/
def actionOracleInitial {actions : ℕ} (urs : URS VestaG) (vkTranscriptRepr : Fp)
    (inputs : Fin actions → PublicInputs Fp) : List (TranscriptElt Fp VestaG) :=
  initialTranscript (shape := plonkProofShape actions urs.k) vkTranscriptRepr
    (actionCircuit.instanceCommitment urs inputs)

/-- The independent reply slots and complete private field tape for one reference attempt. -/
abbrev ActionOracleTape (actions k : ℕ) :=
  PlonkChallengeTape k (Fin challengeDigestCard) × (Fin (fieldSampleCount actions) → Fp)

/-- Uniform raw reply slots and the exact wide-reduced private-field distribution. -/
noncomputable def actionOracleTapeLaw (actions k : ℕ) : PMF (ActionOracleTape actions k) :=
  Zcash.independentProductPMF (PMF.uniformOfFintype (PlonkChallengeTape k (Fin challengeDigestCard)))
    (independentTapeLaw fieldSample (fieldSampleCount actions))

/-- Project a common pair of tapes to the complete typed reference proof and raw digests. -/
def actionOracleDigestView {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (tapes : ActionOracleTape actions urs.k) :
    PlonkChallengeTape urs.k (Fin challengeDigestCard) × PlonkFreshView actions urs.k VestaG :=
  let ch := plonkChallengesFromTape (fun i => ((tapes.1 i).val : Fp))
  (tapes.1, (ch, plonkReferenceProofFromTape urs hk
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness ch tapes.2))

/-- This projection has exactly the already proved complete Action raw-digest law. -/
theorem actionOracleDigestView_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    (actionOracleTapeLaw actions urs.k).map (actionOracleDigestView urs hk inputs witness) =
      actionZkDigestProver urs hk inputs witness := by
  simp only [actionOracleTapeLaw, Zcash.independentProductPMF, actionOracleDigestView,
    actionZkDigestProver, rawDigestChallengeExperiment, sampleFieldsWith_eq_independentTape,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Erasing the raw replies leaves exactly the wide-reduced typed prover used by the acceptance theorem. -/
theorem actionOracleTypedTape_law [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    (actionOracleTapeLaw actions urs.k).map (fun tapes =>
      (actionOracleDigestView urs hk inputs witness tapes).2) = actionZkTypedProver urs hk inputs witness := by
  change (actionOracleTapeLaw actions urs.k).map
    (Prod.snd ∘ actionOracleDigestView urs hk inputs witness) = _
  rw [← PMF.map_comp, actionOracleDigestView_law, ← actionZkTypedProver_digest_law]
  simp only [attachPlonkDigests, liftDigestTapeView, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  calc
    _ = (actionZkTypedProver urs hk inputs witness).bind PMF.pure :=
      congrArg (PMF.bind (actionZkTypedProver urs hk inputs witness))
        (funext fun view => PMF.map_const _ view)
    _ = _ := PMF.bind_pure _

/-- The actual Action reference computation with the statement's common-input prefix. -/
def actionOracleComp {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (privateTape : Fin (fieldSampleCount actions) → Fp) (vkTranscriptRepr : Fp) :
    OracleComp TranscriptHashAddress (Fin challengeDigestCard) ProverAttemptResult :=
  plonkReferenceOracleComp urs hk
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness privateTape (actionOracleInitial urs vkTranscriptRepr inputs)

/-- The complete Action oracle program respects its original twenty-two-reply budget. -/
theorem actionOracleComp_queryBound {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (privateTape : Fin (fieldSampleCount actions) → Fp) (vkTranscriptRepr : Fp) :
    (actionOracleComp urs hk inputs witness privateTape vkTranscriptRepr).QueryBound (urs.k + 11) :=
  plonkReferenceOracleComp_queryBound _ _ _ _ _ _ _

/-- Evaluate the real cached oracle on the same pair of tapes used by the reference projection. -/
def actionOracleRunTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (tapes : ActionOracleTape actions urs.k) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  cachedOracleRunTape (urs.k + 11) (actionOracleComp urs hk inputs witness tapes.2 vkTranscriptRepr) cache tapes.1

/-- One real proof attempt with lazy, consistent raw oracle answers. -/
noncomputable def actionOracleProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  (independentTapeLaw fieldSample (fieldSampleCount actions)).bind fun privateTape =>
    (cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (actionOracleComp urs hk inputs witness privateTape vkTranscriptRepr) cache).map some

/-- The common finite-tape execution has exactly the real cached-oracle distribution. -/
theorem actionOracleRunTape_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (actionOracleTapeLaw actions urs.k).map (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache) =
      actionOracleProver urs hk inputs witness vkTranscriptRepr cache := by
  simp only [actionOracleTapeLaw, Zcash.independentProductPMF, actionOracleRunTape,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  calc
    _ = (independentTapeLaw fieldSample (fieldSampleCount actions)).bind (fun privateTape =>
        (PMF.uniformOfFintype (PlonkChallengeTape urs.k (Fin challengeDigestCard))).map
          (cachedOracleRunTape (urs.k + 11)
            (actionOracleComp urs hk inputs witness privateTape vkTranscriptRepr) cache)) :=
      PMF.bind_comm _ _ _
    _ = _ := congrArg (PMF.bind (independentTapeLaw fieldSample (fieldSampleCount actions)))
      (funext fun privateTape => by
        simpa only [independentTapeLaw_uniform] using
          cachedOracleRunTape_law (PMF.uniformOfFintype (Fin challengeDigestCard))
            (actionOracleComp_queryBound urs hk inputs witness privateTape vkTranscriptRepr) cache)

/-- Program the exact query prefix from a public raw-digest proof view, preserving every prior answer. -/
def actionOracleProgramView {actions : ℕ} (urs : URS VestaG) (vkTranscriptRepr : Fp)
    (inputs : Fin actions → PublicInputs Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (view : PlonkChallengeTape urs.k (Fin challengeDigestCard) × PlonkFreshView actions urs.k VestaG) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  programOracleView cache (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) view.1 view.2.2)

/-- Distinct transcript addresses can always be installed in a fresh oracle cache. -/
theorem actionOracleProgramView_empty_ne_none {actions : ℕ}
    (urs : URS VestaG) (vkTranscriptRepr : Fp) (inputs : Fin actions → PublicInputs Fp)
    (view : PlonkChallengeTape urs.k (Fin challengeDigestCard) × PlonkFreshView actions urs.k VestaG) :
    actionOracleProgramView urs vkTranscriptRepr inputs [] view ≠ none := by
  have hgood := programOracleTrace_ne_none_of_fresh
    (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) view.1 view.2.2).2 []
    (plonkRawOracleView_queries_nodup _ _ _) (by intro query hquery; simp)
  simpa only [actionOracleProgramView, programOracleView, ne_eq, Option.map_eq_none_iff] using hgood

/-- The oracle simulator takes only public data and the preexisting oracle cache. -/
noncomputable def actionOracleSimulator [Fintype VestaG] {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  (actionZkDigestSimulator urs hk inputs).map (actionOracleProgramView urs vkTranscriptRepr inputs cache)

/-- The real and programmed observations agree on the same tapes whenever programming succeeds. -/
theorem actionOracleRunTape_eq_programmed {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (tapes : ActionOracleTape actions urs.k)
    (hgood : actionOracleProgramView urs vkTranscriptRepr inputs cache
      (actionOracleDigestView urs hk inputs witness tapes) ≠ none) :
    actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache tapes =
      actionOracleProgramView urs vkTranscriptRepr inputs cache (actionOracleDigestView urs hk inputs witness tapes) := by
  have hreplay := plonkReferenceOracleComp_replay urs hk
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness tapes.2 (actionOracleInitial urs vkTranscriptRepr inputs) tapes.1
  change freshOracleRunTape (urs.k + 11)
    (actionOracleComp urs hk inputs witness tapes.2 vkTranscriptRepr) tapes.1 = _ at hreplay
  have h := cachedOracleRunTape_eq_programmed (urs.k + 11)
    (actionOracleComp urs hk inputs witness tapes.2 vkTranscriptRepr) cache tapes.1 (by
      rw [hreplay, Option.bind_some]
      exact hgood)
  rw [hreplay, Option.bind_some] at h
  exact h

/-- The full Action simulation is charged once; only the simulator's oracle-conflict probability remains. -/
theorem actionOracle_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := plonkSimulationErrorBound actions + (actionZkDigestSimulator urs hk inputs).toOuterMeasure
      {view | actionOracleProgramView urs vkTranscriptRepr inputs cache view = none}
    PMFEventBiasLE (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleSimulator urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionOracleSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs witness vkTranscriptRepr cache) error := by
  have hsim := wideActionZkDigest_simulation_error_bound urs hk inputs witness hvalid hW
  rw [← actionOracleDigestView_law urs hk inputs witness] at hsim
  have h := simulation_map_of_agree (actionOracleTapeLaw actions urs.k)
    (actionOracleDigestView urs hk inputs witness) (actionZkDigestSimulator urs hk inputs)
    (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache)
    (actionOracleProgramView urs vkTranscriptRepr inputs cache)
    {view | actionOracleProgramView urs vkTranscriptRepr inputs cache view = none}
    hsim.1 hsim.2 (fun tapes _ hgood => actionOracleRunTape_eq_programmed urs hk inputs witness vkTranscriptRepr cache tapes hgood)
  rw [actionOracleRunTape_law] at h
  exact h

end Zcash.Snark.ZeroKnowledge
