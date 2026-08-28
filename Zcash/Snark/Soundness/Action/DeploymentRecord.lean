import Zcash.Snark.Soundness.Action.AdaptiveStatementProfile
import Zcash.Snark.Soundness.Action.ByteAcceptance
import Zcash.Snark.Soundness.Oracle.Challenge255

/-!
# The deployment-instantiation record

The Action capstones are exact inside their stated model; interpreting them as claims about the
deployed verifier requires identifying each modeled ingredient with its deployed counterpart.
`ActionDeploymentInstantiation` is that bridge as one machine-readable surface: a field per
floor, each stating the identification against the development's own definitions, with the
deployed objects carried as record data.  Its finite failure observer is deduplicated before the
proved Challenge255 hybrid is applied, so one record supplies a *joint* deployed experiment rather
than an insufficient per-squeeze event bound, and its query budget is certified tight, so the
hybrid's per-query charge totals a closed number rather than a free multiple.
`Capstones/Action.lean` consumes the record and derives the deployed knowledge-failure bound.  No
term is constructed here, and fields whose floors are intentionally permanent say so in their
docstrings.

The adversary-class restriction — deployed provers are modeled as represented online-AGM
programs — is carried by `ComputedAdaptiveActionStatementFSFamily` itself, the type the record
is parameterized over, so it appears as the record's parameter rather than as a field.
The idealized typed observer/table equality is deliberately separate from production parsing.
Production acceptance, proof bytes, and raw instance columns are named below, and the one-way
`rustAcceptsRefinesLeanRaw` field states the universal Rust-to-Lean deployment assumption
explicitly. `rustAcceptedProofRepresented` is the distinct algebraic-group-model edge connecting
an accepted decoded proof to the represented proof selected by the family.  The honest captures
exercise the Lean side on finite examples; they do not prove either universal field.
-/

namespace Zcash.Snark

open Zcash.Common

open scoped ENNReal
open Halo2
open Zcash.Circuits.Action

local instance deploymentRecordVestaInhabited : Inhabited VestaG := ⟨0⟩

/-- One deployment interpretation of the adaptive Action capstones: the deployed challenge law,
basis law, key digest, acceptance predicate, DLOG profile, and complete finite failure observer,
each identified with its modeled counterpart.

Fields split by status.  `challengeLawIsChallenge255` identifies the typed deployed conversion
with `challenge255`; `challenge255_joint_eventBias_le` then discharges the adaptive joint hybrid,
with only the permanent BLAKE2b-to-uniform-digest floor behind that identification, and
`challengeQueryBound_le` keeps the budget that hybrid is charged per query no looser than the
experiment's own envelope. `basisIsGeneratorRO`
is the GroupHash-as-random-oracle idealization, permanent up to the encoding-distribution
groundwork.  `vkDigestAgreesOnCanonical` binds the family's opaque digest to the deployed one at
the canonical key only — the capstones claim no cross-key binding. `idealizedAcceptsFaithful`
identifies only the injectable-oracle observer's typed core; it is not a Rust-reader claim.
`rustAcceptsRefinesLeanRaw` names that production claim separately, in the soundness direction
actually required. `instanceColumnsExact` and `numProofs_pos` pin the shape of each deployed call:
exact ten-row instance columns
(excluding the trailing-zero commitment alias) and one invocation per present bundle carrying
its positive action count. `dlogAdvantageAgrees` prevents the record from
carrying an unrelated advantage function: it must be the one used by `profile`.  Its concrete
security interpretation remains the permanent external estimate. -/
structure ActionDeploymentInstantiation {T : Type*} [DecidableEq T] (pp : ProofParams)
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (query : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → T)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (workLimit : ℕ) where
  /-- The nonzero generator used by the DLOG reduction. -/
  basisGenerator : VestaG
  basisGenerator_ne_zero : basisGenerator ≠ 0
  /-- The setup query labels are collision-free, as required by the generator-RO basis theorem. -/
  queryInjective : Function.Injective query
  /-- The exact finite-security profile consumed by the Action capstone.  Its explicit prover and
  reduction costs remain at the accepted work-accounting floor. -/
  profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDirectDlogProfile
    family hchar basisGenerator workLimit
  /-- The deployed one-squeeze challenge law at the typed digest-to-field boundary. -/
  deployedChallengeLaw : PMF Fp
  /-- The typed conversion is the proved 512-bit reduction law.  The concrete hash-to-uniform-
  digest identification is the accepted floor immediately behind this equality. -/
  challengeLawIsChallenge255 : deployedChallengeLaw = challenge255
  /-- The deployed distribution of the augmented URS basis. -/
  deployedBasisLaw : PMF (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
  /-- The deployed fixed hash-to-curve derivation realizes the generator-random-oracle
  experiment.  Permanent under the GroupHash idealization. -/
  basisIsGeneratorRO :
    deployedBasisLaw = (orchardGeneratorROSetup query).map (orchardGeneratorROBasis query)
  /-- The deployed verifying-key digest. -/
  deployedVkDigest : VerifyingKey (AdaptiveActionStatementShape pp) Fp VestaG → Fp
  /-- The family's opaque transcript digest agrees with the deployed digest at the canonical
  key of every basis.  Single-key agreement only: no cross-key binding is claimed or needed. -/
  vkDigestAgreesOnCanonical : ∀ basis,
    family.vkHash basis (adaptiveActionStatementVk pp basis) =
      deployedVkDigest (adaptiveActionStatementVk pp basis)
  /-- The pinned-key description supplied to the production verifier at each basis. -/
  pinnedVkDescription :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) → String
  /-- The description hashes to the same canonical-key scalar used by the family. -/
  pinnedVkDigestAgrees : ∀ basis,
    family.vkTranscriptRepr basis = keyDigest (pinnedVkDescription basis)
  /-- The idealized verifier's acceptance on typed inputs under an injectable oracle table.  This
  exists for the Challenge255 hybrid and is not the production Rust acceptance relation. -/
  deployedIdealizedAccepts :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → Prop
  /-- The injectable-oracle typed observer agrees with the model's checked acceptance.  This is
  an idealized experiment identification, not evidence about Rust decoding. -/
  idealizedAcceptsFaithful : ∀ basis O,
    deployedIdealizedAccepts basis O ↔ family.accepts basis O
  /-- The raw instance columns each deployed verifier call supplies, per action. -/
  deployedInstanceColumns :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → Fin pp.numProofs → List (List Fp)
  /-- Every action's supplied raw instance is exactly the full ten-row column serializing its
  typed public inputs (`actionCircuit_publicInputRows_zero`).  This pins the instance
  construction behind the typed boundary `acceptsFaithful` prices: Halo2's Lagrange commitment
  zero-pads columns, so a shorter column commits — and verifies — identically to its zero-padding
  (`commitInstance_append_replicate_zero`, `assembleNonInteractiveInstances?_padColumns`); in
  particular a nine-row column aliases the ten-row column ending in `disableCrossAddress = 0`.
  Row-count validation cannot exclude the alias; supplying exact rows does. -/
  instanceColumnsExact : ∀ basis O (p : Fin pp.numProofs),
    deployedInstanceColumns basis O p =
      List.ofFn fun column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns =>
        actionCircuit.publicInputRows ((family.runOutput basis O).inputs p)
          (⟨column⟩ : Column .instance)
  /-- The proof byte string passed to the production verifier for this run. -/
  deployedProofBytes :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → List UInt8
  /-- Actual production Rust acceptance for the selected raw columns and proof bytes.  The record
  deliberately leaves this relation abstract until a verified Rust semantics supplies it. -/
  deployedRustAccepts :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → Prop
  /-- **Explicit production refinement assumption.** For every input represented by this
  deployment record, Rust acceptance implies the complete Lean raw-byte predicate.  The direction
  is one-way because soundness needs event inclusion, not full implementation equivalence. -/
  rustAcceptsRefinesLeanRaw : ∀ basis O,
    deployedRustAccepts basis O →
      DeployedAcceptsRawBytes (AdaptiveActionStatementShape pp)
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis) (adaptiveActionStatementVk pp basis)
        (pinnedVkDescription basis) (deployedInstanceColumns basis O)
        (adaptiveActionStatementCommitColumn pp basis) (deployedProofBytes basis O)
  /-- **AGM representation assumption.** On an accepted run, Lean's canonical reader returns the
  same typed proof as the online-AGM family output.  This is not reader correctness: it is the
  separate claim that the accepted production proof lies in the represented adversary class. -/
  rustAcceptedProofRepresented : ∀ basis O,
    deployedRustAccepts basis O →
      (readProof? (AdaptiveActionStatementShape pp)).run (deployedProofBytes basis O) =
        some ((family.runOutput basis O).toAlgebraicWfProof.proof.1, [])
  /-- The verifier is invoked once per present Orchard bundle, with the proof count equal to the
  bundle's action count.  Zero models an absent bundle, never an empty verifier invocation
  (`book/src/formal-verification/source-map.md`), so a deployment record prices a positive
  count; that the count equals the deployed bundle's action count is part of the same
  identification. -/
  numProofs_pos : 0 < pp.numProofs
  /-- Maximum number of distinct challenge points visited by the complete knowledge-failure
  experiment. -/
  challengeQueryBound : ℕ
  /-- A finite execution tree for the deployed typed knowledge-failure experiment.  Its Boolean
  output is acceptance with failure of the executable witness projection. -/
  failureObserver :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      OracleComp (AdaptiveActionStatementTranscript pp) Fp Bool
  /-- The observer really decides the typed deployed knowledge-failure predicate under lookup-table
  semantics. -/
  failureObserverTrue_iff : ∀ basis O,
    (failureObserver basis).run O = true ↔
      deployedIdealizedAccepts basis O ∧
        family.adaptiveStatementKnowledgeExtractor hchar basis O = none
  /-- Deduplication gives random-oracle semantics to repeated transcript points and preserves the
  stated query budget. -/
  failureObserverQueryBound : ∀ basis,
    (OracleComp.dedup [] (failureObserver basis)).QueryBound challengeQueryBound
  /-- The budget is no looser than the experiment it prices: one adversary run, at most
  `family.Q` transcript points, plus the verifier's own `11 + k` squeezes — the envelope
  `relationFinderReads_card_le` certifies for one retained traversal.  `OracleComp.QueryBound` is
  upward-closed, so `failureObserverQueryBound` alone is only a floor on `challengeQueryBound`,
  and the capstone's joint charge `challengeQueryBound * challenge255Bias` could be padded past
  `1`; this ceiling is what prices that charge at the closed `2^-136` the deployed endpoint
  states. -/
  challengeQueryBound_le :
    challengeQueryBound ≤ family.Q + (11 + (AdaptiveActionStatementShape pp).k)
  /-- Lazy uniform answers to the deduplicated observer are exactly the whole-table ideal event
  bounded by the Action capstone.  This is the explicit typed fixture/refinement seam. -/
  idealFailureMeasure_eq :
    (((orchardGeneratorROSetup query).map (orchardGeneratorROBasis query)).bind fun basis ↦
        (OracleComp.dedup [] (failureObserver basis)).runFreshPMF uniformChallenge).toOuterMeasure
          {true} =
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure
          ((fun p ↦ (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.adaptiveStatementKnowledgeFailureEvent hchar)
  /-- The assumed discrete-log advantage at each query/group-work budget — the value the
  profile consumes. Data, not an obligation: its identification with a standard
  resource-bounded game is the permanent external estimate. -/
  dlogAdvantage : ℕ → ℕ → ℝ≥0∞
  /-- Prevent a deployment record from advertising a different advantage than its capstone
  profile. -/
  dlogAdvantageAgrees : dlogAdvantage = profile.advantage

namespace ActionDeploymentInstantiation

variable {T : Type*} [DecidableEq T] {pp : ProofParams}
  {family : ComputedAdaptiveActionStatementFSFamily pp}
  {query : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → T}
  {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O) <
      Zcash.Arithmetic.scalarFieldOrder}
  {workLimit : ℕ}

/-- The joint deployed failure law: sample the deployed basis, then run the deduplicated complete
observer with Challenge255 answers. -/
noncomputable def deployedFailurePMF
    (deployment : ActionDeploymentInstantiation pp family query hchar workLimit) : PMF Bool :=
  deployment.deployedBasisLaw.bind fun basis ↦
    (OracleComp.dedup [] (deployment.failureObserver basis)).runFreshPMF
      deployment.deployedChallengeLaw

/-- The certified query ceiling at the profile's work limit: the adversary's budget is at most
`workLimit` (`profile.queryBound`), so the observer visits at most `workLimit + (11 + k)` distinct
points. -/
theorem challengeQueryBound_le_workLimit
    (deployment : ActionDeploymentInstantiation pp family query hchar workLimit) :
    deployment.challengeQueryBound ≤ workLimit + (11 + (AdaptiveActionStatementShape pp).k) :=
  le_trans deployment.challengeQueryBound_le
    (Nat.add_le_add_right deployment.profile.queryBound _)

/-- The observer's Boolean event has the intended model meaning on every concrete oracle table. -/
theorem failureObserver_true_iff_model
    (deployment : ActionDeploymentInstantiation pp family query hchar workLimit)
    (basis) (O : family.Coins) :
    (deployment.failureObserver basis).run O = true ↔
      (basis, O) ∈ family.adaptiveStatementKnowledgeFailureEvent hchar := by
  rw [deployment.failureObserverTrue_iff]
  exact and_congr (deployment.idealizedAcceptsFaithful basis O) Iff.rfl

/-- Production Rust acceptance at the concrete BLAKE2b table is contained in the exact typed
family acceptance event.  This theorem composes — and visibly consumes — raw-reader refinement,
exact Action instance serialization, canonical proof decoding, key-digest agreement, and the
proved Lean byte-to-family bridge. -/
theorem rustAccepts_halo2Coins_implies_familyAccepts
    (deployment : ActionDeploymentInstantiation pp family query hchar workLimit)
    (basis)
    (haccepts : deployment.deployedRustAccepts basis family.halo2Coins) :
    family.accepts basis family.halo2Coins := by
  apply family.accepts_of_acceptsBytes basis (deployment.pinnedVkDescription basis)
    (deployment.deployedProofBytes basis family.halo2Coins)
    (deployment.pinnedVkDigestAgrees basis)
  refine ⟨?_, deployment.rustAcceptedProofRepresented basis family.halo2Coins haccepts⟩
  have hraw := deployment.rustAcceptsRefinesLeanRaw basis family.halo2Coins haccepts
  have hinstances : deployment.deployedInstanceColumns basis family.halo2Coins =
      adaptiveActionStatementRawInstances pp
        (family.runOutput basis family.halo2Coins).inputs := by
    funext p
    simpa only [adaptiveActionStatementRawInstances] using
      deployment.instanceColumnsExact basis family.halo2Coins p
  rw [← hinstances]
  exact hraw

/-- The exact observer used by `deployedFailurePMF` still decides the modeled knowledge-failure
event: deduplication changes repeated-query scheduling but preserves lookup-table execution. -/
theorem dedupFailureObserver_true_iff_model
    (deployment : ActionDeploymentInstantiation pp family query hchar workLimit)
    (basis) (O : family.Coins) :
    (OracleComp.dedup [] (deployment.failureObserver basis)).run O = true ↔
      (basis, O) ∈ family.adaptiveStatementKnowledgeFailureEvent hchar := by
  rw [OracleComp.run_dedup _ O [] (by simp)]
  exact deployment.failureObserver_true_iff_model basis O

end ActionDeploymentInstantiation

end Zcash.Snark
