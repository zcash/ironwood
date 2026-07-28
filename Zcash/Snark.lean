-- The Orchard SNARK verifier: transcription and soundness.
--
-- Library layout:
-- * `Core/` — the shared objects that are specific to the verifier: the typed proof string and
--   the challenges. The arithmetic-tier objects the verifier is built from (the scalar field
--   `F_p`, the verifier group and URS, the fingerprint MSM and its Pippenger accelerator) live
--   one tier down, in `Zcash/Arithmetic/`; `Core.lean` is a one-name compatibility alias for
--   the byte-locked fixture captures and nothing else.
-- * `Verifier/` — the transcription layer: the deployed halo2 verifier's MSM assembly as a pure
--   Lean function (queries, expressions, multiopen, IPA fold, Fiat–Shamir schedule).
-- * `Fingerprint/` — the faithfulness cross-check: the captured-fixture match (`native_decide`,
--   loaded in the auto-generated `Fixture.lean`) plus the Schwartz–Zippel and batch-RLC bounds.
-- * `Soundness/` — the soundness argument: IPA special soundness and extraction, binding as a
--   DLR reduction, the constraint layer, the permutation/lookup kernels, and the composition
--   (`Soundness/Main.lean`), instantiated at Vesta (`Soundness/Vesta.lean`).
--
-- Import modules here that should be built as part of the library.

-- The arithmetic tier the verifier is stated over. The umbrella also re-exports `Fp` and `URS`
-- at the `Zcash` root, which is how they resolve unqualified across the repository.
import Zcash.Arithmetic
import Zcash.Arithmetic.Msm
import Zcash.Arithmetic.FastMsm
-- The `Zcash.Snark`-namespace compatibility alias for the byte-locked fixture captures. Kept in
-- the closure so the captures still elaborate; no editable module depends on it.
import Zcash.Snark.Core
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Fingerprint.SchwartzZippel
import Zcash.Snark.Fingerprint.Batch
import Zcash.Snark.Verifier.Ipa
import Zcash.Snark.Verifier.Checks
import Zcash.Snark.Verifier.Queries
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Verifier.Parametric
import Zcash.Snark.Fingerprint.Match
import Zcash.Snark.Soundness.GrandProduct
import Zcash.Snark.Soundness.Lookup
import Zcash.Snark.Soundness.Permutation
import Zcash.Snark.Soundness.PermutationConstruction
import Zcash.Snark.Soundness.RunningProduct
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.ConstraintRelations
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.InnerProduct
import Zcash.Snark.Soundness.Extraction
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Soundness.IpaSoundness
-- Verifier-native semantic models used by the Clean integration boundary.  These
-- belong to the core SNARK library even when no capstone imports them incidentally.
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.Canonical.InstanceCommitment
-- Deployed halo2-verifier soundness path: peel the deployed IPA (U/W/S apparatus) onto the clean
-- `ipa_soundV`, with commitment binding expressed as a discrete-log-relation reduction.
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Deployed.Flat
import Zcash.Snark.Soundness.Deployed.Fold
import Zcash.Snark.Soundness.Deployed.Ipa
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
-- The reusable Fiat–Shamir forking kernel and its concrete adversary producer.
import Zcash.Snark.Soundness.Forking
import Zcash.Snark.Soundness.Main
-- Multiopen decode reconstruction: bind the IPA witness to real verifier columns recovered from
-- batched openings (`Multiopen.Decode`), the compatibility layer exposing the propositional binding
-- interface over fs-adversary's `NontrivialRelation`/`ForkedTranscript` apparatus (`Multiopen.Compat`),
-- the `x₄` multiopen rewinding (`Multiopen.Deployed`), and the opened chain threading the fork's
-- declared `U`/`W` components through the batch decode (`Multiopen.Opened`).
-- Schwartz–Zippel good-challenge budgets and production (kills `hgood` at the `_xgood` rungs).
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Compat
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.RPoly
import Zcash.Snark.Soundness.Multiopen.Claimed
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.Multiopen.CanonicalSelection
import Zcash.Snark.Soundness.Canonical.Terminal
import Zcash.Snark.Soundness.Canonical.Vesta
import Zcash.Snark.Soundness.TopLevelTerminal
import Zcash.Snark.Soundness.TopLevelVesta
import Zcash.Snark.Soundness.ActionVesta
import Zcash.Snark.Soundness.Vesta
-- Concrete fork-tree knowledge error over the deployed Orchard parameters.
import Zcash.Snark.Soundness.Deployed.ConcreteBounds
-- AGM binding reduction: consume computed deployed relations through the programmed-basis
-- discrete-log adapter and representation-carrying algebraic-prover model.
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.AGM.Probability
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.BindingSignature
-- Rewind-free deployed multiopen decoding and additive pinned-root composition.
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
