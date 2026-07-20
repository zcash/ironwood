-- The Orchard SNARK verifier: transcription and soundness.
--
-- Library layout:
-- * `Core/` — the shared objects: the scalar field `F_p`, the verifier group and URS, the typed
--   proof string, the challenges, and the fingerprint MSM.
-- * `Verifier/` — the transcription layer: the deployed halo2 verifier's MSM assembly as a pure
--   Lean function (queries, expressions, multiopen, IPA fold, Fiat–Shamir schedule).
-- * `Fingerprint/` — the faithfulness cross-check: the captured-fixture match (`native_decide`,
--   loaded in the auto-generated `Fixture.lean`) plus the Schwartz–Zippel and batch-RLC bounds.
-- * `Soundness/` — the soundness argument: IPA special soundness and extraction, binding as a
--   DLR reduction, the constraint layer, the permutation/lookup kernels, and the composition
--   (`Soundness/Main.lean`), instantiated at Vesta (`Soundness/Vesta.lean`).
--
-- Import modules here that should be built as part of the library.

import Zcash.Snark.Core.Field
import Zcash.Snark.Core.Group
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Core.Msm
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
import Zcash.Snark.Soundness.InnerProduct
import Zcash.Snark.Soundness.TrustBoundary
import Zcash.Snark.Soundness.Extraction
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Soundness.IpaSoundness
-- Deployed halo2-verifier soundness path: peel the deployed IPA (U/W/S apparatus) onto the clean
-- `ipa_soundV`, with commitment binding expressed as a discrete-log-relation reduction.
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Deployed.Fold
import Zcash.Snark.Soundness.Deployed.Ipa
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.TrustBoundary
import Zcash.Snark.Soundness.Deployed.Verification
-- The Fiat–Shamir forking development: discharges the forked transcript tree in the random-oracle
-- model, and proves round-by-round soundness by tying each IPA round challenge to the transcript
-- prefix that commits it.
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.Forking.Assembly
import Zcash.Snark.Soundness.Forking.Ordering
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Vesta
-- AGM binding reduction: consume computed deployed relations through the fixed-slot discrete-log
-- adapter and representation-carrying algebraic-prover model (#15).
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.AGM.Probability
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.TrustBoundary
