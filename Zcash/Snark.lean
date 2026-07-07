-- The Orchard SNARK verifier fingerprint.
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
import Zcash.Snark.Fingerprint.Match
import Zcash.Snark.Soundness.InnerProduct
import Zcash.Snark.Soundness.Extraction
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Soundness.IpaSoundness
-- Deployed halo2-verifier soundness path: peel the deployed IPA (U/W/S apparatus) onto clean `ipa_soundV`,
-- with commitment binding expressed as a discrete-log-relation reduction (#13).
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Deployed.Fold
import Zcash.Snark.Soundness.Deployed.Ipa
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
-- Fiat-Shamir forking development: random-oracle discharge (#11) and round-by-round soundness (#23).
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.Forking.Ordering
import Zcash.Snark.Soundness.Forking.Assembly
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Vesta
-- AGM binding reduction: route each deployed `HasNontrivialRelation` branch through the fixed-slot
-- discrete-log adapter and the algebraic-prover model (#15).
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.AGM.Probability
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Capstone
