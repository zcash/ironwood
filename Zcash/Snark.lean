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
--   loaded in the auto-generated `Fixture.lean`) plus the Schwartz–Zippel bound.
-- * `Soundness/` — the soundness argument, in dependency layers. `Ipa/` (opening relation and the
--   round fold) and `Constraint/` (the vanishing check) are two independent roots; `Argument/`
--   proves the permutation and lookup arguments over `Constraint/`; `Pricing/` measures the
--   challenge bad sets and `Relation/` says what constraint satisfaction buys. Above those,
--   `AGM/`, `StraightLine/`, and `Composition/` carry extraction and composition from the
--   acceptance predicate (`Soundness/Main.lean`), instantiated at Vesta
--   (`Soundness/Deployed/Vesta.lean`).
-- * `Fixtures/` — concrete Orchard captures and the boundary checks they license, split by
--   capture kind. The namespaces (`Fixture`, `Fixture2`, `FixtureRandom`, `FixtureRandom2`) are
--   emitted by halo2's `dump_vesta_lean_fixture` and cannot be renamed here: the fixture CI
--   regenerates each `Fixture.lean` and diffs it. `FixtureMax` is the shape at any action count.
-- * `Capstones/` — the deployed Action circuit's advertised statements, all in `Capstone`:
--   `ActionEvents` -> `ActionChecks` -> `ActionBudgets` -> `Action`, ending at twelve endpoints
--   that nothing else depends on. The verifier-level endpoints are elsewhere, with the layer
--   that proves them: the straight-line knowledge errors beside their capture, the
--   consensus work factors in `Soundness/AGM/`.
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
import Zcash.Snark.Verifier.Ipa
import Zcash.Snark.Verifier.Checks
import Zcash.Snark.Verifier.Queries
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.Instances
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Verifier.Deployed
import Zcash.Snark.Verifier.Parametric
import Zcash.Snark.Verifier.GroupingRef
import Zcash.Snark.Fingerprint.Match
-- The quantified random match — the sample space, the good event's enumerated
-- denominator factors, and the rational-representation walk of the assembled coefficients.
import Zcash.Snark.Fingerprint.SampleSpace
import Zcash.Snark.Fingerprint.Rational.GoodEvent
import Zcash.Snark.Fingerprint.Rational.Representation
import Zcash.Snark.Fingerprint.Rational.ConstraintWalk
import Zcash.Snark.Fingerprint.Rational.GroupingTable
import Zcash.Snark.Fingerprint.Rational.IpaWalk
import Zcash.Snark.Fingerprint.Rational.OpeningWalk
import Zcash.Snark.Fingerprint.Rational.Capstone
import Zcash.Snark.Fingerprint.Epsilon
import Zcash.Snark.Soundness.Argument.GrandProduct
import Zcash.Snark.Soundness.Argument.Lookup
import Zcash.Snark.Soundness.Argument.Permutation
import Zcash.Snark.Soundness.Argument.PermutationConstruction
import Zcash.Snark.Soundness.Argument.RunningProduct
import Zcash.Snark.Soundness.Argument.GrandProductBridge
import Zcash.Snark.Soundness.Argument.LookupAssembly
import Zcash.Snark.Soundness.Argument.PermutationRows
import Zcash.Snark.Soundness.Relation.ConstraintRelations
import Zcash.Snark.Soundness.Pricing.ChallengePricing
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Zcash.Snark.Soundness.Ipa.Halves
import Zcash.Snark.Soundness.Constraint.Constraints
import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Ipa.CommitFold
import Zcash.Snark.Soundness.Ipa.Consistency
import Zcash.Snark.Soundness.Relation.KnowledgeSoundness
import Zcash.Snark.Soundness.Ipa.IpaSoundness
-- Verifier-native semantic models used by the Clean integration boundary.  These
-- belong to the core SNARK library even when no capstone imports them incidentally.
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.Canonical.InstanceCommitment
-- Deployed halo2-verifier algebra and binding reductions.
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Deployed.Fold
import Zcash.Snark.Soundness.Deployed.Verification
-- The reusable Fiat–Shamir oracle kernel and its represented adversary model: random-oracle
-- lemmas, deployed transcript ordering, closed-form IPA assembly, and the bounded
-- querying-adversary reduction.
import Zcash.Snark.Soundness.Oracle.Model
import Zcash.Snark.Soundness.FiatShamir.Assembly
import Zcash.Snark.Soundness.FiatShamir.Ordering
import Zcash.Snark.Soundness.FiatShamir.Execution
import Zcash.Snark.Soundness.FiatShamir.Adversary
import Zcash.Snark.Soundness.Main
-- Multiopen decode reconstruction: bind the IPA witness to real verifier columns recovered from
-- the represented `x₄` power batch (`Multiopen.Decode`, `Multiopen.Deployed`), the MSM evaluation
-- spine (`Multiopen.Compat`), and the explicit opened/member interfaces (`Multiopen.Opened`).
-- Schwartz–Zippel good-challenge budgets and production (kills `hgood` at the `_xgood` rungs).
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Compat
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.RPoly
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.Canonical.Terminal
import Zcash.Snark.Soundness.Circuit.Terminal
import Zcash.Snark.Soundness.Decoded.Vesta
-- AGM binding reduction: consume computed deployed relations through the programmed-basis
-- discrete-log adapter and representation-carrying algebraic-prover model. The adapter and its
-- pricing are model-free and live in `Zcash.Common.{AlgebraicRelation,RelationProbability}`;
-- what is AGM here is the URS view and the represented prover.
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.Peel
-- Rewind-free deployed multiopen decoding and additive pinned-root composition.
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
-- The straight-line AGM route: staged IPA representations, fixed-call deployed constraint
-- extraction, and an explicit finite-security DLOG work profile.
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
-- The constraint-level and straight-line family interfaces are inhabited at the witness shape.
import Zcash.Snark.Soundness.Composition.StraightLineWitness
-- The zero-data keystone and the constant zero prover family, at any shape.
import Zcash.Snark.Soundness.AGM.ZeroFamily
-- The zero family's deployed root layer: six staged root events at any shape.
import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
-- The straight-line deployed interface, inhabited with live IPA rounds at any instance-free shape.
import Zcash.Snark.Soundness.Composition.ZeroStraightLine
-- The direct-coordinate postprocessing carries an explicit polynomial total-cost model.
-- The Action-level semantic challenge exclusions, priced and summed.
-- A rewind-free decode presented through the opened-batch interface the Action terminal takes.
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.SemanticChallengeRemainder
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.Composition.SequentialLift
import Zcash.Snark.Soundness.Composition.DirectPathCost
-- Circuit soundness specializations consume the Clean/Ironwood integration
-- boundary; they do not belong to that boundary's import graph.
import Zcash.Snark.Soundness.StraightLine.Terminal
import Zcash.Snark.Soundness.StraightLine.Event
import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Soundness.Action.AdaptiveStatementModel
import Zcash.Snark.Soundness.Action.AdaptiveStatementAccounting
import Zcash.Snark.Soundness.Action.AdaptiveStatementTerminal
import Zcash.Snark.Soundness.Action.AdaptiveStatementEvent
import Zcash.Snark.Soundness.Action.AdaptiveStatementCapstone
import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge
import Zcash.Snark.Soundness.Action.AdaptiveStatementProfile
import Zcash.Snark.Soundness.Action.AdaptiveStatementReads
