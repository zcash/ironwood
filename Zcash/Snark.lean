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
--   (`Soundness/Deployed/Vesta.lean`). Deliberately NOT re-exported by this umbrella: the
--   byte-locked fixture captures must `import Zcash.Snark` (the header halo2's
--   `dump_vesta_lean_fixture` emits), and re-exporting the soundness argument here put the
--   whole `Soundness/` subtree on every capture lane's build path — most of the cold-build
--   critical path (issue #153). Import `Soundness` modules directly. They stay in the
--   default build through the `Zcash.Snark.Soundness.+` glob on the `Zcash` target, and
--   `scripts/check_build_coverage.sh` asserts the closure property in CI.
-- * `Fixtures/` — concrete Orchard captures and the boundary checks they license, split by
--   capture kind. The namespaces (`Fixture`, `Fixture2`, `FixtureRandom`, `FixtureRandom2`) are
--   emitted by halo2's `dump_vesta_lean_fixture` and cannot be renamed here: the fixture CI
--   regenerates each `Fixture.lean` and diffs it. `FixtureMax` is the shape at any action count.
-- * `Capstones/` — the deployed Action circuit's advertised statements, all in `Capstone`:
--   `ActionEvents` -> `ActionChecks` -> `ActionBudgets` -> `Action`, ending at the two
--   knowledge-soundness endpoints that nothing else depends on — the consensus-generic error
--   formula and its `2^123` work-factor instantiation. The verifier-level endpoints are
--   elsewhere, with the layer that proves them: the straight-line knowledge errors beside their
--   capture, the consensus work factors in `Soundness/AGM/`.
--
-- Import modules here that this umbrella should re-export. Build coverage does not depend on
-- this list: every module under `Zcash/` must be reachable from some default target, which
-- `scripts/check_build_coverage.sh` enforces (the `Soundness/` subtree, for instance, is
-- carried by a lakefile glob instead of an import here).

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
-- The deployed verifier group. The captures state their points in `VestaG` (and open the
-- CompElliptic Pasta namespaces this module carries), so the umbrella must supply it; it was
-- hoisted out of `Soundness/Decoded/Vesta.lean` exactly so that supplying it does not pull
-- the soundness stack back onto the capture lanes (issue #153).
import Zcash.Snark.Core.Vesta
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
-- The quantified random match — the sample space, the good event's enumerated denominator
-- factors, and the rational-representation walk (`Fingerprint/SampleSpace`, `Fingerprint/
-- Rational/`, `Fingerprint/Epsilon`) — is deliberately NOT re-exported, for the same reason
-- as `Soundness/` above: the captures reference none of it, and its `Rational/Capstone`
-- chain (~4 min) sat on every capture lane's build path through this umbrella. Its
-- consumers (each random family's `Epsilon.lean`, and the census files through them)
-- import it directly, and the `FixtureCheck` glob keeps it in the default build.
