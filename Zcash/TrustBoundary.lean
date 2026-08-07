import Zcash.Circuits.Action.RealBases
import Zcash.Security.Ledger.Bridge
import Zcash.Security.Ledger.SinsemillaDLR
import Zcash.Arithmetic.FastMsm
import Zcash.Security.KeyBinding.Instance
import Zcash.Security.KeyBinding.Probability
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.Spendability
import Zcash.Security.Ledger.SpendAuthority
import Zcash.Security.Ledger.Completeness
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.Nullifier
import Zcash.Security.Ledger.Value
import Zcash.Security.Ledger.KeyBindingArm
import Zcash.Security.Ledger.ExtractionArm
import Zcash.Security.Ledger.ExtractionKappaArm
import Zcash.Security.RedDSA.Basic
import Zcash.Security.RedDSA.Extraction
import Zcash.Security.RedDSA.KnowledgeError
import Zcash.Security.Common.Birthday
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Meta.AxiomCheck
import Zcash.Snark.Soundness.Ipa.CommitFold
import Zcash.Snark.Soundness.Decoded.Vesta
import Zcash.Snark.Soundness.Decoded.VacuityWitness
import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.FiatShamir.Adversary
import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.Constraint.FoldSplit
import Zcash.Snark.Soundness.Argument.GrandProductBridge
import Zcash.Snark.Soundness.Argument.LookupAssembly
import Zcash.Snark.Soundness.Argument.PermutationRows
import Zcash.Snark.Soundness.Relation.ConstraintRelations
import Zcash.Snark.Soundness.Pricing.ChallengePricing
import Zcash.Security.Ledger.KeyBindingDLR
import Zcash.Security.Ledger.NoteCommitDLR
import Zcash.Security.Ledger.MerkleDLR
import Zcash.Security.Ledger.OrchardCapstone
import Zcash.Snark.Soundness.Pricing.DegreeWalk
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.PinnedRootWitness
import Zcash.Snark.Soundness.Composition.StraightLineWitness
import Zcash.Snark.Soundness.Composition.DirectPathCost
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Verifier.Deployed
import Zcash.Snark.Soundness.Composition.SemanticChallengeRemainder
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.Composition.SequentialLift
import Zcash.Snark.Soundness.Composition.ChallengeReads
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.AGM.ZeroFamily
import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
import Zcash.Snark.Soundness.Composition.ZeroStraightLine
import Zcash.Snark.Soundness.AGM.DirectConstraintFamily
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Fingerprint.Match
import Zcash.Snark.Fingerprint.Epsilon
import Zcash.Snark.Fingerprint.Rational.ConstraintWalk
import Zcash.Snark.Fingerprint.Rational.GroupingTable
import Zcash.Snark.Fingerprint.Rational.IpaWalk
import Zcash.Snark.Fingerprint.Rational.OpeningWalk
import Zcash.Snark.Fingerprint.Rational.Capstone
import Mathlib.Util.AssertNoSorry
import Zcash.Snark.Soundness.AGM.AdaptiveIpaSurfaces
import Zcash.Snark.Soundness.AGM.AdaptiveRootSurfaces
import Zcash.Snark.Soundness.Action.AdaptiveStatementReads

/-!
# Trust boundary, build-checked

The library-wide census that makes the trust claims build-time checks rather than prose: a change
that widens a declaration's trusted base — a `sorry` reached through some dependency, an unexpected
axiom, or `native_decide` where none was permitted — fails this file rather than passing silently.

Two commands from `Zcash.Meta.AxiomCheck`, per the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`):

* **Computed break reductions** get `assert_computable`: the declaration is a plain `def` — not a
  theorem, marked neither `unsafe`/`partial` nor `noncomputable` — with axioms bounded by
  `propext` / `Quot.sound`. `+choice` additionally permits `Classical.choice`; with the
  plain-`def` check this asserts choice enters only through erased `Prop` certificate fields, so
  the break data cannot have been conjured from mere propositional existence.
* **Theorems** get `assert_axioms`, an upper bound at the standard tier
  (`propext` / `Classical.choice` / `Quot.sound`). Both commands reject `sorryAx`.

Both commands are built on `Lean.collectAxioms`, which walks a declaration's transitive
*dependencies*. Coverage therefore flows downwards only: a declaration that nothing censused
depends on is checked by nothing, however prominent it is. Deliverable endpoints are exactly the
top-level leaves, so they must be pinned *directly* — never left to inherit coverage from some
dependent, which would vanish the moment that dependent is refactored.
`scripts/check_endpoint_census.sh` enforces this in CI for the capstone naming families. A new
public endpoint must either belong to one of the listed protocol families or end in the semantic
suffix `_error_bound`, `_finite_security`, `_measure_le`, `_probability_bound`, or `_capstone`; the
last keeps new protocol families covered without another prefix-specific regex edit.
-/

/-! ## Key binding — computed break reductions -/

assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak +choice
assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak +choice

/-! ## Key binding — theorems -/

assert_axioms Zcash.Security.KeyBinding.Extractor.card_ivk_ge
assert_axioms Zcash.Security.KeyBinding.commit_scalar_pm
assert_axioms Zcash.Security.KeyBinding.rivk_eq_finalOracle
assert_axioms Zcash.Security.KeyBinding.sameIvk_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.openingBreak_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.break_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.residual_of_finalQuery_eq
assert_axioms Zcash.Security.KeyBinding.nk_pinned
assert_axioms Zcash.Security.KeyBinding.ak_pinned
assert_axioms Zcash.Security.KeyBinding.qk_or_sk_pinned
assert_axioms Zcash.Security.KeyBinding.collision_mem_shifted_pm
assert_axioms Zcash.Security.KeyBinding.toInterface

/-! ## Birthday bound -/

assert_axioms Zcash.Security.Birthday.card_shifted_pm_collision_le
assert_axioms Zcash.Security.Birthday.shifted_pm_collision_fraction_le
assert_axioms Zcash.Security.Birthday.birthday_closed_form

/-! ## Key binding — whole-table random-oracle model -/

assert_computable Zcash.Security.KeyBinding.finalQueryEquiv
assert_axioms Zcash.Security.KeyBinding.eval_restrict
assert_axioms Zcash.Security.KeyBinding.pair_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.finset_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.ofBreak_queries
assert_axioms Zcash.Security.KeyBinding.break_measure_le
assert_computable Zcash.Security.KeyBinding.badList
assert_axioms Zcash.Security.KeyBinding.mem_badList
assert_axioms Zcash.Security.KeyBinding.badList_measure_le
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory_measure_le
assert_axioms Zcash.Security.KeyBinding.CollidesDuring
assert_axioms Zcash.Security.KeyBinding.CollidesDuring.of_pair
assert_axioms Zcash.Security.KeyBinding.sum_two_mul_add
assert_axioms Zcash.Security.KeyBinding.collidesDuring_measure_le
assert_axioms Zcash.Security.KeyBinding.queries_pair_collision_measure_le
assert_computable Zcash.Security.KeyBinding.derivQueries
assert_axioms Zcash.Security.KeyBinding.break_measure_le_adaptive
assert_axioms Zcash.Security.KeyBinding.break_measure_le_of_queryBound
assert_axioms Zcash.Security.KeyBinding.toOuterMeasure_bind_le
assert_axioms Zcash.Security.KeyBinding.break_measure_le_mixture
assert_axioms Zcash.Security.KeyBinding.uniformOfFintype_prod
assert_computable Zcash.Security.KeyBinding.evalEquiv
assert_axioms Zcash.Security.KeyBinding.uniform_triple_eval
assert_axioms Zcash.Security.KeyBinding.break_measure_le_product
assert_axioms Zcash.Security.toInterface_break_measure_le

/-! ## Ledger-layer break reductions

Most of these data-producing reductions rest on `propext` and `Quot.sound` only — no
`Classical.choice` even in erased positions, the strict (flagless) `assert_computable`
tier. The exception is `nfOldEqOrBreak`: it decides the `nk`-equality branch on
`DecidableEq NK`, so choice arrives with its proof terms in erased positions (the
`+choice` tier). The reduction data is still a direct term of the inputs. -/

assert_computable Zcash.Security.RandomOracle.Collision.upToSign
assert_computable Zcash.Security.Ledger.Merkle.collisionOfWrongLeaf
assert_computable Zcash.Security.Ledger.noteCommitBreakOfNe
assert_computable Zcash.Security.Ledger.nfOldEqOrBreak +choice

/-! ## Statement-layer pinning theorems

The statement layer's exported pinning guarantees: an address `(g_d, pk_d)` determines
`ivk`, and hence `nk` is determined up to an exhibited key-binding break. -/

assert_axioms Zcash.Security.Ledger.ivk_pinned
assert_axioms Zcash.Security.Ledger.nk_eq_or_break

/-! ## Ledger model

The ledger-model definitions are plain computable data over public ledger contents; the
theorems are deterministic list facts. -/

assert_computable Zcash.Security.Ledger.Model.posVal
assert_computable Zcash.Security.Ledger.Merkle.subRoot
assert_computable Zcash.Security.Ledger.Merkle.authChildren
assert_axioms Zcash.Security.Ledger.Merkle.Path.compress_isSome
assert_axioms Zcash.Security.Ledger.Merkle.path_of_root
assert_computable Zcash.Security.Ledger.Model.leafList
assert_computable Zcash.Security.Ledger.Model.leafFun
assert_computable Zcash.Security.Ledger.Model.rootAfter
assert_computable Zcash.Security.Ledger.Model.nullifiers
assert_computable Zcash.Security.Ledger.Model.transparentPoolBalance
assert_computable Zcash.Security.Ledger.Model.outputActions
assert_computable Zcash.Security.Ledger.Model.outputOpenings
assert_computable Zcash.Security.Ledger.Model.positionedOutputs
assert_computable Zcash.Security.Ledger.Model.nonZeroSpends
assert_computable Zcash.Security.Ledger.Model.shieldedPoolBalance
assert_axioms Zcash.Security.Ledger.Model.shieldedPoolBalance_zero
assert_axioms Zcash.Security.Ledger.Model.posVal_lt
assert_axioms Zcash.Security.Ledger.Model.rootAfter_prefix
assert_axioms Zcash.Security.Ledger.Model.output_rho_eq_nullifiers
assert_axioms Zcash.Security.Ledger.Model.output_rho_nodup
assert_axioms Zcash.Security.Ledger.Model.leafList_eq_map
assert_axioms Zcash.Security.Ledger.Model.outputOpenings_length

/-! ## Balance-subset

The capstone and the per-spend pinning are computable reductions; `findPair` and the
anchor search (`Nat.find`, itself axiom-free) keep the branch decisions decidable.
`+choice` on the three reductions is the erased-positions tier: choice enters only
through Mathlib proof terms in `Prop` positions (e.g. `List.getD_eq_getElem`'s proof),
never the data path. -/

assert_computable Zcash.Security.Ledger.Model.findPair
assert_axioms Zcash.Security.Ledger.Model.findPair_spec
assert_axioms Zcash.Security.Ledger.Model.findPair_none
assert_axioms Zcash.Security.Ledger.Model.flatMap_sublist
assert_axioms Zcash.Security.Ledger.Model.outputActions_prefix
assert_axioms Zcash.Security.Ledger.Model.nullifiers_prefix
assert_axioms Zcash.Security.Ledger.Model.take_prefix_take
assert_axioms Zcash.Security.Ledger.Model.spendActions_map_nf_sublist
assert_axioms Zcash.Security.Ledger.Model.length_leafList
assert_axioms Zcash.Security.Ledger.Model.length_positionedOutputs
assert_axioms Zcash.Security.Ledger.Model.positionedOutputs_getElem
assert_computable Zcash.Security.Ledger.Model.noteCommitBreakOfOutputNe
assert_axioms Zcash.Security.Ledger.Model.satisfied_of_spendMem
assert_axioms Zcash.Security.Ledger.Model.anchor_of_spendMem
assert_computable Zcash.Security.Ledger.Model.spendPinnedOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.allPinnedOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.balanceSubsetOrBreak +choice

/-! ## Balance integrity

`+choice` on the three endpoints is again the erased-positions tier: choice arrives with
the `ring`/`omega` proof terms in their `Prop` fields, never the data path. -/

assert_computable Zcash.Security.Ledger.Model.txNetValue
assert_computable Zcash.Security.Ledger.Model.issuanceTotal
assert_axioms Zcash.Security.Ledger.Model.transparentPoolBalance_eq
assert_axioms Zcash.Security.Ledger.Model.positionedOutputs_value_sum
assert_axioms Zcash.Security.Ledger.Model.nonZeroSpends_value_sum
assert_axioms Zcash.Security.Ledger.Model.shieldedPoolBalance_eq_neg
assert_computable Zcash.Security.Ledger.Model.allConservedOrBreak
assert_computable Zcash.Security.Ledger.Model.balanceConservationOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.shieldedBalanceCapOrBreak +choice
assert_axioms Zcash.Security.Ledger.Model.sum_val_le_of_le
assert_axioms Zcash.Security.Ledger.Model.positionedOutputs_value_sum_mono
assert_axioms Zcash.Security.Ledger.Model.shieldedPoolBalance_nonneg
assert_computable Zcash.Security.Ledger.Model.balanceIntegrityOrBreak +choice

/-! ## Spendability

The Faerie-Gold core and the roadblock inversion are computable reductions at the strict
flagless tier; the nullifier split and the persistence theorem are deterministic list
facts. -/

assert_axioms Zcash.Security.Ledger.Model.nullifiers_append
assert_computable Zcash.Security.Ledger.Model.faerieGoldCore
assert_computable Zcash.Security.Ledger.Model.respendOrBreak
assert_axioms Zcash.Security.Ledger.Model.validLedger_append

/-! ## The nullifier-binding reduction

Computed break reduction: a nullifier collision between distinct notes, over the
additive shape of the deployed derivation, computes a nontrivial relation among the
commitment bases, the nullifier base, and the randomness base — the balance
argument's terminal. `+choice` is the erased-positions tier: choice arrives with the
`abel`/`simp` proof terms in the relation's `Prop` fields, never the data path. -/

assert_computable Zcash.Security.Ledger.Model.NontrivialRelation.ofNullifierCollision +choice

/-! ## Spend Authority

The per-action core and the valid-ledger capstone are computable reductions; the
receivability pinning is a deterministic module-algebra theorem. `+choice` on the two
reductions is the erased-positions tier: choice arrives with `smul_eq_zero`'s Mathlib
proof inside the receivability pinning, consumed only in `Prop` positions — never the
data path. -/

assert_axioms Zcash.Security.Ledger.Model.ivk_eq_of_receivable
assert_computable Zcash.Security.Ledger.Model.spendAuthForgeryOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.spendAuthorityOrBreak +choice

/-! ## Honest-spend completeness and the Spendability capstone

The honest construction is computable data (the wallet's own algorithm, including the
authentication data recovered from the defined tree); the two completeness endpoints
are theorems over it. The Spendability capstone is a computed reduction: the
roadblock branch decides nullifier membership and searches out the revealing action.
It carries no `+choice`: neither the decision nor the search reaches for choice, and
no choice-bearing proof term survives in its erased `Prop` positions either. -/

assert_computable Zcash.Security.Ledger.Model.honestTx
assert_computable Zcash.Security.Ledger.Model.HonestAction.withDummySpend
assert_axioms Zcash.Security.Ledger.Model.HonestAction.satisfied
assert_axioms Zcash.Security.Ledger.Model.honestTx_valid
assert_computable Zcash.Security.Ledger.Model.spendabilityOrBreak

/-! ## Probabilistic capstones

The game-level probability statements: pure event algebra over an adversary
distribution of valid annotated ledgers, with a named ε hypothesis per break arm.
The all-prefixes bounds name their ε's on events shared across prefixes, so they
cost no factor of `k` over the single-prefix bounds. -/

assert_axioms Zcash.Security.Ledger.Model.balanceSubsetPerTx_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceSubset_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceConservationPerTx_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceConservation_measure_le
assert_axioms Zcash.Security.Ledger.Model.shieldedBalanceCapPerTx_measure_le
assert_axioms Zcash.Security.Ledger.Model.shieldedBalanceCap_measure_le
assert_axioms Zcash.Security.Ledger.Model.shieldedBalanceNonNegative_succ_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceIntegrityPerTx_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceIntegrity_measure_le
assert_axioms Zcash.Security.Ledger.Model.spendAuthority_measure_le

/-! ## The Orchard-protocol discrete-log-relation discharges

Each Orchard-protocol Balance-subset break arm reduces to a nontrivial discrete-log
relation among the fixed Sinsemilla bases, and `orchardBalanceSubsetOrRelation` routes
all three from a valid Orchard ledger. The probability layer bounds each capstone
violation by the relation event — the branch preimage of that reduction — so a single
`ε_sinsemilladlr` replaces the abstract capstones' per-arm ε's, and the all-prefixes
bounds cost no factor of `k`. The reductions are computable, so they get
assert_computable. The probability bounds and the encoding-injectivity and
coefficient-injectivity facts they consume are theorems, so they get assert_axioms. -/

assert_axioms Zcash.NontrivialRelation.toOne
assert_axioms Zcash.Circuits.Specs.Sinsemilla.chunksOf_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.commitIvkChunks_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.noteCommitChunks_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.merkleChunks_inj
assert_axioms Zcash.Security.Ledger.Bridge.preCoeffs_inj
assert_axioms Zcash.Security.Concrete.PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq
assert_computable Zcash.Security.Ledger.Bridge.relationOfChainPmEq +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Security.Ledger.Bridge.relationOfKeyBindingBreak +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check)
assert_computable Zcash.Security.Ledger.Bridge.relationOfNoteCommitBreak +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_computable Zcash.Security.Ledger.Bridge.relationOfMerkleCollision +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Security.Ledger.Bridge.orchardBalanceSubsetOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceSubsetPerTx_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceSubset_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardShieldedBalanceNonNegative_succ_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceIntegrityPerTx_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceIntegrity_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

/-! ## The Orchard Spend Authority key-binding arm

The Spend Authority key-binding break is the same Orchard-protocol `CommitIvkCollision`
as the Balance key-binding arm. `relationOfSpendAuthorityKBBreak` sends it to a
nontrivial discrete-log relation at the `CommitIvk` domain point and randomness base —
the same terminal as the Balance key-binding arm, with no oracle model.
`orchardSpendAuthorityOrRelation` composes it into the Spend Authority reduction, and
`orchardSpendAuthority_measure_le` names the key-binding arm's hypothesis on that
composed reduction's relation event, so the bound is the forgery arm's ε plus a
discrete-log-relation advantage; the forgery arm's ε is RedDSA ±-randomized
unforgeability. -/

assert_computable Zcash.Security.Ledger.Bridge.relationOfSpendAuthorityKBBreak +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check)
assert_computable Zcash.Security.Ledger.Bridge.orchardSpendAuthorityOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardSpendAuthority_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

/-! ## RedDSA

The abstract scheme behind the signature obligations. Completeness and the
re-randomization axioms are theorems. The extraction failure is computable data,
per breaks-as-computed-data. -/

assert_axioms Zcash.Security.RedDSA.randomizePrivate_add_neg
assert_axioms Zcash.Security.RedDSA.randomizePrivate_zero
assert_axioms Zcash.Security.RedDSA.Scheme.randomizePublic_zero
assert_axioms Zcash.Security.RedDSA.Scheme.derivePublic_randomizePrivate
assert_axioms Zcash.Security.RedDSA.Scheme.derivePublic_add
assert_axioms Zcash.Security.RedDSA.Scheme.derivePublic_injective
assert_axioms Zcash.Security.RedDSA.Scheme.verify_sign
assert_axioms Zcash.Security.RedDSA.Scheme.verify_sign_randomized

/-! ## RedDSA extractability: the binding-signature discharge

The deterministic core of the binding-signature extraction: substituting a verifying
binding signature's representations over the public basis into the Schnorr verification
equation assembles coefficients whose evaluation is zero; whenever some coefficient is
nonzero, they are an `AlgebraicRelationWitness` (`bindingSig_relation_of_nontrivial`), and
away from the one bad challenge of the representation's pivot slot, one is
(`QueryRep.assembled_ne_zero_of_ne_badChallenge`). The knowledge-error block below composes
this with the labeled squeeze and the relation-to-discrete-log reduction. -/

assert_computable Zcash.Security.RedDSA.QueryRep.assembled
assert_computable Zcash.Security.RedDSA.QueryRep.pivot
assert_computable Zcash.Security.RedDSA.QueryRep.badChallenge
assert_axioms Zcash.Security.RedDSA.QueryRep.representationEval_key_of_pivot_eq_none
assert_axioms Zcash.Security.RedDSA.QueryRep.assembled_ne_zero_of_ne_badChallenge
assert_computable Zcash.Security.RedDSA.bindingSig_relation_of_nontrivial +choice

/-! ## The binding-signature knowledge error

The κ-discharge: over the challenge oracle's whole table and the logs of the `m`
presented bases, a labeled algebraic adversary within query budget `qH` produces a
verifying binding signature whose effective representation has a pivot with probability at
most `(qH + 1)/|F| + ε_DL + 1/|F|` (`kappaEvent_measure_le`) — the straight-line AGM+ROM
extraction of Fuchsbauer–Plouviez–Seurin, in the key-only setting. Challenge queries carry
the adversary's representations as labels the oracle never sees; the representation in
effect at the output's query point is the first annotation there, or the announced output
representation when the run never queried the point — the squeeze's fallback branch, which
plays the game's own final challenge query. The relation finder replaying the adversary is
computable, and is the discrete-log adversary that the named `ε_DL` hypothesis constrains.
Degeneracy needs no side condition: at base `0` the hypothesis itself forces
`ε ≥ 1 − 1/|F|` (`textbookDLAdvantageLE_base_zero`). -/

assert_computable Zcash.Security.RedDSA.dischargeOut
assert_computable Zcash.Security.RedDSA.dischargeChallenge
assert_computable Zcash.Security.RedDSA.effectiveRep
assert_computable Zcash.Security.RedDSA.relFinder +choice
assert_axioms Zcash.Security.RedDSA.kappa_le_of_arms
assert_axioms Zcash.Security.RedDSA.kappaEvent_subset
assert_axioms Zcash.Security.RedDSA.badFiber_measure_le
assert_axioms Zcash.Security.RedDSA.relFiber_subset_relSet
assert_axioms Zcash.Security.RedDSA.relFiber_measure_le
assert_axioms Zcash.Security.RedDSA.kappaEvent_measure_le
assert_computable Zcash.Security.RedDSA.zeroBasisRelationFinder +choice
assert_axioms Zcash.Security.RedDSA.textbookDLAdvantageLE_base_zero

/-! ## The transaction-balance premiss in extractor-plus-knowledge-error form

The transaction-balance premiss discharge with a fallible extractor: the extractor
is an arbitrary function, its failures are exhibited `RedDSA.ExtractionFailure`
data, and the Balance capstones bound the violation by `εdlr + κ`, per prefix and at
all prefixes with no factor of `k`. The premiss lands in the binding-signature
layer's nontrivial `(Vbase, Rbase)` relation via `ofBundleIntImbalance`, with the
no-overflow bound discharged from the statement's value ranges, validity's
action-count and `vBalance` range rules, and the named numeric hypothesis
`(maxActions + 1) * valueBound ≤ r`. The Orchard instantiation names the same bounds
at the Orchard-protocol primitives; the integrity bound takes `εdlr + κ` in place of
the opaque `ε_bindsig`. `+choice` is the erased-positions tier. -/

assert_computable Zcash.Security.Ledger.Model.ValueShape.premissOrBreakFallible +choice
assert_computable Zcash.Security.Ledger.Model.txBalancePremissFallible +choice
assert_axioms Zcash.Security.Ledger.Model.extractFailEvent_failure
assert_axioms Zcash.Security.Ledger.Model.txBalanceBreakEvent_fallible_subset
assert_axioms Zcash.Security.Ledger.Model.balanceConservation_measure_le_kerr
assert_axioms Zcash.Security.Ledger.Model.shieldedBalanceCap_measure_le_kerr
assert_axioms Zcash.Security.Ledger.Model.balanceConservationBefore_measure_le_kerr
assert_axioms Zcash.Security.Ledger.Model.shieldedBalanceCapBefore_measure_le_kerr
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceConservationBefore_measure_le_kerr +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.orchardBalanceIntegrity_measure_le_kerr +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

/-! ## The key-binding arms' ε, discharged

The Balance-subset and Spend Authority key-binding arms' probability in the
key-binding oracle model: `(n + 4)(n + 3)/|RIVK|` for any `n`-query-bounded ledger
adversary, inherited from the key-binding layer's bound at an unchanged query count.
The bounded events are the reductions' own; the composite machine recovers the arm's
witness pair from the adversary's output by an oracle-free computable lookup
(`kbPairOf` from the ledger for Balance; `kwAt` at the announced indices for Spend
Authority), identified with the reduction's pair by the localization theorems. -/

assert_computable Zcash.Security.Ledger.Model.BalanceBreak.kbPair
assert_computable Zcash.Security.Ledger.Model.kbPairOf
assert_axioms Zcash.Security.Ledger.Model.spendPinnedOrBreak_kbPair
assert_axioms Zcash.Security.Ledger.Model.allPinnedOrBreak_kbPair
assert_axioms Zcash.Security.Ledger.Model.balanceSubsetOrBreak_kbPair
assert_computable Zcash.Security.Ledger.Model.kwAt
assert_axioms Zcash.Security.Ledger.Model.spendAuthorityOrBreak_pair
assert_axioms Zcash.Security.Ledger.Model.balanceSubset_keyBindingArm_measure_le
assert_axioms Zcash.Security.Ledger.Model.spendAuthority_keyBindingArm_measure_le

/-! ## The extraction-failure arm's κ, discharged in the oracle model

The conservation reduction's extraction-failure arm, bounded in the challenge-oracle
model: `(qH + 2)/|F| + ε_DL` for any `qH`-query-bounded labeled algebraic ledger
adversary, from the knowledge-error bound at an unchanged query count. The extractor
(`kappaExtractor`) reads the `key` coefficient at the ℛ slot off the representation in
effect at the signature's query point. The composite machine recovers the failing
transaction and its announced representation oracle-free (`failTxOfAnn`, identified with
the reduction's own selection by the localization theorems) and returns its signature
data; the all-prefixes form costs no factor of `k`, because every prefix's failure arm
breaks at the ledger's first imbalanced transaction. -/

assert_computable Zcash.Security.Ledger.Model.kappaPrimitivesAt +choice
assert_computable Zcash.Security.Ledger.Model.kappaShapeAt +choice
assert_computable Zcash.Security.Ledger.Model.kappaBindingAt +choice
assert_computable Zcash.Security.Ledger.Model.kappaExtractor +choice
assert_computable Zcash.Security.Ledger.Model.bvkAt +choice
assert_computable Zcash.Security.Ledger.Model.failTxOfAnn
assert_computable Zcash.Security.Ledger.Model.kappaOut +choice
assert_computable Zcash.Security.Ledger.Model.kappaComposite +choice
assert_axioms Zcash.Security.Ledger.Model.bvkAt_eq
assert_axioms Zcash.Security.Ledger.Model.kappaComposite_queryBound
assert_computable Zcash.Security.Ledger.Model.allConservedOrBreak_extractFail +choice
assert_computable Zcash.Security.Ledger.Model.balanceConservationOrBreak_extractFail +choice
assert_axioms Zcash.Security.Ledger.Model.extractFail_mem_kappaEvent
assert_axioms Zcash.Security.Ledger.Model.balanceConservation_extractFailArm_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceConservationBefore_extractFailArm_measure_le

/-! ## Binding-signature relation reductions

Unlike the ledger break reductions, these depend on `Classical.choice` (`+choice`). It enters
only through erased `Prop` certificate fields (the arithmetic side proofs); the relation
coefficients themselves are direct terms of the inputs, and the plain-`def` check means the data
cannot have been conjured from mere propositional existence. -/

assert_computable Zcash.Security.BindingSignature.NontrivialRelation.ofImbalance +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.ofBundleModImbalance +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.ofBundleIntImbalance +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.ofOrchardImbalance +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.ofSaplingImbalance +choice

/-!
## SNARK soundness stack

The census also carries the SNARK binding and knowledge-soundness reductions and, like the
key-binding and ledger sections above, expresses them through the `Zcash.Meta.AxiomCheck` macros:

* **Computed break reductions** — the data-producing `def`s that extract a discrete-log relation
  from a collision, fold, or peel — get `assert_computable`: a plain `def`, not marked
  `noncomputable`. `Classical.choice` enters only through erased `Prop` certificate fields
  (`+choice`); the relation coefficients are direct terms of the inputs, so the break data cannot
  have been conjured from mere propositional existence. Vesta-instantiated producers additionally
  inherit CompElliptic's `native_decide` curve point-count axiom (`+native`).

  Note that CompElliptic's witnesses are *not* the bulk of what `+native` covers library-wide.
  Exactly three owners across the whole census are CompElliptic's: the two curve point counts
  (`Pallas.q_nsmul_Gpt`, `Vesta.p_nsmul_Gpt`) and the Tonelli–Shanks root-of-unity data
  (`Fields.Pasta.pallasBase`, whose certificate sits in a structure-field auto-param). Every other
  owner — the six fixed-base window tables, the Action gate-coherence and permutation-domain facts,
  the captured fixture claims, the keygen certificate — is this repository's own. Compiler trust
  here is overwhelmingly first-party, not an inherited leaf; each `+native(...)` list names
  precisely which certificates its entry rests on.
* **Theorems** — the probability-layer bounds, the knowledge-soundness and binding endpoints across
  all adversary models, the DL capstones, and the run-time/query-charge lemmas — get
  `assert_axioms`, bounding the trusted base at the standard tier (`propext` / `Classical.choice` /
  `Quot.sound`), with `+native` on the Vesta-instantiated endpoints.
-/

/-! ### Why the two tiers differ: the vacuity witness

`Zcash.Snark.Soundness.Decoded.VacuityWitness` proves that a nontrivial relation among *arbitrary*
Vesta generators exists from the group order alone — no transcript, no verifying key, no acceptance
hypothesis. That is what makes the tier of an endpoint's pin load-bearing rather than cosmetic:

* `assert_computable` endpoints are plain `def`s, so their relation coefficients are terms of their
  inputs and the witness below cannot discharge them. These genuinely exhibit an extractor.
* `noncomputable def` endpoints get only `assert_axioms`. Since the right summand of `… ⊕' relation`
  is unconditionally inhabited, their *statements* do not force the acceptance hypotheses — only
  the proofs actually written do. The pin bounds the trusted base, not the extraction.

This is why the `⊕'`-with-data shape is necessary but not sufficient. The computable straight-line
route and adaptive knowledge bound are stated at `ursOfAugmentedBasis k basis` for a
quantified basis, while the fixture layer separately anchors verifier behavior at `capturedURS`.
`ursOfAugmentedBasis_augmentedBasis` joins the URS component, but there is currently no theorem
constructing the straight-line family for the captured proof. The census therefore makes no claim
of computable extraction at the captured artifacts. -/

assert_axioms Zcash.Snark.ursOfAugmentedBasis_augmentedBasis
assert_axioms Zcash.Snark.nonempty_nontrivialRelation_vesta +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/-! ### Binding reductions from IPA/CommitFold collisions -/

assert_computable Zcash.Snark.NontrivialDLRelation.ofCollision +choice
assert_computable Zcash.Snark.NontrivialDLRelation.ofIpaOpenings +choice

/-! ### Verifier-equation correspondence -/

assert_axioms Zcash.Snark.deployedAccepts_verifierEq

/-! ### Generic binding-reduction break

The combination-collision reduction returns computed relation data as a plain `def`. -/

assert_computable Zcash.NontrivialRelation.ofCombinationCollision +choice

/-! ### AGM / Fiat–Shamir soundness

The AGM kernels compute representations, openings, and relations as data (`assert_computable`); the
probability layer and the binding endpoints are theorems (`assert_axioms`). -/

assert_computable Zcash.Snark.discreteLogOfBasis_of_relation +choice
assert_computable Zcash.Snark.discreteLogOfChallenge_of_relation +choice
assert_computable Zcash.Snark.programmedExtractOrMiss +choice
assert_computable Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness +choice
assert_computable Zcash.Snark.relationWitnessOfCollision +choice
assert_computable Zcash.Snark.discreteLogOfAugmentedRelationAtChallenge +choice
assert_computable Zcash.Snark.separateOrRelationWitness +choice
assert_computable Zcash.Snark.algebraicPowerBatchWithSourceOrRelation +choice
assert_computable Zcash.Snark.finForallOrRelationWitness
assert_computable Zcash.Snark.constructIntermediateSets_comm_route +choice
assert_computable Zcash.Snark.deployed_slot_route_of_checks +choice
assert_computable Zcash.Snark.deployedRouteSelectorOfSpecs +choice
assert_computable Zcash.Snark.deployedConstraintQuotientAgreementOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedConstraintQuotientFinder +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.decodedQuotientEqReassembledOrRelationWitness +choice
assert_computable Zcash.Snark.DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness +choice
assert_computable Zcash.Snark.x4BatchCommitments +choice
assert_computable Zcash.Snark.deployedSetMemberCommitments +choice
assert_computable Zcash.Snark.deployedX4AlgebraicBatchOrRelation +choice
assert_computable Zcash.Snark.deployedX4AlgebraicBatchWithSourceOrRelation +choice
assert_computable Zcash.Snark.deployedX1AlgebraicBatchWithSourceOrRelation +choice
assert_computable Zcash.Snark.deployedX1BatchOfCoveredWithSourceOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedX4ColumnRepresentationsOfCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedX4BatchOfCoveredOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedX4BatchOfCoveredWithSourceOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedRootOutcomeOfCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedRootFSFamily.ofCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedConstraintFSFamily.ofCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedConstraintFinderOfOutcome +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.OrchardUniformURSIdentification +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchardGeneratorROSetup
assert_axioms Zcash.Snark.orchardGeneratorROBasis
assert_axioms Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicRelationWitness.augment
assert_axioms Zcash.Snark.bindingWin_unbounded_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.queryCharge
assert_axioms Zcash.Snark.queryCharge_sum_mul_le
assert_axioms Zcash.Snark.le_queryCharge_of_mem_queries
assert_axioms Zcash.Snark.mem_queries_dedup
assert_axioms Zcash.Snark.applyUpdates_apply_mem_nodup
assert_axioms Zcash.Snark.queryCharge_sum_mul_le_table_budget
assert_axioms Zcash.Snark.steeredCharge_context_sum_mul_le
assert_axioms Zcash.Snark.steeredCharge_context_sum_mul_le_table_budget
assert_axioms Zcash.Snark.steeredCharge_sum_mul_le
assert_axioms Zcash.Snark.OracleComp.queries_queryList
assert_axioms Zcash.Snark.OracleComp.queries_bind
assert_axioms Zcash.Snark.OracleComp.mem_queries_completing
assert_axioms Zcash.Snark.OracleComp.restrictSum
assert_axioms Zcash.Snark.fsWinsFull_restrictSum_le
assert_axioms Zcash.Snark.uniformURS_basis_transfer +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicPoint.point_eq_components +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Msm.eval_repr +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.RepresentedMultiopen.ofCoveredList +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicWfProof.ofRepresented +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.assembleQueries_points_mem
assert_axioms Zcash.Snark.constructIntermediateSets_ref_mem
assert_axioms Zcash.Snark.multiopenMsm_points_mem
assert_axioms Zcash.Snark.AlgebraicWfProof.ofStandard +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.OracleComp.reachSet
assert_axioms Zcash.Snark.OracleComp.run_congr_reachSet
assert_axioms Zcash.Snark.OracleComp.restrictTo
assert_axioms Zcash.Snark.OracleComp.splitDomain
assert_axioms Zcash.Snark.finite_domain_restriction
assert_axioms Zcash.Snark.fsWinsFull_mapDomain_measure_eq
assert_axioms Zcash.Snark.fsWinsFull_splitDomain
assert_axioms Zcash.Snark.fsWinsFull_unbounded_measure_le
assert_axioms Zcash.Snark.truncateTranscript
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog +choice
assert_axioms Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_axioms Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog
assert_axioms Zcash.Snark.programmedRelSet_card
assert_axioms Zcash.Snark.programmedRelSet_subset_win_union_miss
assert_axioms Zcash.Snark.missSet_card_le
assert_axioms Zcash.Snark.relation_prob_le_of_textbookDL
assert_axioms Zcash.Snark.programmedRelSetWithCoins_card
assert_axioms Zcash.Snark.programmedRelSetWithCoins_subset_win_union_miss
assert_axioms Zcash.Snark.missSetWithCoins_card_le
assert_axioms Zcash.Snark.relationWithCoins_prob_le_of_textbookDL
assert_axioms Zcash.Snark.truncateRelationFinder
assert_axioms Zcash.Snark.truncatedRelationFinderCalls
assert_axioms Zcash.Snark.truncatedRelationFinderCalls_le
assert_axioms Zcash.Snark.TextbookDLWithCoinsFixedCallsAdvantageLE
assert_axioms Zcash.Snark.TextbookDLWithCoinsTruncatedAdvantageLE
assert_axioms Zcash.Snark.textbookDLWithCoinsTruncatedAdvantageLE_iff
assert_axioms Zcash.Snark.RelationFinderExpectedCallsLE
assert_axioms Zcash.Snark.relationFinderCallTail
assert_axioms Zcash.Snark.relSetWithCoins_subset_truncate_union_tail
assert_axioms Zcash.Snark.relationFinderCallTail_prob_le
assert_axioms Zcash.Snark.relationWithCoins_prob_le_of_truncated_textbookDL
assert_axioms Zcash.Snark.orchard_relation_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.commitment_binding_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/-! ### Multiopen decode and straight-line composition

The decode layer covers Vandermonde column recovery, the `x₄` flat-power-batch collapse, and the
straight-line extraction composition. Every break the deployed route charges to DLOG is computed
relation data, censused below through explicit `PSum` outcomes and computable finders. Theorems throughout, so
`assert_axioms`, with `+native` on the Vesta-instantiated endpoints. -/

-- The decode layer (`Soundness.Multiopen.Decode`/`Deployed`): the Vandermonde recovery of the
-- column witnesses, the deployed x4 collapse proved to be a flat power batch, and the two-level
-- binding of the extracted witness to the member commitments.
assert_axioms Zcash.Snark.deployedCommitment_x4_batch
assert_axioms Zcash.Snark.multiopenValue_x4_batch
-- The multiopen support modules, pinned directly rather than transitively through the capstones
-- above. `Opened` holds the augmented batch/member interfaces and canonical column decode;
-- `RPoly` the interpolation/power-form algebra; `Compat` the Msm-evaluation and two-openings
-- binding lemmas; `ValueCheckDeployed` the deployed point sets.
-- A stray axiom here would surface at a capstone, but only these pins name its declaration.
assert_axioms Zcash.Snark.vandermonde_decode_map
assert_axioms Zcash.Snark.vandermonde_reconstruct_map
assert_axioms Zcash.Snark.openedColumnDecode
assert_axioms Zcash.Snark.rotatedFeed
assert_axioms Zcash.Snark.poly_eq_of_agree_on_family
assert_axioms Zcash.Snark.foldl_range_add_eq_sum
assert_axioms Zcash.Snark.foldl_range_guardProd_eq_prod
assert_axioms Zcash.Snark.guardProd_eq_prod_erase
assert_axioms Zcash.Snark.lagrangePoly
assert_axioms Zcash.Snark.lagrangePoly_eval_node
assert_axioms Zcash.Snark.lagrangePoly_eval
assert_axioms Zcash.Snark.foldl_mul_inv_eq_prod
assert_axioms Zcash.Snark.multiopenEval_powerForm
assert_axioms Zcash.Snark.coeffs_zero_of_power_sum_vanishes
assert_axioms Zcash.Snark.lagrangePoly_natDegree_lt
assert_axioms Zcash.Snark.Msm.eval_zero
assert_axioms Zcash.Snark.Msm.eval_scale
assert_axioms Zcash.Snark.Msm.eval_add
assert_axioms Zcash.Snark.deployedSetPts
assert_axioms Zcash.Snark.deployedAllPts
assert_axioms Zcash.Snark.deployedSetPts_subset
assert_axioms Zcash.Snark.deployed_query_point_mem
-- The good-challenge production (`Soundness.GoodChallenge`): the Schwartz-Zippel exclusion budget
-- and the pigeonhole that produces an accepting challenge outside the bad set.
assert_axioms Zcash.Snark.uniformChallenge_szBadSet
assert_axioms Zcash.Snark.uniformChallenge_szGoodSet
assert_axioms Zcash.Snark.uniformChallenge_quotient_szBadSet
assert_axioms Zcash.Snark.uniformChallenge_szBadSet_union
assert_axioms Zcash.Snark.exists_accepting_good_challenge
assert_axioms Zcash.Snark.exists_accepting_good_challenge_quotient
-- Deterministic verifier routing used by the rewind-free deployed constraint decoder.
assert_axioms Zcash.Snark.vanishing_query_mem_assembleQueries
assert_axioms Zcash.Snark.assembleQueries_vanishingH_unique
assert_axioms Zcash.Snark.constructIntermediateSets_unique_comm_routed
assert_axioms Zcash.Snark.vanishing_slot_routed
assert_axioms Zcash.Snark.hfold_of_expectedHEval_binding
assert_axioms Zcash.Snark.hfold_of_vanishing_slot_binding
assert_axioms Zcash.Snark.deployedAccepts_xn_ne_one
assert_axioms Zcash.Snark.deployedAccepts_pipeline
assert_axioms Zcash.Snark.deployed_member_commitment_eq_assembled
assert_axioms Zcash.Snark.lagrangeBasisPoly_eval
assert_axioms Zcash.Snark.lagrange_bind_derived
-- The permutation and lookup arguments folded into the constraint model: the verifier's expression
-- list is the generic builder run on its own claimed evaluations, the same builder over column
-- polynomials evaluates back onto it, and the fold equation therefore needs no fingerprint premise.
assert_axioms Zcash.Snark.permutationExpressions_map
assert_axioms Zcash.Snark.lookupExpressions_map
assert_axioms Zcash.Snark.subProofConstraints_map
assert_axioms Zcash.Snark.allConstraints_map
assert_axioms Zcash.Snark.subProofExpressions_eq
assert_axioms Zcash.Snark.allExpressions_eq
assert_axioms Zcash.Snark.eval_constraintPolys
assert_axioms Zcash.Snark.eval_combineConstraints
assert_axioms Zcash.Snark.eval_combineConstraints_deployed
assert_axioms Zcash.Snark.hfold_of_constraint_polys_of_xn_ne_direct
assert_axioms Zcash.Snark.constraints_supply_of_deployedAlgebraicDecode
-- The permutation and lookup arguments closed from the verifier's own row checks: the combined
-- check splits into its parts, the running product telescopes across the rows, two challenge root
-- counts turn the product into a multiset identity, and the existing structural theorems turn that
-- into the copy constraints and the lookup inclusion.
assert_axioms Zcash.Snark.constraints_dvd_of_good_y
assert_axioms Zcash.Snark.telescope_running_product
assert_axioms Zcash.Snark.grandProduct_eq_or_cell_eq_zero
assert_axioms Zcash.Snark.multiset_pair_eq_of_prod_eval_eq
assert_axioms Zcash.Snark.cellPairs_eq_of_running_product
assert_axioms Zcash.Snark.perm_copy_constraints_of_running_product
assert_axioms Zcash.Snark.lookup_multisets_of_prod_eval_eq
assert_axioms Zcash.Snark.lookup_multisets_of_diff_eq_zero
assert_axioms Zcash.Snark.lookup_subset_of_components
assert_axioms Zcash.Snark.lookup_subset_of_prod_eval_eq
-- The deployed row reading: the step rule's folds are running products, the boundary rules pin the
-- product at the first and last rows, and the cell names separate. These are theorems about
-- `permChunkExpression` itself, so the chain above starts at the verifier's own constraint list.
assert_axioms Zcash.Snark.permChunk_left_eq_prod
assert_axioms Zcash.Snark.permChunk_right_eq_prod
assert_axioms Zcash.Snark.permChunkExpression_eq
assert_axioms Zcash.Snark.eval_eq_zero_of_dvd_vanishing
assert_axioms Zcash.Snark.perm_row_recurrence
assert_axioms Zcash.Snark.running_product_start
assert_axioms Zcash.Snark.running_product_end
assert_axioms Zcash.Snark.name_injective_of_coset
assert_axioms Zcash.Snark.deployed_perm_copy_constraints
-- Locating a single rule inside the verifier's flat constraint list, fixing the permutation sets to
-- committed running products, and chaining the two: the copy constraints now follow from the
-- polynomial constraint identity itself, with no hypothesis about the shape of the checks.
assert_axioms Zcash.Snark.permChunkExpression_mem_permutationExpressions
assert_axioms Zcash.Snark.start_mem_permutationExpressions
assert_axioms Zcash.Snark.end_mem_permutationExpressions
assert_axioms Zcash.Snark.mem_subProofConstraints_of_mem_permutationExpressions
assert_axioms Zcash.Snark.mem_allConstraints_of_mem_subProofConstraints
assert_axioms Zcash.Snark.mem_constraintPolys_of_mem_permutationExpressions
assert_axioms Zcash.Snark.head?_deployedPermSets
assert_axioms Zcash.Snark.getLast?_deployedPermSets
assert_axioms Zcash.Snark.deployed_copy_constraints_of_identity
-- The same for the lookup argument: its five rules located in the list, read row by row, and
-- chained to the inclusion.
assert_axioms Zcash.Snark.lookupExpressions_eq
assert_axioms Zcash.Snark.mem_subProofConstraints_of_mem_lookupExpressions
assert_axioms Zcash.Snark.mem_constraintPolys_of_mem_lookupExpressions
assert_axioms Zcash.Snark.running_product_end_flipped
assert_axioms Zcash.Snark.lookup_row_recurrence
assert_axioms Zcash.Snark.lookup_row_zero
assert_axioms Zcash.Snark.lookup_row_step
assert_axioms Zcash.Snark.lookup_rules_dvd_of_identity
assert_axioms Zcash.Snark.deployed_lookup_subset_of_identity
assert_axioms Zcash.Snark.deployed_lookup_relation_of_identity
-- Decompression: the θ-compressed membership becomes membership of whole rows, since the
-- compression is the fold polynomial of the row's values and a good θ separates distinct tuples.
assert_axioms Zcash.Snark.foldPoly_sub
assert_axioms Zcash.Snark.tuple_eq_of_foldPoly_eval_eq
assert_axioms Zcash.Snark.compress_eval_eq_foldPoly
assert_axioms Zcash.Snark.deployed_lookup_tuple_of_identity
-- Every new challenge surface priced the way `hgood` is: a uniform-challenge measure bound per
-- root-set event — the fold split's `y`, the bridge's `β` and `γ`, the vanishing-factor escapes,
-- and the decompression's pairwise `θ`. Sequential conditioning across the squeezes is the same
-- coupling hook `hgood` carries, documented with the `hfold`/`hgood` surfaces.
assert_axioms Zcash.Snark.uniformChallenge_szBadSet_iUnion_le
assert_axioms Zcash.Snark.goodY_failure_measure_le
assert_axioms Zcash.Snark.perm_gamma_failure_measure_le
assert_axioms Zcash.Snark.perm_beta_failure_measure_le
assert_axioms Zcash.Snark.escape_measure_le
assert_axioms Zcash.Snark.theta_failure_measure_le
/-! ### Break-branch machinery — computed

These checks pin each charged relation finder as a plain executable `def`. `+choice` is allowed
only through erased proof fields. Noncomputable events and probability theorems are censused
separately with `assert_axioms`. -/

assert_computable Zcash.Snark.bindOrRelationWitness
assert_computable Zcash.Snark.finForallOrRelationWitness
assert_computable Zcash.Snark.finForallOption
assert_computable Zcash.Snark.listForallOrRelationWitness
assert_computable Zcash.Snark.boundedForallOrRelationWitness
assert_computable Zcash.Snark.szBadSetAvoidance? +choice
assert_computable Zcash.Snark.foldSplitAvoidance? +choice
assert_computable Zcash.Snark.ActionTerminal.foldSplitAvoidance? +choice
assert_computable Zcash.Snark.resolverPermutationGoodChallenges? +choice
assert_computable Zcash.Snark.resolverPermutationChallengeExclusions? +choice
assert_computable Zcash.Snark.resolverLookupGoodChallenges? +choice
assert_computable Zcash.Snark.resolverLookupBundleExclusions? +choice
assert_computable Zcash.Snark.EnabledLookup.thetaAvoidance? +choice
assert_computable Zcash.Snark.TopLevelLookup.topLevelLookupChallengeExclusions? +choice
assert_computable Zcash.Snark.FullCircuitSatisfaction.of_components_or_bad
assert_computable Zcash.Snark.declaredCopies_satisfied_or_bad_of_replay +choice
assert_computable Zcash.Snark.copy_constraints_or_bad_of_replay +choice
assert_computable Zcash.Snark.CopyReplayWitness.constraints_or_bad +choice
assert_computable Zcash.Snark.FullCircuitBridge.satisfaction_or_bad +choice
assert_computable Zcash.Snark.FullCircuitBridge.constraints_or_bad +choice
assert_computable Zcash.Snark.decodedPolynomialResolver_opens_or_relation +choice

-- The accepted-route terminal converts canonical `CircuitSat` into the circuit's statements with
-- no free semantic callback, decoder, or selected-column feed.
assert_axioms Zcash.Snark.topLevelBundleStatement_or_bad_of_constraintSatisfaction +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_computable Zcash.Snark.topLevelStatements_or_relation_of_circuitSat +choice +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_computable Zcash.Snark.topLevelStatements_or_relation_of_decodedMemberPolynomial_eq +choice +native(
  CompElliptic.Fields.Pasta.pallasBase)
-- The last links: the point check lifted to the polynomial identity, the permutation taken to be the
-- one keygen builds from the circuit's copy constraints, the cells of every chunk covered at once,
-- and circuit satisfaction defined by the whole constraint list rather than the gates alone.
assert_axioms Zcash.Snark.constraint_identity_of_hfold
assert_axioms Zcash.Snark.declared_equalities_of_running_product
assert_axioms Zcash.Snark.deployed_declared_equalities_of_identity
assert_axioms Zcash.Snark.prod_map_chunkCellPairs
assert_axioms Zcash.Snark.perm_copy_constraints_of_chunk_products
assert_axioms Zcash.Snark.chunkName_injective_of_coset
assert_axioms Zcash.Snark.deployed_declared_equalities_of_identity_chunks
assert_axioms Zcash.Snark.circuitSatViaConstraints_of_check
-- Closing the loop: the capstone hands over an opening paired with satisfaction of the whole
-- constraint list, and the two arguments' relations are read back out of that same predicate.
assert_axioms Zcash.Snark.snarkRelation_constraints
assert_axioms Zcash.Snark.declared_equalities_of_circuitSat
assert_axioms Zcash.Snark.lookup_relation_of_circuitSat
assert_axioms Zcash.Snark.lookup_tuple_of_circuitSat
-- Several permutation chunks, not one: the chaining rule located in the list, read at row zero, and
-- the chunks flattened into a single running product so the permutation acts on every cell.
assert_axioms Zcash.Snark.chain_mem_permutationExpressions
assert_axioms Zcash.Snark.running_product_chain
assert_axioms Zcash.Snark.deployed_copy_constraints_of_identity_chunks
assert_axioms Zcash.Snark.hgood_of_good_challenge
-- Product-measure lifting, now used by the direct pinned-root composition.
assert_axioms Zcash.Snark.independentProductPMF_fiber_bound
-- Acceptance through `assemble?` and its explicit verifier equation.
assert_axioms Zcash.Snark.fullAlgebraicAcceptDeployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.fullAlgebraicAccept_of_deployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtractionFailureEventDeployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Rewind-free AGM unbatching and its direct additive root pricing.
assert_axioms Zcash.Snark.algebraicBatchErrorPolynomial_eval
assert_axioms Zcash.Snark.algebraicBatchErrorPolynomial_natDegree_le
assert_axioms Zcash.Snark.algebraicBatch_values_of_errorPolynomial_eq_zero
assert_axioms Zcash.Snark.algebraicBatch_badSet_measure_le
assert_axioms Zcash.Snark.deployedX4AlgebraicValues_of_good
assert_axioms Zcash.Snark.deployedClearedQuotientIdentity_of_good_x3
assert_axioms Zcash.Snark.deployedAggregateNodeBinding_of_good_x2
assert_axioms Zcash.Snark.deployedMemberNodeBinding_of_good_x1
assert_axioms Zcash.Snark.deployedMemberNodeBinding_of_good_challenges
assert_axioms Zcash.Snark.xEscTable_measure_le
assert_axioms Zcash.Snark.xEscAtPoint_measure_le
assert_axioms Zcash.Snark.PinnedRootEvent.landing_measure_le
assert_axioms Zcash.Snark.PinnedRootFamily.landing_measure_le
assert_axioms Zcash.Snark.deployedRootBad_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The shape-only root budget is monotone, so its consensus-maximum specialization bounds every
-- smaller captured Orchard bundle rather than only the exact endpoint shape.
assert_axioms Zcash.Snark.algebraicRootBudget_mono
assert_axioms Zcash.Snark.DeployedRootPrefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedRootSqueezeInvariance +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedRootSqueezeInvariance_of_prefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedRootOnlineTrace.toSqueezeInvariance +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedDeployedRootFSFamily.pinned +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedConstraintXOnlineTrace.toPinning +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedDeployedConstraintFSFamily.pinnedX +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.tableReadingPinnedRootEvent
assert_axioms Zcash.Snark.tableReadingPinnedRootEvent_landing_measure_le
assert_axioms Zcash.Snark.deployedRootEventBudget_sum_le
assert_axioms Zcash.Snark.badX_le_via_squeeze_prefixed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Squeeze-point toolkit: prefix-determinism makes the `x` point stable under self-reprogramming.
-- This is not the live constraint schedule's chronology discharge: point stability alone does not
-- prove that the bad set was fixed before `x`.
assert_axioms Zcash.Snark.hstab_of_xPrefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Prefix injectivity at the multiopen squeeze points (`FiatShamir.Adversary.PreIpa`): each point
-- pins every field absorbed before it — the toolkit for the deployed squeeze-invariance
-- schedules, which need each root-set datum emitted strictly before its own squeeze.
assert_axioms Zcash.Snark.preXSqueezePoint_inj
assert_axioms Zcash.Snark.preX1SqueezePoint_inj
assert_axioms Zcash.Snark.preX2SqueezePoint_inj
assert_axioms Zcash.Snark.preX3SqueezePoint_inj
assert_axioms Zcash.Snark.preX4SqueezePoint_inj
-- The degree walk (`Soundness.DegreeWalk`): every constraint family's polynomial stays under an
-- explicit cap — gates by `Expr.degreeBound`, permutation chunks by width, lookups by their
-- compressed expressions — the combined bound the `x`-squeeze schedule's `epsilonX` prices.
assert_axioms Zcash.Snark.natDegree_combineConstraints_le
-- The quantified random match, generic half (`Fingerprint/SampleSpace`,
-- `Fingerprint/Rational/{GoodEvent,Representation,Family}`, `Fingerprint/{Match,Epsilon}`): the
-- structured sample space rebuilds a well-formed proof
-- string at every point; the good event's enumerated denominator factors are individually
-- nonzero, jointly priced by per-factor Schwartz–Zippel, and nonvanishing under products; the ε
-- theorem bounds a competing coefficient family's agreement with `assemble?` at a uniform
-- point by `(D + Σ totalDegree (denFactors vk)) / p`; the challenge-restricted variant pins
-- the proof-string slots to an arbitrary assignment and prices the same bound over the
-- challenge coordinates alone — the factors are challenge-only and restriction does not raise
-- degree; the cross-denominator variants admit a competing family with its own denominators
-- from the enumerated factor closure, cross-multiplied (`RationalCoeffFamily.mulDen`) to the
-- summed budget `D + Dden`; and a `Perm` of pair lists with
-- duplicate-free second components is realized by the base-matching index bijection — the
-- `Perm`→positional bridge the per-capture `fingerprint_matches_positional` facts instantiate.
assert_axioms Zcash.Snark.proofStringWellFormed_toProofString
assert_axioms Zcash.Snark.toProofString_ofInputs
assert_axioms Zcash.Snark.denFactors_ne_zero
assert_axioms Zcash.Snark.denFactors_totalDegree_sum_le
assert_axioms Zcash.Snark.den_eval_ne_zero
assert_axioms Zcash.Snark.fingerprint_schwartz_zippel_index
assert_axioms Zcash.Snark.card_exists_eval_zero_le
assert_axioms Zcash.Snark.goodEvent_compl_card_le
assert_axioms Zcash.Snark.Point.merge_restrict
assert_axioms Zcash.Snark.totalDegree_aeval_le_of_le_one
assert_axioms Zcash.Snark.eval_restrictSlots
assert_axioms Zcash.Snark.restrictSlots_totalDegree_le
assert_axioms Zcash.Snark.restrictSlots_denFactors_ne_zero
assert_axioms Zcash.Snark.restrictSlots_denFactors_totalDegree_sum_le
assert_axioms Zcash.Snark.goodEvent_merge_iff
assert_axioms Zcash.Snark.goodEvent_merge_compl_card_le
assert_axioms Zcash.Snark.competing_coefficient_family_agreement_le
assert_axioms Zcash.Snark.competing_coefficient_family_agreement_le_challengesOnly
assert_axioms Zcash.Snark.RationalCoeffFamily.mulDen
assert_axioms Zcash.Snark.competing_coefficient_family_agreement_le_denClosure
assert_axioms Zcash.Snark.competing_coefficient_family_agreement_le_challengesOnly_denClosure
assert_axioms Zcash.Snark.perm_reindex_of_nodup_snd
assert_axioms Zcash.Snark.msmMatch_other_reindex_of_nodup
-- The query-side representation walk (`Fingerprint/Rational/ConstraintWalk`): the constraint list
-- factors through fixed represented functions over the Lagrange denominator, its length is the
-- shape-polynomial `constraintBudget`, and `expected_h_eval` is represented over the vanishing
-- denominator at the `hEvalBudget` degree cap.
assert_axioms Zcash.Snark.allExpressions_listRep
assert_axioms Zcash.Snark.allExpressions_length
assert_axioms Zcash.Snark.expectedHEval_rep
-- Grouping stability (`Verifier/GroupingRef`, `Fingerprint/Rational/GroupingTable`): the multiopen
-- grouping is natural in a provenance-preserving reference relabeling (hypothesis-free), the
-- reference of the assembled queries is one fixed table on the good event, and `assemble?`
-- returns `some` at every good point — all five gates discharged.
assert_axioms Zcash.Snark.constructIntermediateSets_ref_ids
assert_axioms Zcash.Snark.constructIntermediateSets_ref_points
assert_axioms Zcash.Snark.constructIntermediateSets_ref_sets
assert_axioms Zcash.Snark.hasDuplicateCommitmentPoint_ref
assert_axioms Zcash.Snark.refQueries_eq_refTable
assert_axioms Zcash.Snark.grouped_ids_eq
assert_axioms Zcash.Snark.grouped_points_eq
assert_axioms Zcash.Snark.grouped_sets_eq
assert_axioms Zcash.Snark.assembleAt_some
-- The IPA scalar walk (`Fingerprint/Rational/IpaWalk`): the deployed grouping's members carry
-- zero scalar blocks (hypothesis-free), so the assembled `w`/`u`/`g` scalars take their closed
-- IPA forms, each represented — `computeB` at `2^k + k + 1`, the `computeS` entries at `1 + k`,
-- and every `g`-coordinate given a representation of the opening value.
assert_axioms Zcash.Snark.assembleQueries_grouped_gwuZero
assert_axioms Zcash.Snark.assembleFinalMsm_wScalar_of_gwuZero
assert_axioms Zcash.Snark.assembleFinalMsm_uScalar_of_gwuZero
assert_axioms Zcash.Snark.assembleFinalMsm_gScalars_of_gwuZero
assert_axioms Zcash.Snark.computeB_rep
assert_axioms Zcash.Snark.computeS_getD_rep
assert_axioms Zcash.Snark.wScalar_rep
assert_axioms Zcash.Snark.uScalar_rep
assert_axioms Zcash.Snark.gScalars_coord_rep
-- The opening walk (`Fingerprint/Rational/OpeningWalk`): the claimed-evaluation stream factors
-- through fixed represented functions, the barycentric interpolant and per-set quotients clear
-- into the enumerated factors, and the multiopen opening value — exactly as `assembleFinalMsm`
-- invokes it — is represented over `openDen` at the `vBudget` cap on the good event.
assert_axioms Zcash.Snark.assembleQueries_map_eval
assert_axioms Zcash.Snark.queryEval_rep
assert_axioms Zcash.Snark.lagrangeEval_rep
assert_axioms Zcash.Snark.openingValue_eq
assert_axioms Zcash.Snark.openingValue_rep
-- The walk capstone (`Fingerprint/Rational/Capstone`): the assembled `other` coefficient
-- stream equals one fixed positional function list on the good event, every coordinate's
-- coefficient is represented at the `msmDegreeBudget`/`msmDenBudget` caps, and the whole
-- family packages into the `RationalCoeffFamily` the ε theorem consumes — from
-- `VkSymbolicFacts` plus the three walk hypotheses alone.
assert_axioms Zcash.Snark.assembleQueries_commitment_char
assert_axioms Zcash.Snark.ipaFold_other
assert_axioms Zcash.Snark.assembleAt_other_map_fst
assert_axioms Zcash.Snark.assembleAt_other_length
assert_axioms Zcash.Snark.otherCoeffFns_rep
assert_axioms Zcash.Snark.coordFn_rep
assert_axioms Zcash.Snark.coordFn_agrees
assert_axioms Zcash.Snark.assembleCoeffFamily
-- The schedule, priced (`Composition.ScheduleBudget`): the committed carriers stay under the
-- walk's caps, root witnesses at one table share the family's own outcome, and the schedule
-- constructor discharges `measure_le` outright.
-- The captured family carries an explicit fresh-query `OracleComp` trace and derives exact
-- pinning from its query log. The lower-level direct-pinning constructor remains generic plumbing;
-- it is not a standalone captured-capstone premise.
assert_axioms Zcash.Snark.natDegree_committedPreXConstraintDifference_le
assert_axioms Zcash.Snark.natDegree_deployedConstraintDifferencePreX_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintXBadSet_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedConstraintXPrefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintXPinning_of_prefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintXSqueezeSchedule_of_pinned +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintXSqueezeSchedule_of_prefixDetermined +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The pinned-root witness family (`AGM.PinnedRootWitness`): the zero data over the degenerate
-- shape, whose assembled multiopen commitment is the zero point for every basis and record.
assert_axioms Zcash.Snark.multiopenCommitment_witness_zero +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.witnessProof +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.witnessFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The actual strict-prefix property is satisfiable: the constant family's root sets are empty
-- except at `x₃`, whose point set consumes only earlier answers.  It is packaged as an inhabitant
-- of `ComputedDeployedRootFSFamily`; the weaker invariance theorem is a corollary.
assert_axioms Zcash.Snark.witnessFamily_reads_update +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedRootBad_witness +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedAllPts_x3_blind
assert_axioms Zcash.Snark.deployedAllPts_congr_preMultiopen
assert_axioms Zcash.Snark.deployedRootPrefixDetermined_witness +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.witnessOnlineMemberFamily +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.witnessDeployedRootFamily +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The constraint-level and straight-line interfaces are inhabited on the same witness
-- (`Composition.StraightLineWitness`): the constraint difference of the zero data is the zero
-- polynomial, so the constraint-`x` stage is a read-free executable computation, and the
-- degenerate shape's IPA trace is round-free.
assert_axioms Zcash.Snark.deployedConstraintDifferencePreX_witness +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The total pre-x constraint event: the difference from the family's own
-- source, the unguarded bad set, and the zero prover's any-shape constraint-x stage.
assert_axioms Zcash.Snark.deployedConstraintDifferencePreX +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedOnlineMemberFSFamily.membersCovered_wrapped +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedOnlineMemberFSFamily.canonical_wrapped +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroExplicitConstraintDifference
assert_axioms Zcash.Snark.zeroConstraintDifference_explicit +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstConstraintXTrace +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstStraightLineDeployedFamily +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Adversary coverage: the sequential online-AGM prover model and its lifting to
-- the staged family; the total difference reads only the pre-x view.
assert_axioms Zcash.Snark.committedPreXConstraintDifference_ps_congr
assert_axioms Zcash.Snark.committedPreXConstraintDifference_challenge_congr
assert_axioms Zcash.Snark.PreXView.difference +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialPreXProver.view_difference_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialPreXProver.toConstraintXTrace +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialPreXProver.lift +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialPreXProver.lift_adversary +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialPreXProver.lift_Q +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Uniform sequential cuts, the first brick: prefix-determinism at every squeeze index
-- is derived from the prover's execution order, never assumed.
assert_axioms Zcash.Snark.OracleComp.run_congr_of_agree
assert_axioms Zcash.Snark.SequentialCut.toPrefixDeterminedAt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- State surfaces: a semantic exclusion set read off the cut state costs
-- `(Q + 1) * epsilon`, with stability derived from the cut's execution order.
assert_axioms Zcash.Snark.SequentialCut.state_stable +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent_basis_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The state-surface discharge: each Action semantic failure event contained in
-- its cut state surface and priced at `(Q + 1) * epsilon`, views supplying every read.
assert_axioms Zcash.Snark.ActionTerminal.vkAt +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.semanticChRecord
assert_axioms Zcash.Snark.ActionTerminal.semanticChRecord_theta
assert_axioms Zcash.Snark.ActionTerminal.semanticChRecord_beta
assert_axioms Zcash.Snark.ActionTerminal.straightLineRunRecord_read +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailureEvent_subset +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailure_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaFailureEvent_subset +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaFailure_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaFailureEvent_subset +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaFailure_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionXYFailureEvent_subset +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionXYFailure_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Per-state probability bounds: each surface premise reduced to the staged counts.
assert_axioms Zcash.Snark.ActionTerminal.actionThetaBadSet_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaBadSets_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaBadSets_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionYBadSet_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Challenge reads: what each semantic exclusion set consumes — congruences over
-- polynomial maps agreeing on the named slot classes and over the named earlier challenges.
assert_axioms Zcash.Snark.CommitmentId.isColumnInput
assert_axioms Zcash.Snark.CommitmentId.isPermutationInput
assert_axioms Zcash.Snark.CommitmentId.isLookupInput
assert_axioms Zcash.Snark.CommitmentId.isColumnInput.toPermutation
assert_axioms Zcash.Snark.CommitmentId.isColumnInput.toLookup
assert_axioms Zcash.Snark.permutationColumnPolynomialOfResolver_congr
assert_axioms Zcash.Snark.resolverPermutationPairs_congr
assert_axioms Zcash.Snark.resolverPermutationBetaBadSet_congr
assert_axioms Zcash.Snark.resolverPermutationGammaBadSet_congr
assert_axioms Zcash.Snark.allResolverPermutationBetaBadSet_congr
assert_axioms Zcash.Snark.allResolverPermutationGammaBadSet_congr
assert_axioms Zcash.Snark.fixedQueryFeedOfResolver_congr
assert_axioms Zcash.Snark.adviceQueryFeedOfResolver_congr
assert_axioms Zcash.Snark.instanceQueryFeedOfResolver_congr
assert_axioms Zcash.Snark.lookupInputPolyOfResolver_congr
assert_axioms Zcash.Snark.lookupTablePolyOfResolver_congr
assert_axioms Zcash.Snark.resolverLookupProductDifference_congr
assert_axioms Zcash.Snark.resolverLookupBetaBadSet_congr
assert_axioms Zcash.Snark.resolverLookupGammaBadSet_congr
assert_axioms Zcash.Snark.allResolverLookupBetaBadSet_congr
assert_axioms Zcash.Snark.allResolverLookupGammaBadSet_congr
assert_axioms Zcash.Snark.resolverEnvironment_congr
assert_axioms Zcash.Snark.TopLevelLookup.thetaBadSet_congr
-- Census the bundled sequential adversary and its resource arithmetic.
assert_axioms Zcash.Snark.resolverPermutationCell_card
assert_axioms Zcash.Snark.TopLevelLookup.thetaBudget_eq
assert_axioms Zcash.Snark.ActionTerminal.ActionSequentialCuts +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.ActionSequentialCuts.theta_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.ActionSequentialCuts.beta_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.ActionSequentialCuts.gamma_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.ActionSequentialCuts.xy_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.deployedConstraintXBadSet_witness +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessConstraintXTrace +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessDeployedConstraintFamily +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessStraightLineIpaTrace +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessStraightLineDeployedFamily +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The shape-generic keystone for a captured-shape constant family's staged IPA trace: a
-- zero-coordinate proof pins the zero polynomial at every round.
assert_axioms Zcash.Snark.ipaDiscrepancyPolynomialAt_zero
assert_axioms Zcash.Snark.straightLineIpaRootPolynomial_of_zero_coordinates +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The constant-walk generalization: with sub-proofs the multiopen value survives, and every
-- IPA root polynomial is the linear C(initial discrepancy) * X.
assert_axioms Zcash.Snark.ipaDiscrepancyStep_const
assert_axioms Zcash.Snark.ipaDiscrepancyPolynomialAt_const
assert_axioms Zcash.Snark.straightLineInitialDiscrepancy_of_zero_coordinates +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.straightLineIpaRootPolynomial_of_zero_group_coordinates +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The constant-walk staged IPA trace at any shape: the zero prover's rounds contribute
-- nothing, so the staged polynomial is C(-(nu10 * v)) * X with v its multiopen value.
assert_axioms Zcash.Snark.zeroWfProof_straightLineIpaRootPolynomial_const +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstIpaStage +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstIpaStage_agrees +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstIpaStage_fresh +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstStraightLineIpaTrace +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The zero-data assembly keystone (`Soundness/ZeroData`) and the constant zero prover family at
-- any shape (`Soundness/AGM/ZeroFamily`): the assembled multiopen MSM of zero data is zero-data
-- whatever the scalar layouts, so the captured key's scalar metadata carries a concrete constant
-- prover with live IPA rounds.  The grouping-provenance lemma feeds both the keystone and member
-- coverage.
assert_axioms Zcash.Snark.assembleQueries_refZeroData
assert_axioms Zcash.Snark.constructIntermediateSets_sets_ref_provenance
assert_axioms Zcash.Snark.assembledMsm_zeroData
assert_axioms Zcash.Snark.multiopenCommitment_zeroData
assert_computable Zcash.Snark.zeroProofString
assert_computable Zcash.Snark.zeroAlgebraicProofString +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroProofString_wellFormed
assert_computable Zcash.Snark.zeroWfProof +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroWfProof_canonical +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroWfProof_aMulti +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroFamily_membersCovered +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.zeroOnlineMemberFamily +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The zero data's deployed batches exist at every pair count: zero column and member
-- commitments, with the `x₄` batch's own coordinates as the `x₁` aggregates.
assert_axioms Zcash.Snark.refZeroData_eval
assert_axioms Zcash.Snark.deployedSetMemberCommitments_zeroData +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.x4BatchCommitments_zeroData +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.zeroDeployedBatchesFull +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The zero family's deployed root layer (`Soundness/AGM/ZeroFamilyRoots`): six staged root
-- computations at any shape, each blind to its own squeeze because the only challenge dependence
-- the closed forms share is `assembleQueries`, which reads the pre-multiopen prefix alone.
assert_axioms Zcash.Snark.assembleQueries_x4_blind
assert_axioms Zcash.Snark.deployedSetsForEval_fst_x1_blind
assert_axioms Zcash.Snark.deployedRootBad_zeroFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.preIpaLen_strictMono
assert_axioms Zcash.Snark.zeroRootStage_agrees +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroRootStage_fresh +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The staged root sets are `szBadSet`s of polynomials, so the family is noncomputable; its
-- axiom base is censused instead.
assert_axioms Zcash.Snark.zeroDeployedRootFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The value side of the zero-data keystone (`Soundness/ZeroData`): all-zero claimed evaluations
-- survive the `x₁` compression, the Lagrange interpolation at `x₃`, the `x₂` fold and the `x₄`
-- collapse, so an instance-free zero proof's multiopen value is the zero scalar.  This is what
-- starts the straight-line discrepancy walk at zero.
assert_axioms Zcash.Snark.constructIntermediateSets_sets_eval_provenance
assert_axioms Zcash.Snark.multiopenEval_zero
assert_axioms Zcash.Snark.multiopenValue_of_zeroEvals
assert_axioms Zcash.Snark.multiopenValue_zeroProofString
-- The straight-line deployed interface, inhabited with live IPA rounds
-- (`Composition/ZeroStraightLine`): the constraint-`x` root set is empty at an instance-free
-- shape, and the staged IPA polynomial is zero at every one of the shape's `k` rounds — unlike
-- the witness shape, where `k = 0` empties the obligation.
assert_axioms Zcash.Snark.zeroConstraintDifference_eq_zero +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroConstraintXBadSet_empty +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroWfProof_straightLineIpaRootPolynomial +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.zeroStraightLineDeployedFamily +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedRootSqueezeInvariance_witness +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The satisfiability witness is itself an executable five-query stage, not a classical
-- enumeration of the finite oracle domain.
assert_computable Zcash.Snark.witnessOutcome +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessOnlineMemberFamily +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessRootStage +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessRootTrace +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.witnessDeployedRootFamily +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The direct route (`AGM.DirectX4Columns`): the `x₄` columns are read off the online coverage —
-- a column below the pair count is its set's `x₁` power sum, the last is the prover's `q′` — so
-- the batch-or-relation decision needs no offline interpolation and no field-capacity premise.
assert_axioms Zcash.Snark.x4BatchCommitments_eq_memberPowerSum
assert_axioms Zcash.Snark.aggregate_opens_deployedCommitment +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The direct path's total-cost model (`Composition.DirectPathCost`): executable modeled counts,
-- and a shape-polynomial bound with no adversary-dependent spread premise or `|F|` term. Choice
-- enters the total only through erased `Prop` positions of the finite sum.
assert_computable Zcash.Snark.directColumnDecodeOps
assert_computable Zcash.Snark.deployedDirectDecodeOps +choice
-- The semantic challenge remainder (`Composition.SemanticChallengeRemainder`): the bundle-wide
-- permutation and lookup exclusions priced from their card bounds, summed with the `y` fold-split
-- term.  These terms are charged separately from the compressed-identity ceiling.
-- The index-generic squeeze bridge (`Composition.PrefixedSqueeze`): a bad-root event at any
-- pre-IPA squeeze costs `(Q + 1) * epsilon`, so the y/beta/gamma/theta surfaces are priced the
-- same way the x surface already was.
assert_axioms Zcash.Snark.preIpaLen_strictMono
assert_axioms Zcash.Snark.algebraicFullPrefixesPre_eq_of_eq_at +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.algebraicFullPrefixesPre_ne_at +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The interpolation points the synthetic opened-batch adapters take as a hypothesis
-- (`AGM.SyntheticOpened`): a walk up from the batching challenge, injective while shorter than
-- the field characteristic.
-- The decode-to-opened bridge (`AGM.DecodeToOpened`): the rewind-free decode's own coordinates
-- presented as the opened-batch object and member decodes the Action terminal consumes.
assert_axioms Zcash.Snark.decodePoints_injective
assert_axioms Zcash.Snark.decodePoints_zero
-- Circuit-generic straight-line decode terminal.
assert_computable Zcash.Snark.topLevelStatements_or_relation_of_decode +choice +native(
  CompElliptic.Fields.Pasta.pallasBase)
-- The rewind-free decode reaching the Action terminal
-- (`Soundness.Action.StraightLineTerminal`): one accepting execution, no rewind, with
-- only the challenge exclusions left as premises.
assert_computable Zcash.Snark.ActionTerminal.action_bundleStatement_or_relation_of_decode +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil, Zcash.Snark.actionCopyAddressFailures_eq_nil,
  Zcash.Snark.actionCopyBounds, Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.ActionGateCoherence.gateData_eq, Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The same terminal, reached from the straight-line constraint event: the family supplies the
-- decode from its own accepting run.
assert_computable Zcash.Snark.ActionTerminal.action_bundleStatement_or_relation_of_straightLineDecoded +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The executable form of the rewind-free terminal: it checks the challenge exclusions by
-- evaluation and hands back either every Action's private witnesses or explicit relation
-- coefficients. This is the endpoint at which the breaks-as-computed-data discipline is
-- observable, so it carries the computable pin rather than only an axiom bound.
assert_computable Zcash.Snark.ActionTerminal.actionTerminalWitnessOrRelationFinder +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Circuit-generic straight-line terminal transports and semantic events.
assert_axioms Zcash.Snark.DeployedAlgebraicDecode.reRound
assert_axioms Zcash.Snark.straightLineAccepts_of_decoded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.straightLineRunDecodeAt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The exact Action lane: literal false-`BundleStatement` runs are contained in the compressed
-- event, four per-challenge exclusion events, and the executable relation-finder event. The
-- ordinary and knowledge endpoints price that computed relation as a DLOG break
-- (`Soundness.Action.StraightLineEvent`).
assert_axioms Zcash.Snark.ActionTerminal.actionRunDecode +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.straightLineRunAcceptsAt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelStatementOrRelationDecoded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelBundleStatementDecoded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.straightLineTerminalRelationEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelRunModel +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelRunPolynomial +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelXYFailureEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelBetaFailureEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelGammaFailureEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelThetaFailureEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.topLevelTerminalRelationFinderCovers +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The same rewind-free route, entered one step later: the caller supplies constraint
-- satisfaction directly instead of the decoded-member polynomial equality.
assert_computable Zcash.Snark.ActionTerminal.action_bundleStatement_or_relation_of_decode_circuitSat +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionRunAccepts +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionXYFailureEvent +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaFailureEvent +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaFailureEvent +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailureEvent +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.straightLineRunReads_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailureEvent_subset_surface +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaFailureEvent_subset_surface +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaFailureEvent_subset_surface +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionXYFailureEvent_subset_surfaces +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.DeployedAlgebraicDecode.memberBinding
assert_axioms Zcash.Snark.DeployedAlgebraicDecode.toOpenedBatch_current
assert_computable Zcash.Snark.pinnedPoints +choice
assert_axioms Zcash.Snark.pinnedPoints_injective
assert_axioms Zcash.Snark.PrefixDeterminedAt +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.hstab_of_prefixDeterminedAt +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.badAt_table_le_via_squeeze_prefixed +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.badAt_le_via_squeeze_prefixed +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.allResolverPermutationGammaBadSet_measure_le
assert_axioms Zcash.Snark.allResolverPermutationBetaBadSet_measure_le
assert_axioms Zcash.Snark.allResolverLookupGammaBadSet_measure_le
assert_axioms Zcash.Snark.allResolverLookupBetaBadSet_measure_le
assert_axioms Zcash.Snark.squeezeSurfaceEvent_prob_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.resolverPermutationPairs_length
assert_axioms Zcash.Snark.resolverPermutationCell_card_congr
assert_axioms Zcash.Snark.semanticSurfaces_prob_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.semanticChallengeRemainder_covers
assert_axioms Zcash.Snark.straightLineConstraintSemanticFailure_prob_le_of_surfaces +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The decode behind the straight-line constraint event, and the choice that names it.
assert_axioms Zcash.Snark.straightLineConstraintDecoded_nonempty_decode +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.straightLineDecode +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedDirectDecodeOps_le

-- Online-source constraint composition.  All disagreement branches retain concrete relation
-- coefficients and are charged through the same single-instance textbook-DLOG finder.
assert_axioms Zcash.Snark.deployedConstraint_memberPoly_eq_online +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedOnlineConstraintOutcomeOfDecode +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintOutcomeOfRoot_relation_eq_online +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintDecodedOfRoot +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintBadX_subset_landing +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintBadX_prob_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedConstraintSemanticUpgradeContained +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintSemanticFailure_subset_union +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Primary straight-line AGM capstone. The staged representation trace, not the final
-- `AlgebraicWfProof` alone, supplies IPA squeeze chronology, and the family's own constraint-`x`
-- trace derives exact `x` pinning rather than assuming it. Its complete deployed constraint
-- finder has a pointwise four-invocation bound, so no expected-runs truncation or Markov term
-- appears. Representations remain ghost extractor data, outside the Halo2 proof and verifier.
assert_axioms Zcash.Snark.StraightLineIpaOnlineTrace.toSqueezeInvariance +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.AlgebraicWfProof.straightLineIpaZeroOrRelation +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The one-run IPA dichotomy and the two root-event forms derived from it. All three hand back
-- the relation as coefficients over the public basis, so they carry the computable pin: the
-- coordinates are terms of the transcript, not an inhabitant chosen from an existence proof.
assert_computable Zcash.Snark.AlgebraicWfProof.straightLineBindingAttackZRootOrRelation +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.AlgebraicWfProof.straightLineBindingAttackZIndexedRootOrRelation +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineIpaFSFamily.straightLineIpaRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDeployedRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDecodeOfOutcome? +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintOutcome? +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSuccess? +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Census the executable cached adaptive finder and its resource bounds.
assert_computable Zcash.Snark.ActionTerminal.actionRelationFinder +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_computable Zcash.Snark.ActionTerminal.actionKnowledgeExtractor +choice +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinderCalls_le_four +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailureSet_subset +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The straight-line four-budget semantic promotion.
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineConstraintSemanticUpgradeContained +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_subset_union +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ActionTerminal.actionKnowledgeFailure_probability_bound_of_baseUnionBound +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.permutationColumnCount_eq,
  Zcash.Snark.ActionPermutationDomain.routingFailures_eq_nil,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Direct-route costs: both possible direct decodes charge their represented source traversal, the
-- query ceiling loses three bits, and the complete group-work allowance includes the verifier MSM
-- and other reduction postprocessing rather than treating the whole reduction as group-free.
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogRandomOracleQueries_le_eight_mul +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork_le_eight_mul
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineDirectDlogProfile.solverCost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/-! ## The Action circuit — the halo2-native soundness trust surface

The circuit-layer soundness theorems live at the `native_decide` tier, and the generic and
instantiated tiers carry *different* budgets — the assertions below are the authority, not this
prose:

* The generic theorems (`Circuit.soundness`, `Circuit.soundnessPost`) reach three owners: the
  Pallas point-count witness `Pallas.q_nsmul_Gpt` and the two `windowScalar_ne_zero` facts. (The
  `y = 0` exclusion `Pallas.neg_five_not_isCube`, declared in `Zcash/Circuits/Specs/Pallas.lean`
  inside CompElliptic's namespace, is a kernel proof and carries no certificate.)
* The six fixed-base window-table certificates (`Certs.*Cert_check`) enter only at the
  fully-instantiated `orchardActionCircuit`, where the deployed bases are supplied.

Note `pallas_natCard` is a *theorem* here (`Specs/Pallas.lean`), not an axiom owner: it delegates
to CompElliptic's `card_eq`, whose compiler-trust leaf is `q_nsmul_Gpt`. A `sorry` or any further
axiom reached anywhere in the Action stack fails the build here. -/

assert_axioms Zcash.Circuits.Action.Circuit.soundness +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Circuits.Action.Circuit.soundnessPost +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Circuits.Action.orchardActionCircuit +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)

/-! ## The circuit → ledger bridge — exported refinement theorems

The refinement from the Action circuit's postcondition to the games-facing ledger statement
(`ActionBreak … ∨ ∃ inst w, …`), together with the two correctness directions of the
break classifier `classifyAction`: an escape it returns is a break of the witness's own hash
query, and a `none` return — no escape at any of the four sites — means every Sinsemilla query
of the witness is defined. `actionBreak_iff_classify_isSome` packages both directions as the
consumer-boundary equivalence. Same budget as the circuit layer above: standard tier plus
`native_decide` certificates (including the Pallas point-count witness).

`actionSpec_to_ledger` is the bridge's whole consumer surface: composition with circuit
satisfaction lives on the Circuits side, where the `Constraints` predicate it would consume
is actually produced. -/

assert_axioms Zcash.Security.Ledger.Bridge.actionSpec_to_ledger +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.actionBreak_of_classify +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.classify_none_defined +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.actionBreak_iff_classify_isSome +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

/-! ## The Sinsemilla discrete-log-relation reduction

The onward step from a classified Action escape to the games-facing relation object, which
the census above stops short of: the escaped chain is turned into an explicit generator
combination (`ofPoint_hashToPoint`), the coefficient vector is computed from the break data
(`breakCoeffs`, with its relation and nontriviality facts), and the two headline reductions
package that as a `NontrivialRelationOne` at the escaped site's domain point.

`relationOfBreakData` and `classifyRelation` are asserted computable, per the
breaks-as-computed-data convention. `+native` covers the deployed bases' on-curve certificates
carried in their erased `Prop` fields; `+choice` is the same erased-positions tier the classifier
itself sits at.

`ofPoint_hashToPoint` and `breakCoeffs_nontrivial` stay at the standard tier: the chain
combination reasons in `ℕ`-multiples of the lifted table, and nontriviality only in the scalar
field. `breakCoeffs_relation` needs `+native` because it scales group elements by field
elements, and the `Module Fq PallasGroup` instance is built from the Pallas point count. That
is the same witness the circuit layer above carries, reaching this file through the group's
scalar action rather than a certificate check. -/

assert_computable Zcash.Security.Ledger.Bridge.breakCoeffs +choice
assert_computable Zcash.Security.Ledger.Bridge.relationOfBreakData +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_computable Zcash.Security.Ledger.Bridge.classifyRelation +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.ofPoint_hashToPoint
assert_axioms Zcash.Security.Ledger.Bridge.breakCoeffs_relation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Security.Ledger.Bridge.breakCoeffs_nontrivial
assert_axioms Zcash.Security.Ledger.Bridge.classify_query_inr +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.classifyRelation_isSome_iff +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.Bridge.classifyRelation_site +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

/-! ## `@[csimp]` replacement lemmas

Every `@[csimp]` lemma gets an axiom check here. The compiler applies the
substitution in all downstream compiled code, but the axioms of the lemma's own
proof are not propagated into downstream `native_decide` axiom tracking (
[lean4#7463](https://github.com/leanprover/lean4/issues/7463)), so a csimp lemma
whose proof smuggled `sorryAx` or a project axiom would be invisible to every
consumer's census entry. Checking the lemma itself closes that hole.

What the substitution changes about *evaluation* is worth stating explicitly, since the census
records axioms rather than runtimes: `evalNat_eq_evalNatFast` redirects every compiled call site —
including the fixtures' `native_decide` auxiliaries — to `pippengerFastPar`, whose ~32 windows are
evaluated through `List.parMap`, i.e. `Task.spawn`/`Task.get` on the real thread pool. That widens
the *compiled surface* the fixture certificates run over (windowed Pippenger plus the task runtime,
rather than a naive double-and-add ladder), all of it already inside the `native_decide` trust
boundary — `Task.spawn`/`Task.get` are `@[extern]`, while the kernel sees the reference bodies and
`List.parMap_eq_map` closes by `rfl`. Because each task computes a pure, independently determined
value, a scheduling fault can hang or crash the build but cannot silently change a result; a wrong
answer requires a memory-safety defect, the same class every `native_decide` already trusts. See
`Zcash/Common/ParMap.lean` and `Zcash/Arithmetic/FastMsm.lean`. -/

assert_axioms Zcash.Arithmetic.Msm.evalNat_eq_evalNatFast

/-! ## Statement-bound Fiat–Shamir

These entries keep the protocol hardening inside the checked surface. The executable entries must
remain ordinary definitions; the theorem entries pin the entire transitive axiom base of statement
binding and malformed-instance rejection. The module documentation in
`Zcash.Snark.Verifier.Deployed` records the opaque-key-representation and commitment-level limits of
that binding claim. -/

assert_computable Zcash.Snark.absorbInstanceCommitments
assert_axioms Zcash.Snark.absorbInstanceCommitments_congr
assert_computable Zcash.Snark.initialTranscript
assert_axioms Zcash.Snark.initialTranscript_congr
assert_computable Zcash.Snark.deriveChallengesForStatement
assert_axioms Zcash.Snark.deriveChallengesForStatement_congr
assert_computable Zcash.Snark.preThetaTranscriptForStatement
assert_computable Zcash.Snark.validateInstances?
assert_computable Zcash.Snark.assembleInstances? +choice
assert_computable Zcash.Snark.assembleNonInteractiveInstances? +choice
assert_axioms Zcash.Snark.columnQueries_congr_commitment
assert_axioms Zcash.Snark.assembleQueries_congr_instanceCommitment
assert_axioms Zcash.Snark.assembleQueries_congr_instanceCommitment_of_layout_bounded
assert_axioms Zcash.Snark.assemble?_congr_instanceCommitment
assert_axioms Zcash.Snark.assemble?_congr_instanceCommitment_of_layout_bounded
assert_axioms Zcash.Snark.vkTranscriptRepr_eq_of_initialTranscript_eq
assert_axioms Zcash.Snark.instanceCommitment_eq_of_initialTranscript_eq
assert_axioms Zcash.Snark.vkTranscriptRepr_mem_preThetaTranscriptForStatement
assert_axioms Zcash.Snark.instanceCommitment_mem_preThetaTranscriptForStatement
assert_axioms Zcash.Snark.adviceCommitment_mem_preThetaTranscriptForStatement
assert_axioms Zcash.Snark.assembleNonInteractiveInstances?_eq_none_of_wrong_column_count
assert_axioms Zcash.Snark.assembleNonInteractiveInstances?_eq_none_of_oversized_column

-- Probability-bound leaves matched by the `_measure_le` suffix. These are surface and
-- root-set measures inside the AGM and pricing layers rather than protocol capstones, and
-- their trusted base is already bounded through the endpoints that consume them; the pins
-- are what the suffix rule demands, not an independent claim.

-- AGM/AdaptiveIpaSurfaces.lean

-- AGM/AdaptiveOnline.lean
assert_axioms Zcash.Snark.LabeledOracleComp.finalBadWithoutRelation_measure_le
assert_axioms Zcash.Snark.LabeledOracleComp.firstLabelOrFallbackBad_measure_le

-- AGM/AdaptiveRootComposition.lean

-- AGM/AdaptiveRootSurfaces.lean

-- AGM/AdaptiveSurfaces.lean

-- AGM/DeployedRootSets.lean
assert_axioms Zcash.Snark.deployedX1AllRootSet_measure_le
assert_axioms Zcash.Snark.deployedX1RootSet_measure_le
assert_axioms Zcash.Snark.deployedX2RootSet_measure_le
assert_axioms Zcash.Snark.deployedX3RootSet_measure_le
assert_axioms Zcash.Snark.deployedX4RootSet_measure_le

-- AGM/ShiftRecovery.lean
assert_axioms Zcash.Snark.ipaShiftXi_badSet_measure_le
assert_axioms Zcash.Snark.ipaShiftZ_badSet_measure_le

-- AGM/StraightLineIpa.lean
assert_axioms Zcash.Snark.ipaDiscrepancyBadSet_measure_le

-- AGM/StraightLinePinnedRoots.lean
assert_axioms Zcash.Snark.ComputedStraightLineIpaFSFamily.pinnedIpaRoots_landing_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineIpaFSFamily.straightLineIpaRootBad_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- AGM/ValueUnbatch.lean
assert_axioms Zcash.Snark.clearedQuotientErrorPolynomial_badSet_measure_le
assert_axioms Zcash.Snark.memberBindingErrorPolynomial_badSet_measure_le
assert_axioms Zcash.Snark.nodeBindingErrorPolynomial_badSet_measure_le
assert_axioms Zcash.Snark.powerErrorPolynomial_badSet_measure_le

-- FiatShamir/Adversary/OracleComp.lean
assert_axioms Zcash.Snark.escapesDuringC_measure_le

-- Pricing/ChallengePricing.lean
assert_axioms Zcash.Snark.lookup_beta_failure_measure_le
assert_axioms Zcash.Snark.lookup_gamma_failure_measure_le

-- Pricing/UniformMeasure.lean
assert_axioms Zcash.Snark.sum_point_mem_measure_le

-- Probability-bound leaves matched by the `_probability_bound` suffix. Like the `_measure_le`
-- block above, these are per-challenge surface and residual-event measures inside the Action
-- terminal rather than protocol capstones; their trusted base is already bounded through the
-- Action endpoints that consume them, so the pins are what the suffix rule demands rather than
-- independent claims.

-- Soundness/Action/AdaptiveEvent.lean

-- Soundness/Action/AdaptiveSurfaces.lean

-- Probability-bound leaves matched by the `_measure_le` suffix: surface and root-set
-- measures inside the AGM and adaptive-statement layers, pinned because the suffix rule
-- demands it rather than as independent claims.

assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.adaptiveActionBetaSurfaceAtOf_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.adaptiveActionGammaSurfaceAtOf_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.adaptiveActionThetaSurfaceAtOf_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.adaptiveActionXSurfaceAtOf_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.adaptiveActionYSurfaceAtOf_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.decodedIpaSurface_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.decodedRootSurface_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputIpaBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputIpaFallbackBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputIpaSurface_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputRootBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputRootSurface_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.outputSemanticBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.queriedIpaBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.queriedRootBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.queriedSemanticBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.statementLabeledPrefixBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.statementPrefixBad_measure_le +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero, Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check, Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check, Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.adaptiveFallbackIpaSurfaceCore_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveFallbackIpaSurface_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveIpaFallbackBad_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveIpaQueriedBad_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveIpaRootPolynomial_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveLabeledPrefixBad_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptivePrefixBad_measure_le
assert_axioms Zcash.Snark.adaptiveQueriedIpaSurfaceCore_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveQueriedIpaSurface_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveRootSurfaceAt_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveX1AllRootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveX2RootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveX3RootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveX4RootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveXiRootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.adaptiveZRootSet_measure_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
