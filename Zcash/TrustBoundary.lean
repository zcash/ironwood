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
import Zcash.Security.Common.Birthday
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Meta.AxiomCheck
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Deployed.ConcreteBounds
import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.Forking.Adversary
import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.ConstraintRelations
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.ActionVesta
import Zcash.Security.Ledger.KeyBindingDLR
import Zcash.Security.Ledger.NoteCommitDLR
import Zcash.Security.Ledger.MerkleDLR
import Zcash.Security.Ledger.DeployedCapstone
import Zcash.Snark.Soundness.DegreeWalk
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.PinnedRootWitness
import Zcash.Snark.Soundness.Composition.StraightLineWitness
import Zcash.Snark.Soundness.Composition.DirectPathCost
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Circuits.Integration.StraightLineActionTerminal
import Zcash.Circuits.Integration.StraightLineActionEvent
import Zcash.Snark.Fixtures.MultiAction.ActionCapstone
import Zcash.Snark.Soundness.Composition.SemanticChallengeRemainder
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.Composition.SequentialLift
import Zcash.Snark.Soundness.Composition.ChallengeReads
import Zcash.Circuits.Integration.StraightLineActionBudgets
import Zcash.Snark.Soundness.AGM.ZeroFamily
import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
import Zcash.Snark.Soundness.Composition.ZeroStraightLine
import Zcash.Snark.Soundness.AGM.DirectConstraintFamily
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Trust boundary, build-checked

The library-wide census that makes the trust claims build-time checks rather than prose: a change
that widens a declaration's trusted base — a `sorry` reached through some dependency, an unexpected
axiom, or `native_decide` where none was permitted — fails this file rather than passing silently.

Two commands from `Zcash.Meta.AxiomCheck`, per the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`):

* **Computed break reductions** get `assert_computable`: the declaration is a plain `def` — not a
  theorem, not marked `noncomputable` — with axioms bounded by `propext` / `Quot.sound`.
  `+choice` additionally permits `Classical.choice`; with the plain-`def` check this asserts
  choice enters only through erased `Prop` certificate fields, so the break data cannot have been
  conjured from mere propositional existence.
* **Theorems** get `assert_axioms`, an upper bound at the standard tier
  (`propext` / `Classical.choice` / `Quot.sound`). Both commands reject `sorryAx`.
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
assert_computable Zcash.Security.Ledger.Model.poolValueBalance
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

/-! ## Balance-value (conservation form)

`+choice` on the two endpoints is again the erased-positions tier: choice arrives with
the `ring`/`omega` proof terms in their `Prop` fields, never the data path. -/

assert_computable Zcash.Security.Ledger.Model.txNetValue
assert_computable Zcash.Security.Ledger.Model.issuanceTotal
assert_axioms Zcash.Security.Ledger.Model.transparentPoolBalance_eq
assert_axioms Zcash.Security.Ledger.Model.positionedOutputs_value_sum
assert_axioms Zcash.Security.Ledger.Model.nonZeroSpends_value_sum
assert_axioms Zcash.Security.Ledger.Model.poolValueBalance_eq_neg
assert_computable Zcash.Security.Ledger.Model.allValueOrBreak
assert_computable Zcash.Security.Ledger.Model.valueConservationOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.balanceValueOrBreak +choice
assert_axioms Zcash.Security.Ledger.Model.sum_val_le_of_le
assert_axioms Zcash.Security.Ledger.Model.positionedOutputs_value_sum_mono
assert_axioms Zcash.Security.Ledger.Model.poolValueBalance_nonneg
assert_computable Zcash.Security.Ledger.Model.balanceOrBreak +choice

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

/-! ## The value-premiss discharge

Computed reductions at the Pedersen value-commitment shape: the Balance-value
premiss lands in the binding-signature layer's nontrivial `(V, R)` relation via
`ofBundleIntImbalance`, with the no-overflow bound discharged from the statement's
value ranges, validity's action-count and `vBalance` range rules, and the named
numeric hypothesis `(maxActions + 1) * valueBound ≤ r`. `+choice` is the
erased-positions tier. -/

assert_computable Zcash.Security.Ledger.Model.ValueShape.premissOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.ValueShape.conservationOrBreak +choice
assert_computable Zcash.Security.Ledger.Model.ValueShape.balanceOrBreak +choice

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
Its `+choice` is the erased-positions tier — choice arrives with proof terms in
`Prop` positions, never the data path. -/

assert_computable Zcash.Security.Ledger.Model.honestTx
assert_computable Zcash.Security.Ledger.Model.HonestAction.withDummySpend
assert_axioms Zcash.Security.Ledger.Model.HonestAction.satisfied
assert_axioms Zcash.Security.Ledger.Model.honestTx_valid
assert_computable Zcash.Security.Ledger.Model.spendabilityOrBreak +choice

/-! ## Probabilistic capstones

The game-level probability statements: pure event algebra over an adversary
distribution of valid annotated ledgers, with a named ε hypothesis per break arm. -/

assert_axioms Zcash.Security.Ledger.Model.balanceSubset_measure_le
assert_axioms Zcash.Security.Ledger.Model.valueConservation_measure_le
assert_axioms Zcash.Security.Ledger.Model.balanceValue_measure_le
assert_axioms Zcash.Security.Ledger.Model.spendAuthority_measure_le

/-! ## The deployed discrete-log-relation discharges

Each deployed Balance-subset break arm reduces to a nontrivial discrete-log relation
among the fixed Sinsemilla bases (`deployedBalanceSubsetOrRelation`), routing the three
named ε hypotheses to one discrete-log-relation assumption per domain point. The
reductions are computable, so they get assert_computable. The encoding-injectivity and
coefficient-injectivity facts they consume are theorems. -/

assert_axioms Zcash.NontrivialRelation.toOne
assert_axioms Zcash.Circuits.Specs.Sinsemilla.chunksOf_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.commitIvkChunks_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.noteCommitChunks_inj
assert_axioms Zcash.Circuits.Specs.Sinsemilla.merkleChunks_inj
assert_axioms Zcash.Security.Ledger.Bridge.preCoeffs_inj
assert_axioms Zcash.Security.Concrete.PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube)
assert_computable Zcash.Security.Ledger.Bridge.relationOfChainPmEq +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Security.Ledger.Bridge.relationOfKeyBindingBreak +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check)
assert_computable Zcash.Security.Ledger.Bridge.relationOfNoteCommitBreak +choice +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Concrete.PallasGroup.pallas_base_card_lt_scalar_card,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_computable Zcash.Security.Ledger.Bridge.relationOfMerkleCollision +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Security.Ledger.Bridge.deployedBalanceSubsetOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Concrete.PallasGroup.pallas_base_card_lt_scalar_card,
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

The census also carries the SNARK binding and knowledge-soundness reductions, consolidated here
from the former per-directory files and, like the key-binding and ledger sections above, expressed
through the `Zcash.Meta.AxiomCheck` macros rather than the older `assert_no_sorry` +
`#guard_msgs`-pinned `#print axioms` idiom:

* **Computed break reductions** — the data-producing `def`s that extract a discrete-log relation
  from a collision, fold, peel, or fork — get `assert_computable`: a plain `def`, not marked
  `noncomputable`. `Classical.choice` enters only through erased `Prop` certificate fields
  (`+choice`); the relation coefficients are direct terms of the inputs, so the break data cannot
  have been conjured from mere propositional existence. Vesta-instantiated producers additionally
  inherit CompElliptic's `native_decide` curve point-count axiom (`+native`).
* **Theorems** — the probability-layer bounds, the knowledge-soundness and binding endpoints across
  all adversary models, the DL capstones, and the run-time/query-charge lemmas — get
  `assert_axioms`, bounding the trusted base at the standard tier (`propext` / `Classical.choice` /
  `Quot.sound`), with `+native` on the Vesta-instantiated endpoints.
-/

/-! ### Binding reductions from IPA/CommitFold collisions -/

assert_computable Zcash.Snark.NontrivialDLRelation.ofCollision +choice
assert_computable Zcash.Snark.NontrivialDLRelation.ofIpaOpenings +choice

/-! ### Verifier-soundness capstones -/

assert_axioms Zcash.Snark.deployedAccepts_verifierEq
assert_axioms Zcash.Snark.orchard_verifier_deployed_opening_of_forked
assert_axioms Zcash.Snark.orchard_verifier_deployed_constraint_of_forked
assert_axioms Zcash.Snark.orchard_verifier_vesta_constraint_of_forked +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/-! ### Deployed binding-reduction breaks

The binding reductions return computed data (plain `def`s); the same treatment covers the forking
reductions `ipa_extractV`, `ipaRelation_extract`, `produceDeployed`, `deployed_forking_tree`, and
`deployed_forking_relation`, each computing its witness from an explicit certificate. -/

assert_computable Zcash.NontrivialRelation.ofCombinationCollision +choice
assert_computable Zcash.Snark.NontrivialRelation.ofFoldedGens +choice
assert_computable Zcash.Snark.NontrivialRelation.ofLeafPeel +choice
assert_computable Zcash.Snark.NontrivialRelation.ofDeployedTree +choice
assert_computable Zcash.Snark.NontrivialRelation.ofUnopenedFork +choice
assert_computable Zcash.Snark.NontrivialRelation.ofUnopenedForkVesta +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ipa_extractV +choice
assert_computable Zcash.Snark.ipaRelation_extract +choice
assert_computable Zcash.Snark.produceDeployed +choice
assert_computable Zcash.Snark.deployed_forking_tree +choice
assert_computable Zcash.Snark.deployed_forking_relation +choice

/-! ### AGM / Fiat–Shamir soundness

The AGM kernels compute representations, openings, relations, certificates, and deployed instances
as data (`assert_computable`); the probability layer, the knowledge-soundness and binding endpoints,
and the run-time bounds are theorems (`assert_axioms`). -/

assert_computable Zcash.Snark.discreteLogOfBasis_of_relation +choice
assert_computable Zcash.Snark.discreteLogOfChallenge_of_relation +choice
assert_computable Zcash.Snark.programmedExtractOrMiss +choice
assert_computable Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness +choice
assert_computable Zcash.Snark.relationWitnessOfCollision +choice
assert_computable Zcash.Snark.discreteLogOfAugmentedRelationAtChallenge +choice
assert_computable Zcash.Snark.separateOrRelationWitness +choice
assert_computable Zcash.Snark.algebraicPowerBatchWithSourceOrRelation +choice
assert_computable Zcash.Snark.finForallOrRelationWitness +choice
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
assert_computable Zcash.Snark.deployedX1AlgebraicBatchWithSourceOrRelation +choice
assert_computable Zcash.Snark.deployedX1BatchOfCoveredWithSourceOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedX4ColumnRepresentationsOfCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedX4BatchOfCoveredOrRelation +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedRootOutcomeOfCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedRootFSFamily.ofCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedConstraintFSFamily.ofCovered +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedRootFSFamily.deployedRelationFinder +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedConstraintFinderOfOutcome +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.deployedConstraintRelationFinder +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.relationOfFoldGensWitness +choice
assert_computable Zcash.Snark.deployedLeafPeelWitness +choice
assert_computable Zcash.Snark.deployedToAcceptVWitness +choice
assert_computable Zcash.Snark.algebraicRelationOfDeployedAccept +choice
assert_axioms Zcash.Snark.AlgebraicProver.toProver
assert_axioms Zcash.Snark.AlgebraicDForkCert.toDForkCert
assert_axioms Zcash.Snark.algebraicProverAccept_forkValid
assert_computable Zcash.Snark.deployedAlgebraicForkingRelation +choice
assert_axioms Zcash.Snark.deployed_forking_relation_shifted
assert_axioms Zcash.Snark.deployedAlgebraicForkingRelation_shifted
assert_computable Zcash.Snark.deployedAlgebraicForkingProgrammed +choice
assert_axioms Zcash.Snark.DeployedAlgebraicForkingInstance.run
assert_axioms Zcash.Snark.DeployedAlgebraicForkingInstance.ProducesRelation
assert_axioms Zcash.Snark.deployedAlgebraicRelationProduced
assert_axioms Zcash.Snark.deployedAlgebraicRelationEvent
assert_computable Zcash.Snark.deployedAlgebraicRelationFinder +choice
assert_axioms Zcash.Snark.deployedAlgebraicRelationFinder_isSome_iff
assert_computable Zcash.Snark.deployedAlgebraicRelation +choice
assert_computable Zcash.Snark.deployedAlgebraicRelationWitness +choice
assert_axioms Zcash.Snark.orchardDeployedAlgebraicForkingProgrammed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchardDeployedRelationSet +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.OrchardUniformURSIdentification +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchardGeneratorROSetup
assert_axioms Zcash.Snark.orchardGeneratorROBasis
assert_axioms Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_realizes
assert_axioms Zcash.Snark.algebraicForkCertAttempt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.algebraicForkCertAttempt_valid +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.computedDeployedAlgebraicInstance +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.computedAlgebraicInstanceFailure_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicRelationWitness.augment
assert_axioms Zcash.Snark.DeployedAlgebraicForkingInstance.runRelation
assert_axioms Zcash.Snark.DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
assert_computable Zcash.Snark.DeployedAlgebraicForkingInstance.runToSnark +choice +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.relationFinder +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.relationFinder_isSome_of_bindingWin +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkRelationFinder +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkNonRelationFailure +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.ReductionEfficient +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exists +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.instanceAttempt_runs_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exponential +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_poly +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.FamilyForkSpread +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_of_forkSpread +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.DiscreteLogRelationHardFor +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL_poly +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.cleanOpening +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.cleanOpening_isSome_iff +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL_computed +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL_computed_poly +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.binding_under_DL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.binding_under_DL_poly +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
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
assert_axioms Zcash.Snark.scanCandidate_self
assert_axioms Zcash.Snark.self_mem_goodChallenges_iff
assert_axioms Zcash.Snark.scanRank_insert_erase
assert_axioms Zcash.Snark.scanRank_insert_eq_filter
assert_axioms Zcash.Snark.goodChallengesAt
assert_axioms Zcash.Snark.OracleComp.queries_queryList
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_node_runs_le_gated
assert_axioms Zcash.Snark.OracleComp.queries_bind
assert_axioms Zcash.Snark.OracleComp.mem_queries_completing
assert_axioms Zcash.Snark.scanCandidateAt
assert_axioms Zcash.Snark.scanCandidateAt_fork
assert_axioms Zcash.Snark.scanCandidateAt_update
assert_axioms Zcash.Snark.goodChallengesAt_fork
assert_axioms Zcash.Snark.goodChallengesAt_update
assert_axioms Zcash.Snark.sum_card_scanRank_erase_lt_le
assert_axioms Zcash.Snark.afkScanCharge
assert_axioms Zcash.Snark.afkScanCharge_update
assert_axioms Zcash.Snark.sum_afkScanCharge_le
assert_axioms Zcash.Snark.OracleComp.run_update_eq_of_not_mem_queries
assert_axioms Zcash.Snark.OracleComp.mem_queries_of_run_update_ne
assert_axioms Zcash.Snark.OracleComp.card_filter_mem_queries_le
assert_axioms Zcash.Snark.sum_steered_blind_mul_card
assert_axioms Zcash.Snark.sum_steered_rank_stable_le
assert_axioms Zcash.Snark.sum_steered_rank_abort_le
assert_axioms Zcash.Snark.scanCandidateAt_runs_split
assert_axioms Zcash.Snark.goodChallengesAt_stable
assert_axioms Zcash.Snark.goodChallengesAt_nonempty_changed_query
assert_axioms Zcash.Snark.sum_afkScanCharge_steered_le
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_tape_sum_runs_le_afk
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_step
assert_axioms Zcash.Snark.afkRunBound
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_oracle_tape_sum_runs_le_poly
assert_axioms Zcash.Snark.recursiveAlgebraicFork_oracle_tape_sum_runs_le_poly
assert_axioms Zcash.Snark.OracleComp.restrictSum
assert_axioms Zcash.Snark.fsWinsFull_restrictSum_le
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.determinize
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailureEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.foldedRelationFinder +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.foldedSnarkRelationFinder +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.globalReachSet +choice
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.reachSet_subset_globalReachSet
assert_computable Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.splitFamilyRand +choice
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.run_splitFamilyRand_adversary
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.uniformURS_basis_transfer +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailureEventUnbounded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.bindingEventUnbounded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.determinize
assert_computable Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.globalReachSet +choice
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.reachSet_subset_globalReachSet
assert_computable Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.splitFamilyRand +choice
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.run_splitFamilyRand_adversary
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_foldedTextbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailureEventUnboundedRand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.bindingEventUnboundedRand +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_node_runs_le
assert_axioms Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_unconditional
assert_axioms Zcash.Snark.recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional
assert_axioms Zcash.Snark.recursiveAlgebraicForkFrom_sum_runs_le_of_forkSpread
assert_axioms Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_of_forkSpread
assert_axioms Zcash.Snark.recursiveAlgebraicFork_oracle_tape_sum_runs_le_of_forkSpread
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
assert_axioms Zcash.Snark.orchard_deployed_relation_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchard_deployed_relation_set_eq_relSet +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchard_deployed_relation_event_prob_le_of_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchard_deployed_relation_prob_eq_of_uniformURS +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchard_deployed_relation_prob_le_of_uniformURS_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.orchard_deployed_relation_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

/-! ### Fork-tree knowledge error

The closed form of the fork-tree knowledge error and its evaluation over the deployed Orchard
parameters. All theorems, so `assert_axioms`: the arithmetic runs on `Nat`/`ℝ≥0∞` and the deployed
field cardinality comes from `ZMod.card`, so no compiler trust enters here. -/

assert_axioms Zcash.Snark.kerr_mul_card
assert_axioms Zcash.Snark.kerr_eq
assert_axioms Zcash.Snark.kerr_div_card
assert_axioms Zcash.Snark.deployed_forking_knowledge_error
assert_axioms Zcash.Snark.deployed_forking_knowledge_error_captured

/-! ### Multiopen decode and forking composition

The decode layer's surviving surface: the Vandermonde column recovery, the `x₄` flat-power-batch
collapse, and the forking-extraction composition. The rewind-based compatibility layer that once
sat here — the propositional binding disjunct and the accept-event ladders it fed — has been
removed, so every break the deployed route charges to DLOG is computed relation data, censused
below through explicit `PSum` outcomes and computable finders. Theorems throughout, so
`assert_axioms`, with `+native` on the Vesta-instantiated endpoints. -/

-- The forking-extraction ∘ decoded-capstone composition (`Soundness.Composition.Bridge`): the algebraic
-- clean opening identified with the deployed capstone's shape (`ipaRelation_deployed_of_instance`).
-- On the witness tie the opened-value shift is derived
-- (`shift_eq_zero_of_openings_agree`), so `hshift` survives only on the standalone single-opening
-- bridge. `snarkExtraction_prob_le_of_generatorRO_textbookDL` is the CONDITIONAL knowledge-error
-- bound: the SNARK-extraction failure is contained in the clean-opening failure and inherits its
-- `(Q+k)·3/|Fp| + (Q+1)/|Fp| + ε + 1/|Fp|` bound, conditional on `hExtract` (clean opening ⟹
-- extraction). Discharging `hExtract` — coupling the AGM family's coin measure to the multiopen
-- budget below — is the remaining reconciliation. This stack is not consumed by the rewind-free
-- constraint capstone below.
assert_axioms Zcash.Snark.ipaRelation_deployed_of_instance +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtraction_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.instanceAttempt_provenance +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ipaRelation_deployed_of_openings_agree +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.shift_eq_zero_of_openings_agree +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- The decode layer (`Soundness.Multiopen.Decode`/`Deployed`): the Vandermonde recovery of the
-- column witnesses, the deployed x4 collapse proved to be a flat power batch, and the two-level
-- binding of the extracted witness to the member commitments.
assert_axioms Zcash.Snark.decodedColumnFamily_of_batch_openings
assert_axioms Zcash.Snark.deployedCommitment_x4_batch
assert_axioms Zcash.Snark.multiopenValue_x4_batch
assert_axioms Zcash.Snark.member_binding_of_x1_samples
assert_axioms Zcash.Snark.node_binding_of_samples
-- The multiopen support modules, pinned directly rather than transitively through the capstones
-- above. `Opened` holds the rewind accept events and the three `Classical.choose` witness
-- extractors; `RPoly` the interpolation/power-form algebra; `Compat` the Msm-evaluation and
-- two-openings binding lemmas; `Claimed` the counting cores; `ValueCheckDeployed` the deployed
-- point sets. A stray axiom here would surface at a capstone, but only these pins name the
-- declaration that introduced it.
assert_axioms Zcash.Snark.vandermonde_decode_map
assert_axioms Zcash.Snark.vandermonde_reconstruct_map
assert_axioms Zcash.Snark.openedColumnDecode
assert_axioms Zcash.Snark.openedDecodedCols
assert_axioms Zcash.Snark.openedDecodedCols_eval_x3
assert_axioms Zcash.Snark.openedDecodedCols_top_eval_x3
assert_axioms Zcash.Snark.openedX4Batch_of_witnessFamily
assert_axioms Zcash.Snark.OpenedX4Accept
assert_axioms Zcash.Snark.OpenedX3Accept
assert_axioms Zcash.Snark.OpenedX2Accept
assert_axioms Zcash.Snark.openedX4Rewind_of_x4Prob
assert_axioms Zcash.Snark.openedX4Rewind_of_x4Prob_forked
assert_axioms Zcash.Snark.opened_constraint_of_relation_and_batch
assert_axioms Zcash.Snark.x1DecodeComp
assert_axioms Zcash.Snark.opened_witness_member_binding
assert_axioms Zcash.Snark.OpenedX1Accept
assert_axioms Zcash.Snark.openedMemberDecode_of_x1Prob
assert_axioms Zcash.Snark.rotatedFeed
assert_axioms Zcash.Snark.member_constraint_of_relation_and_batch
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
assert_axioms Zcash.Snark.multiopenEval_perSet_zero_of_samples
assert_axioms Zcash.Snark.lagrangePoly_natDegree_lt
assert_axioms Zcash.Snark.col_eq_lagrangePoly_of_samples
assert_axioms Zcash.Snark.col_eval_node_eq_claimed
assert_axioms Zcash.Snark.Msm.eval_zero
assert_axioms Zcash.Snark.Msm.eval_scale
assert_axioms Zcash.Snark.Msm.eval_add
assert_axioms Zcash.Snark.claimedEval_of_x3Prob
assert_axioms Zcash.Snark.gateGood_of_xProb
assert_axioms Zcash.Snark.deployedSetPts
assert_axioms Zcash.Snark.deployedAllPts
assert_axioms Zcash.Snark.deployedSetPts_subset
assert_axioms Zcash.Snark.deployed_query_point_mem
-- The avoidance-strengthened forking count (`Soundness.Forking.Probability`): the counting lemma
-- that buys the multiopen grid's interpolation samples off the opened set points, so the value
-- check takes no sample-avoidance hypothesis.
assert_axioms Zcash.Snark.exists_injective_accepting_avoiding_of_measure
-- The good-challenge production (`Soundness.GoodChallenge`): the Schwartz-Zippel exclusion budget
-- and the pigeonhole that produces an accepting challenge outside the bad set.
assert_axioms Zcash.Snark.uniformChallenge_szBadSet
assert_axioms Zcash.Snark.uniformChallenge_szGoodSet
assert_axioms Zcash.Snark.uniformChallenge_quotient_szBadSet
assert_axioms Zcash.Snark.uniformChallenge_szBadSet_union
assert_axioms Zcash.Snark.exists_accepting_good_challenge
assert_axioms Zcash.Snark.exists_accepting_good_challenge_quotient
-- The deployed Vesta capstone family: the decoded-column rungs and the terminal, alongside the
-- derived capstone already pinned below.
assert_axioms Zcash.Snark.orchard_verifier_vesta_decoded_constraint_of_forked_x4 +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

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

The circuit-integration stack carries its binding break as computed `NontrivialRelation` data
rather than as the `∃`-closed proposition that is unconditionally true at the concrete curve.
The declarations below are the part of that stack which is genuinely computable, so they are
pinned at the `assert_computable` tier: a plain `def`, never marked `noncomputable`. Pinning
them is what stops the discipline regressing silently — a break that stopped being computed
would still typecheck, and `assert_axioms` alone would not notice.

The combinators are at the strict tier: they introduce no choice at all. The adapters below
them take `+choice`, which the plain-`def` check turns into the assertion that choice enters
only through erased `Prop` certificate fields.

The capstone endpoints are *not* here. They are `noncomputable` — their decisions run through
Mathlib polynomials, which are noncomputable by construction — and so are pinned with
`assert_axioms` above. Moving them to this tier means deciding on coefficient vectors and
stating the result in polynomials, as `decodedQuotientEqReassembledOrRelationWitness` does. -/

assert_computable Zcash.Snark.bindOrRelationWitness
assert_computable Zcash.Snark.finForallOrRelationWitness
assert_computable Zcash.Snark.listForallOrRelationWitness
assert_computable Zcash.Snark.boundedForallOrRelationWitness
assert_computable Zcash.Snark.FullCircuitSatisfaction.of_components_or_bad
assert_computable Zcash.Snark.declaredCopies_satisfied_or_bad_of_replay +choice
assert_computable Zcash.Snark.copy_constraints_or_bad_of_replay +choice
assert_computable Zcash.Snark.CopyReplayWitness.constraints_or_bad +choice
assert_computable Zcash.Snark.FullCircuitBridge.satisfaction_or_bad +choice
assert_computable Zcash.Snark.FullCircuitBridge.constraints_or_bad +choice
assert_computable Zcash.Snark.decodedPolynomialResolver_opens_or_relation +choice

-- The accepted-route adapter fixes the advice and instance member feeds, then the deployed Action
-- boundary consumes the resulting canonical `CircuitSat`. The final theorem has no free semantic
-- callback, decoder, or selected-column feed.
assert_axioms Zcash.Snark.topLevelBundleStatement_or_bad_of_constraintSatisfaction +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms Zcash.Snark.TopLevelAcceptedModel.statements_or_relation_of_circuitSat +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms Zcash.Snark.topLevelStatements_or_relation_of_deployedAccepts +native(
  CompElliptic.Fields.Pasta.pallasBase,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.acceptedAdviceSelection_feed_eq
assert_axioms Zcash.Snark.acceptedInstanceSelection_feed_eq
assert_axioms Zcash.Snark.acceptedModel_circuitSat_or_relation_of_feed_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.acceptedModel_circuitSat_or_relation_of_acceptedSelections +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.action_bundleStatement_or_relation_of_deployedAccepts +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil,
  Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil,
  Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
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
-- The UNCONDITIONAL decomposition: `hExtract` removed, the residual quantified as the
-- clean-but-not-extracted measure term (bounded by the multiopen budget under the coupling
-- documented in `Composition.Decomposition`, not assumed here).
assert_axioms Zcash.Snark.ComputedAlgebraicFSFamily.snarkExtractionFailureEvent_subset_union +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Product-measure lifting, now used by the direct pinned-root composition.
assert_axioms Zcash.Snark.independentProductPMF_fiber_bound
-- Acceptance through `assemble?`, isolated from the historical completeness ladder.
assert_axioms Zcash.Snark.fullAlgebraicAcceptDeployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.fullAlgebraicAccept_of_deployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtractionFailureEventDeployed +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtractionFailureEventDeployed_subset_union +native(
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
-- Prefix injectivity at the multiopen squeeze points (`Forking.Adversary.PreIpa`): each point
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
-- The schedule, priced (`Composition.ScheduleBudget`): the committed carriers stay under the
-- walk's caps, root witnesses at one table share the family's own outcome so the root set
-- collapses across fork tapes, and the schedule constructor discharges `measure_le` outright.
-- The captured family carries an explicit fresh-query `OracleComp` trace and derives exact
-- pinning from its query log. The lower-level direct-pinning constructor remains generic plumbing;
-- it is not a standalone captured-capstone premise.
assert_axioms Zcash.Snark.natDegree_committedPreXConstraintDifference_le
assert_axioms Zcash.Snark.natDegree_deployedConstraintDifferencePreX_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintDifference_tape_congr +native(
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
-- The total pre-x constraint event of issue #127: the difference from the family's own
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
-- Adversary coverage (#127 C8): the sequential online-AGM prover model and its lifting to
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
-- Uniform sequential cuts (#128 F6, first brick): prefix-determinism at every squeeze index
-- is derived from the prover's execution order, never assumed.
assert_axioms Zcash.Snark.OracleComp.run_congr_of_agree
assert_axioms Zcash.Snark.SequentialCut.toPrefixDeterminedAt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- State surfaces (#128 F6): a semantic exclusion set read off the cut state costs
-- `(Q + 1) * epsilon`, with stability derived from the cut's execution order.
assert_axioms Zcash.Snark.SequentialCut.state_stable +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent_basis_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.SequentialCut.surfaceEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The state-surface discharge (#128 F6): each Action semantic failure event contained in
-- its cut state surface and priced at `(Q + 1) * epsilon`, views supplying every read.
assert_axioms Zcash.Snark.ActionTerminal.vkAt +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailureEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaFailureEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaFailureEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionXYFailureEvent_prob_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Per-state measures (#128 F7): each surface premise reduced to the staged counts.
assert_axioms Zcash.Snark.ActionTerminal.actionThetaBadSet_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBetaBadSets_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionGammaBadSets_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionYBadSet_measure_le +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- Challenge reads (#128 F6): what each semantic exclusion set consumes — congruences over
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
assert_axioms Zcash.Snark.TopLevelLookupCoherence.allTopLevelLookupThetaBadSet_congr
-- The captured Action capstone assembly (issue #128): the exact terminal event, the
-- derived-key checks and schedule, and the composed bound.
assert_axioms Zcash.Snark.Fixture.actionAcceptFalseEvent +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.derived_scalars +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate, CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.derived_lookups +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Keygen.certificate, CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.staticChecks_of_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Fixture.vk_advice_layout_length, Zcash.Snark.Fixture.vk_fixed_layout_length,
  Zcash.Snark.Fixture.vk_instance_layout_length, Zcash.Snark.Fixture.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture.vk_omega_order, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.schedule_of_derived +native(
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.Fixture.vk_chunk_width_le, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_lookup_input_degree_le, Zcash.Snark.Fixture.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture.vk_n_pred_le, Zcash.Snark.Fixture.vk_quotient_tail_le,
  Zcash.Snark.Keygen.certificate, CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.Fixture.orchard_action_acceptFalse_prob_le_captured +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  Zcash.Snark.Fixture.vk_advice_layout_length, Zcash.Snark.Fixture.vk_chunk_width_le,
  Zcash.Snark.Fixture.vk_fixed_layout_length, Zcash.Snark.Fixture.vk_gates_degree_le,
  Zcash.Snark.Fixture.vk_instance_layout_length, Zcash.Snark.Fixture.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture.vk_lookup_table_degree_le, Zcash.Snark.Fixture.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture.vk_n_pred_le, Zcash.Snark.Fixture.vk_omega_order,
  Zcash.Snark.Fixture.vk_quotient_tail_le, Zcash.Snark.Keygen.certificate,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
-- and a shape-polynomial bound with no fork-spread, adversary-dependent, or `|F|` term.  Choice
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
-- The rewind-free decode reaching #99's Action terminal
-- (`Circuits.Integration.StraightLineActionTerminal`): one accepting execution, no rewind, with
-- only the challenge exclusions left as premises.
assert_axioms Zcash.Snark.ActionTerminal.action_bundleStatement_or_relation_of_decode +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil,
  Zcash.Snark.actionCopyActiveRowFailures_eq_nil, Zcash.Snark.actionCopyAddressFailures_eq_nil,
  Zcash.Snark.actionCopyBounds, Zcash.Snark.actionMissingConstantAllocations_eq_nil,
  Zcash.Snark.actionNumPermCols_eq, Zcash.Snark.actionNumPermCols_pos,
  CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt,
  Zcash.Snark.ActionGateCoherence.gateData_eq, Zcash.Snark.ActionGateCoherence.selectorDegree,
  Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
assert_axioms Zcash.Snark.ActionTerminal.action_bundleStatement_or_relation_of_straightLineDecoded +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The fusion: the runs without the bundle statement are contained in the compressed event
-- plus four per-challenge exclusion events, and the semantic endpoint prices the union
-- (`Circuits.Integration.StraightLineActionEvent`).
assert_axioms Zcash.Snark.DeployedAlgebraicDecode.reRound
assert_axioms Zcash.Snark.straightLineAccepts_of_decoded +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ActionTerminal.actionRunDecode +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionRunAccepts +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionStatementDecoded +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionSemanticUpgradeContained +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBundleStatementFailure_prob_le_of_compressed_bound +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
-- The surface-form fusion: each event bound discharged from the squeeze machinery under
-- prefix-determinism at the five squeeze indices.
assert_axioms Zcash.Snark.straightLineRunReads_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ActionTerminal.actionThetaFailureEvent_subset_surface +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Snark.ActionTerminal.actionBundleStatementFailure_prob_le_of_surfaces +native(
  Zcash.Snark.actionConstantCellAddressFailures_eq_nil, Zcash.Snark.actionConstantSites_fit,
  Zcash.Snark.actionConstantValueFailures_eq_nil, Zcash.Snark.actionCopyActiveRowFailures_eq_nil,
  Zcash.Snark.actionCopyAddressFailures_eq_nil, Zcash.Snark.actionCopyBounds,
  Zcash.Snark.actionMissingConstantAllocations_eq_nil, Zcash.Snark.actionNumPermCols_eq,
  Zcash.Snark.actionNumPermCols_pos, CompElliptic.Fields.Pasta.pallasBase,
  Zcash.Snark.ActionFixedCoherence.queryCoverageFailures_eq_nil,
  Zcash.Snark.ActionFixedCoherence.realizationFailures_eq_nil,
  Zcash.Snark.ActionGateCoherence.domainExponent_lt, Zcash.Snark.ActionGateCoherence.gateData_eq,
  Zcash.Snark.ActionGateCoherence.selectorDegree, Zcash.Snark.ActionPermutationDomain.chunks_eq,
  Zcash.Snark.ActionPermutationDomain.columnCount_chunkLen_eq,
  Zcash.Snark.ActionPermutationDomain.deltaPowers_injective,
  Zcash.Snark.ActionPermutationDomain.domainExponent_eq,
  Zcash.Snark.ActionPermutationDomain.domainExponent_lt,
  Zcash.Snark.ActionPermutationDomain.queryLayouts_eq,
  Zcash.Snark.ActionPermutationDomain.routingCoherent,
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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
assert_axioms Zcash.Snark.snarkExtractionDeployed_prob_le_via_wrapped_pinned_roots +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedDeployedRootFSFamily.deployedRelation_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedRootFailure_subset_landing +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedDecodeFailure_subset_union +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedNonRelationFailure_prob_le_of_generatorRO +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkExtractionDeployed_prob_le_via_deployed_roots +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Online-source constraint composition.  All disagreement branches retain concrete relation
-- coefficients and are charged through the same single-instance textbook-DLOG finder.
assert_axioms Zcash.Snark.deployedConstraint_memberPoly_eq_online +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedOnlineConstraintOutcomeOfDecode +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintFailure_subset_union +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintRelation_prob_le_of_generatorRO_textbookDL +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintRelationFinderCalls +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintRelationFinderCalls_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedConstraintReductionEfficient +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintReductionEfficient_poly +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintRelation_prob_le_of_generatorRO_truncated_textbookDL +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsDeployed_prob_le_via_deployed_roots_of_relation_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsDeployed_prob_le_via_deployed_roots +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsDeployed_prob_le_of_online_outcome +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintUpgradeContained_of_root +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintOutcomeOfRoot_relation_eq_online +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintDecodedOfRoot +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintBadX_subset_landing +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintBadX_prob_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsDeployed_prob_le_of_root_schedule +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsDeployed_prob_le_of_root_schedule_runtime +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.DeployedConstraintSemanticUpgradeContained +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.deployedConstraintSemanticFailure_subset_union +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsSemanticDeployed_prob_le_of_root_schedule +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.snarkConstraintsSemanticDeployed_prob_le_of_root_schedule_runtime +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Primary straight-line AGM capstone. The staged representation trace, not the final
-- `AlgebraicWfProof` alone, supplies IPA squeeze chronology, and the family's own constraint-`x`
-- trace derives exact `x` pinning rather than assuming it. Its complete deployed constraint
-- finder has a pointwise four-invocation bound and therefore needs no AFK truncation or Markov
-- term. Representations remain ghost extractor data, outside the Halo2 proof and verifier.
assert_axioms Zcash.Snark.StraightLineIpaOnlineTrace.toSqueezeInvariance +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicWfProof.straightLineIpaZeroOrRelation +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedConstraintFSFamily.ofCovered +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedDeployedConstraintFSFamily.pinnedX +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineIpaFSFamily.straightLineIpaRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDeployedRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinderCalls_le_four +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailureSet_subset +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The straight-line four-budget semantic promotion, mirroring the recursive side.
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineConstraintSemanticUpgradeContained +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_subset_union +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Direct-route costs: both possible direct decodes charge their represented source traversal, the
-- query ceiling loses three bits, and the complete group-work allowance includes the verifier MSM
-- and other reduction postprocessing rather than treating the whole reduction as group-free.
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogRandomOracleQueries_le_eight_mul +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork_le_eight_mul
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineDirectDlogProfile.solverCost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Compatibility only: the older envelope allows caller-supplied reduction work and is not the
-- primary deployed interpretation.
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork_le_32_mul
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.five_bit_overhead_at_2pow122

-- Primary straight-line AGM capstone. The staged representation trace, not the final
-- `AlgebraicWfProof` alone, supplies IPA squeeze chronology, and the family's own constraint-`x`
-- trace derives exact `x` pinning rather than assuming it. Its complete deployed constraint
-- finder has a pointwise four-invocation bound and therefore needs no AFK truncation or Markov
-- term. Representations remain ghost extractor data, outside the Halo2 proof and verifier.
assert_axioms Zcash.Snark.StraightLineIpaOnlineTrace.toSqueezeInvariance +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.AlgebraicWfProof.straightLineIpaZeroOrRelation +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedDeployedConstraintFSFamily.ofCovered +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedDeployedConstraintFSFamily.pinnedX +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineIpaFSFamily.straightLineIpaRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDeployedRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinder +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintRelationFinderCalls_le_four +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailureSet_subset +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The straight-line four-budget semantic promotion, mirroring the recursive side.
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineConstraintSemanticUpgradeContained +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_subset_union +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Direct-route costs: both possible direct decodes charge their represented source traversal, the
-- query ceiling loses three bits, and the complete group-work allowance includes the verifier MSM
-- and other reduction postprocessing rather than treating the whole reduction as group-free.
assert_computable Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps +choice +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogRandomOracleQueries_le_eight_mul +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork_le_eight_mul
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.StraightLineDirectDlogProfile.solverCost_le +native(CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- Compatibility only: the older envelope allows caller-supplied reduction work and is not the
-- primary deployed interpretation.
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork_le_32_mul
assert_axioms Zcash.Snark.ComputedStraightLineDeployedFSFamily.five_bit_overhead_at_2pow122

/-! ## The Action circuit — the halo2-native soundness trust surface

The circuit-layer soundness theorems live at the `native_decide` tier: they consume
`native_decide` certificates only — the six fixed-base window tables, small `interval_cases`
facts, and CompElliptic's Pallas point-count witness (`pallas_natCard`). These assertions pin
exactly that budget for the generic soundness theorems and for the fully-instantiated deployed
bundle — a `sorry` or any further axiom reached anywhere in the Action stack fails the build
here. -/

assert_axioms Zcash.Circuits.Action.Circuit.soundness +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Circuits.Action.Circuit.soundnessPost +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.windowScalar_ne_zero,
  Zcash.Circuits.Ecc.MulFixed.Short.windowScalar_ne_zero)
assert_axioms Zcash.Circuits.Action.orchardActionCircuit +native(
  CompElliptic.Curves.Pasta.Pallas.neg_five_not_isCube,
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

`specPost_to_ledger` is the bridge's whole consumer surface: composition with circuit
satisfaction lives on the Circuits side, where the `Constraints` predicate it would consume
is actually produced. -/

assert_axioms Zcash.Security.Ledger.Bridge.specPost_to_ledger +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Concrete.PallasGroup.pallas_base_card_lt_scalar_card,
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
consumer's census entry. Checking the lemma itself closes that hole. -/

assert_axioms Zcash.Arithmetic.Msm.evalNat_eq_evalNatFast
