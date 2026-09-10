import Zcash.Snark.Contract.Knowledge
import Zcash.Snark.Capstones.Action

/-!
# The Action circuit's knowledge-soundness contract

The first instance of `KnowledgeContract`, gathering what
`orchard_action_adaptiveStatement_knowledge_error_bound` promises about the deployed Orchard Action
circuit.

Reading it answers the questions the endpoint's own statement answers only by traversing the layers
underneath it:

* **Runs.** A generator random-oracle table together with one Fiat–Shamir transcript, drawn
  independently. The basis is read from the table by `orchardGeneratorROBasis`.
* **Acceptance.** `ComputedAdaptiveActionStatementFSFamily.accepts`, which is halo2's checked
  acceptance at the adversary's own selected public inputs and proof.
* **Witness.** `ActionTerminal.ActionBundleWitness`, the private witnesses of every Action in the
  bundle carrying their `ActionSpec` satisfaction proofs.
* **Statement.** `BundleStatement`, the semantic conclusion for every Action in the bundle.
* **Failure.** Accepted, yet the executable extractor returned nothing.
* **Error.** The compositional formula the endpoint proves, in the adversary's DL advantage and the
  per-surface Schwartz–Zippel budgets.

Assumptions stay in the signature below rather than in the record: the nonzero generator, the
injective oracle-parameter query, the family construction, and the generic DL advantage profile.
That profile carries caller-supplied prover and reduction work labels; operational accounting is
the separate `AdaptiveStatementAdversaryCostCertificate` and
`CertifiedAdaptiveStatementDlogProfile` route consumed by
`orchard_action_adaptiveStatement_certified_knowledge_error_bound`. The ledger continuation begins
per Action at `Zcash.Security.Ledger.Bridge.actionSpecToLedgerData`; it is not part of this
contract.
-/

open scoped ENNReal

namespace Zcash.Snark.Contract

open Zcash.Snark ComputedAdaptiveActionStatementFSFamily
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Capstone
open Zcash.Snark.Keygen (actionProofParamsFor)
open Zcash.Circuits Zcash.Circuits.Action

/-- The deployed Action circuit's knowledge-soundness contract at one consensus-valid bundle size.

Every field is the object the proving layer already defines; the record only puts them beside each
other. `knowledge_sound` is the advertised endpoint, applied unchanged. -/
noncomputable def actionKnowledgeContract (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor numProofs))
    (profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
      family (adaptiveStatement_pairCount_lt numProofs family) B) :
    KnowledgeContract where
  -- One run: a generator-oracle table at the query labels, and one transcript table
  -- (`Coins`, from `Soundness/Action/AdaptiveStatementModel`).
  Run := (↥(Set.range query) → VestaG) × family.Coins
  -- Both drawn uniformly and independently; the oracle setup is
  -- `Soundness/AGM/ProbabilityVesta`'s.
  law :=
    independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype family.Coins)
  -- Deployed halo2 acceptance (`Soundness/Action/AdaptiveStatementModel`), over the basis read
  -- from the run's oracle table.
  Accepts r := family.accepts (orchardGeneratorROBasis query r.1) r.2
  -- The bundle witness type from `Soundness/Action/StraightLineTerminal`, which abbreviates
  -- `Circuits/Integration/TopLevelWitness`'s external bundle witness.
  Witness r :=
    ActionBundleWitness (family.runOutput (orchardGeneratorROBasis query r.1) r.2).inputs
  -- The executable witness projection from `Soundness/Action/AdaptiveStatementKnowledge`.
  extract r :=
    family.adaptiveStatementKnowledgeExtractor (adaptiveStatement_pairCount_lt numProofs family)
      (orchardGeneratorROBasis query r.1) r.2
  -- The semantic bundle conclusion from `Circuits/Action/TopLevel`.
  Statement r :=
    BundleStatement (family.runOutput (orchardGeneratorROBasis query r.1) r.2).inputs
  -- `StraightLineTerminal`'s lemma: an extracted bundle entails the statement.
  witness_statement := ActionBundleWitness.statement
  -- `AdaptiveStatementKnowledge`'s failure event, pulled back along the table→basis map …
  failure :=
    (fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
      family.adaptiveStatementKnowledgeFailureEvent
        (adaptiveStatement_pairCount_lt numProofs family)
  -- … and the identification that the pulled-back event is the fields' event, definitionally.
  failure_eq := rfl
  -- The endpoint's error formula verbatim; `algebraicRootBudget` is
  -- `Soundness/Composition/AlgebraicRootBudget`'s.
  knowledgeError :=
    (profile.advantage (adaptiveStatementDlogRandomOracleQueries family)
        (adaptiveStatementDlogGroupWork profile.proverGroupWork
          profile.reductionGroupWork) +
      1 / Fintype.card Fp) +
    (family.Q + 1 : ℕ) *
      (1 / Fintype.card Fp +
        actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal)) +
        algebraicRootBudget
          (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          actionCircuit.domainExponent +
        ∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
            Fintype.card Fp)
  -- The advertised endpoint from `Capstones/Action`, applied unchanged.
  knowledge_sound :=
    orchard_action_adaptiveStatement_knowledge_error_bound numProofs B hB query hquery family
      profile

end Zcash.Snark.Contract
