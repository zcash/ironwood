# Guide to the Theorems

**Who this is for.** Anyone deciding how much to trust Ironwood's verifier-soundness
development — a protocol engineer, a reviewer, an auditor. It assumes you know roughly what a
zero-knowledge proof is *for*: a prover convinces a verifier that some statement is true without
revealing why. It does not assume you have read any Lean, and it does not assume you work on
proof systems.

**What it gives you.** The entry point. What the advertised theorems claim, and — the point of
the page — **an ordered list of everything you must satisfy yourself of personally**, with a link
to where each one is discussed at length. Lean names are kept out of the prose and collected in
[one table at the end](#where-this-lives-in-lean), so the page reads as English while still
telling a specialist exactly where to look.

**What it is not.** Not a tour of how the proofs work, and not a replacement for the pages it
points at. Read in this order:

- **this page** — what is claimed, and what you must check personally;
- [**The Knowledge-Soundness Contract**](knowledge-contract.md) — the Action capstone read
  field by field: what a run is, when the verifier accepts, what extraction returns, what a
  returned witness certifies, what the failure event is, and what the error is;
- [**Assumption Register**](assumptions.md) — every assumption in one table, sorted by whether
  it can ever be discharged;
- [**Security Models**](security-models.md) — what trusting each model actually means;
- [**Ledger Security Games**](ledger-security-games.md) — the protocol-property half.

The shape of the argument is in the [proof map](proof-map.md) and the
[proof journey](proof-journey.md); coined terms are in [Definitions](definitions.md); the source
tree is in the [Source Map](source-map.md).

## The claim, in one sentence

> If the deployed Action verifier accepts, then the adversary that produced the accepting
> proof could have handed you the private witnesses it is a proof *about* — except with a
> probability this development bounds explicitly, and only within the adversary class the
> statements quantify over.

Everything below is the fine print: which words are load-bearing, what the bound actually is,
and where the sentence is weaker than it reads.

## What is advertised

Five endpoints, all in `Zcash/Snark/Capstones/Action.lean`, all about the *deployed* Action
verifier, all for **every consensus-valid Action bundle size**:

| | What it adds |
| --- | --- |
| the compositional error formula | the bound in symbolic form, generic in the advertised advantage function |
| its staged-certified counterpart | the same, with the reduction's group work counted additively by a proved counter composition |
| the $2^{123}$ work-factor instantiation | the formula evaluated at a concrete coverage target |
| staged-certified at $2^{123}$ adversary work | the certified accounting, at that adversary budget |
| staged-certified at $2^{125}$ adversary work | the same, at the larger budget |

Reading any one of those theorems tells you a probability is bounded; it does not tell you *what*
is bounded, or what a successful extraction hands back. That is what
[the contract](knowledge-contract.md) is for, and an auditor should read it before accepting any
number on this page.

**Knowledge soundness is the only property advertised.** Ordinary soundness — that the verifier
does not accept a false statement — is the weaker consequence at the same error, so no separate
endpoint states it. On a false statement the extractor cannot have returned a witness, because a
returned witness entails the statement.

**The adversary chooses its statement.** These are *adaptive-statement* results: the adversary
outputs the public inputs and the proof together, rather than being handed a statement to attack.
The canonical verifying key and every selected instance commitment are absorbed into the
transcript before the first challenge, so it cannot choose the statement after seeing one.

**Extraction is straight-line.** One execution, no rewinding, and therefore no expected-runs
truncation and no Markov tail anywhere in the bound. The extractor reads the representations the
algebraic adversary supplies alongside its proof.

**The numbers are coverage parameters.** At $Q \le 2^{123}$ oracle queries the bound is
$\mathrm{Adv}_{\mathrm{DLOG}}(\cdot,\cdot) + 2^{-83}$, evaluated at $2^{126}$ queries and group
operations for the instantiated formula endpoint, and at $2^{124}$ queries and $2^{126}$ group
operations for the staged-certified ones. Read these as *how large an adversary the theorem
covers*, not as an estimate of Vesta's discrete-log cost, and not as a claim that Lean computes
that cost. [Security Models](security-models.md#the-resource-numbers-are-coverage-parameters)
explains why the target sits where it does.

## What you must check yourself

This is the part of the page worth printing out. None of the following is established by the
soundness theorems; each is yours to accept, and they fail in quite different ways. They are
ordered by how much of the result collapses if the item is wrong.

1. **The terminal model assumptions.** Vesta discrete-log hardness, the algebraic restriction on
   the adversary, the random-oracle modelling of the challenge schedule, and the fixed-URS /
   hash-to-curve heuristic. These are intentional and permanent — they are what a result of this
   kind rests on, not work left undone. [Register, tier 1](assumptions.md#tier-1--terminal-model-assumptions).

2. **The bindings to the deployed artifact.** That the transcript and verifying-key byte
   encodings are the deployed ones, and that halo2's challenge conversion is within the stated
   statistical distance of the uniform challenge the theorems draw. These are identifications
   between a Lean object and a shipped one; no theorem makes them.
   [Register, tier 2](assumptions.md#tier-2--concrete-deployment-bindings).

3. **The tracked residuals.** Staging fidelity of the costed programs, the representation-length
   invariant behind the three-decode bound, the bridge from circuit satisfaction to the Orchard
   ledger relation, and the modelling of hash-to-curve as adversary-queryable. Each has a tracker
   and a status. [Register, tier 3](assumptions.md#tier-3--tracked-residuals).

4. **The numeric oracles.** The fingerprint match against the Rust verifier, and CompElliptic's
   Vesta curve facts. Both are closed, re-checkable computations discharged by compiling and
   running code rather than inside Lean's kernel, so each adds a compiler-trust axiom — and each
   would surface as a disagreement with an independent recomputation rather than as silence. The
   [trust discipline](../formal-verification.md#trust-discipline) pins them at build time.

5. **The scope of the fingerprint match.** It holds **for the captured proofs**, not for the
   verifier in general: two honest accepting runs and two match-only runs on random proof
   strings. What it supports is the typed, post-decoding boundary between Rust and Lean — not
   universal byte-level refinement.

6. **Efficiency of the reductions.** Lean cannot express efficiency, so it is argued by
   inspection: the constructions are straight-line manipulations of their inputs. The resource
   *counts* are proved; that a straight-line count is what efficiency means here is the reading
   you supply.

Items 1 and 2 are the intended trusted base. Item 3 is the open surface, and it is where the
distance still lies between "the extracted witness satisfies the deployed Action circuit" and
"the deployed Orchard verifier is sound for real transactions." Being able to read that distance
off in full is the reason this page exists.

## What the development does not claim

**Completeness.** That some run accepts, or that an honest prover's proof extracts, is a separate
property from everything above. A bound on the adversary is never evidence that the circuit
works.

**Non-algebraic adversaries.** They are outside the claim entirely, not covered with a worse
bound.

**Concrete Blake2b.** The challenge hash is modelled as a random oracle. Nothing in Lean argues
that Blake2b behaves like one.

**The protocol.** The Snark endpoints end at the deployed Action circuit's witnesses. The
protocol-level properties — balance integrity, spendability, spend authority — are a separate
development with its own capstones and its own open edges; see
[Ledger Security Games](ledger-security-games.md).

## Where this lives in Lean

For readers checking the prose against the source. Paths are relative to `Zcash/`.

| Described above as | In Lean | File |
| --- | --- | --- |
| The compositional error formula | `orchard_action_knowledgeFailure_prob_le_adaptiveStatement_for` | `Snark/Capstones/Action.lean` |
| Its staged-certified counterpart | `orchard_action_knowledgeFailure_prob_le_adaptiveStatement_certified_for` | `Snark/Capstones/Action.lean` |
| The $2^{123}$ work-factor instantiation | `orchard_action_knowledgeFailure_adaptiveStatement_2pow123_workFactor_generatorRO_for` | `Snark/Capstones/Action.lean` |
| Staged-certified at $2^{123}$ / $2^{125}$ adversary work | `…_adaptiveStatement_certified_2pow123_work_generatorRO_for`, `…_certified_2pow125_work_generatorRO_for` | `Snark/Capstones/Action.lean` |
| Soundness as the weaker consequence | `ComputedAdaptiveActionStatementFSFamily.acceptFalseStatement_subset_knowledgeFailure` | `Snark/Soundness/Action/AdaptiveStatementKnowledge.lean` |
| The event being bounded | `adaptiveStatementKnowledgeFailureEvent` | `Snark/Soundness/Action/AdaptiveStatementKnowledge.lean` |
| What acceptance means | `DeployedAccepts`, and its verifier-equation form `deployedAccepts_verifierEq` | `Snark/Soundness/Main.lean` |
| What extraction returns | `ActionTerminal.ActionBundleWitness` | `Snark/Soundness/Action/StraightLineTerminal.lean` |
| The adaptive-statement game | `AdaptiveStatementModel` | `Snark/Soundness/Action/AdaptiveStatementModel.lean` |
| The algebraic restriction, in the adversary's type | `AGM.OnlineMembers.OnlineMemberProofData` | `Snark/Soundness/AGM/OnlineMembers.lean` |
| The generator random oracle and the sampled basis | `orchardGeneratorROSetup`, `orchardGeneratorROBasis` | `Snark/Soundness/AGM/ProbabilityVesta.lean` |
| The challenge oracle, and the deployed-law gap | `PMFEventBiasLE` | `Snark/Soundness/Oracle/Model.lean` |
| Staging fidelity, as a premiss | `CostedLabeledOracleComp.StagedGroupWorkFaithful` | `Snark/Soundness/AGM/CostedOracle.lean` |
| The circuit-correctness side conditions | `TopLevelCircuitCorrectness` | `Snark/Soundness/Circuit/Terminal.lean` |
| The fingerprint match | `nonInteractiveFingerprint_matches_derived`, per capture | `Snark/Fixtures/*/Boundary.lean` |
| Build-time pins on all of the above | `assert_axioms`, `assert_computable` | `TrustBoundary.lean`, `Snark/Fixtures/*/TrustBoundary.lean` |
