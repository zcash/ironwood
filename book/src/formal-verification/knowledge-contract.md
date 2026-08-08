# The Knowledge-Soundness Contract

The Action circuit's knowledge-soundness result is one theorem,
`orchard_action_adaptiveStatement_knowledge_error_bound`. Reading that theorem tells you a
probability is bounded; it does not, on its own, tell you *what* is bounded, what a successful
extraction hands back, or what that thing certifies. Those live in the layers that prove it.

`Zcash/Snark/Contract/` gathers them. `KnowledgeContract` is a record with one field per question
an auditor must answer, and `actionKnowledgeContract` is its instance for the deployed Action
circuit. This page reads that instance in order.

Nothing in the contract layer is proved. It re-exports definitions and applies the endpoint
unchanged; its census pins carry the same axiom footprint as the endpoint itself. What it adds is
a single obligation, `witness_statement`, discussed below.

## The six questions

### 1. What is a run?

A pair: a **generator random-oracle table**, and one **Fiat–Shamir transcript**, drawn
independently. The URS basis is not sampled directly — it is *read from* the table by
`orchardGeneratorROBasis`, which models halo2's parameter derivation ($g_i = H(0 \| i)$, $W =
H(1)$, $U = H(2)$). Identifying that derivation with a random oracle is a
[modelling assumption](security-models.md#fixed-bases-hash-to-curve-and-the-reference-string),
not a theorem.

The adversary is *adaptive in the statement*: it outputs the public inputs and the proof together,
rather than being handed a statement to attack. The canonical verifying key and every selected
instance commitment are absorbed into the transcript before the first challenge, so the adversary
cannot choose its statement after seeing that challenge.

The adversary is also
[*algebraic*](security-models.md#the-algebraic-adversary-restriction): its output type,
`AlgebraicWfProof`, requires every group element it emits to carry a representation over the
basis. This is a restriction on the adversaries the bound covers, not an assumption that can be
discharged — non-algebraic adversaries are outside the claim entirely.

### 2. When does the verifier accept?

`ComputedAdaptiveActionStatementFSFamily.accepts` — halo2's checked acceptance, at the adversary's
own selected inputs and proof, over the URS read from the oracle table. This is `DeployedAccepts`:
the multiopen argument assembles and its MSM evaluates to zero. It is the deployed verifier's
condition, not a reformulation chosen to be convenient.

### 3. What does extraction return?

`ActionTerminal.ActionBundleWitness`: for every Action in the bundle, the circuit's private
witnesses together with proofs that they satisfy `ActionSpec` at the adversary's public inputs.
It is `Type`-valued — real data, not an existential.

The extractor is a total function returning `Option`. `none` is extraction failure, and it is the
only thing the bound is about. Executability is a property of the proving layer's extractor and
is checked where that extractor is defined; the contract record itself is `noncomputable` (its
law is a `PMF`) and re-checks nothing.

### 4. What does a returned witness certify?

`BundleStatement`: the semantic conclusion for every Action in the bundle.

This is the field that carries the weight. A bound on "accepted but extraction returned nothing"
is worthless if extraction is allowed to return junk — an extractor that returns an arbitrary
inhabitant on every run would drive that probability to zero while proving nothing. The
`witness_statement` field forecloses that: a returned witness *entails* the statement. This is the
vacuity an adversarial pass over the specifications exists to catch, and stating it as a field
means an instance cannot quietly omit it.

### 5. What is the failure event?

Accepted, yet extraction returned nothing. Both conjuncts matter: a run that never accepted is not
a failure, and neither is a run that accepted and yielded a witness.

### 6. What is the error?

The compositional formula the endpoint proves: the adversary's discrete-log advantage at its
query and group-work counts, plus $1/|\mathbb{F}|$, plus a per-query term collecting the
Schwartz–Zippel budgets of each challenge surface. Instantiated at the $2^{123}$ work-factor
target, it lands on $\mathrm{Adv}_{\mathrm{DLOG}}(2^{126}, 2^{126}) + 2^{-83}$.

## What the contract does not say

**Completeness.** That some run accepts, or that an honest prover's proof extracts, is a separate
property. A contract whose acceptance predicate holds nowhere satisfies every field. Read the
contract as a bound on the adversary, never as evidence that the circuit works.

**Ordinary soundness — because it is free.** Accepting a false statement is a special case of
knowledge failure: on a false statement the extractor must have returned `none`, since a returned
witness would have entailed it. So `acceptFalseStatement_le` gives the soundness bound at the same
error, for every contract, and no separate endpoint is advertised for it.

**The ledger.** The contract ends at `ActionBundleWitness`. Carrying that witness into the Orchard
ledger relation is a separate development, and an unfinished one: the circuit-level result is
knowledge soundness, while the ledger-level consequence is still ordinary soundness, because the
bridge to the ledger statement forgets the extracted witness into a proposition.

**The assumptions.** They are the arguments of `actionKnowledgeContract`, not fields of the
record: a nonzero generator `B`, an injective oracle-parameter query, the family-construction
obligations, and the costed discrete-log profile. They stay in that signature deliberately, so
that reading the contract cannot give the impression the claim is unconditional. Two more are
structural rather than arguments, carried by the adversary's *type*: the algebraic restriction
above, and the random-oracle modelling of the challenge schedule. What trusting each of these
means is the subject of [Security Models](security-models.md).

## Why the record is not Action-specific

`KnowledgeContract` is stated for any circuit. Action is its only instance today because it is the
only circuit carrying an advertised capstone — `CommitIvk`, `NoteCommit`, `Ecc`, `Sinsemilla`, and
`Poseidon` are components composed into its specification rather than independent surfaces.

The shape is already recurring, though. The [ledger security games](ledger-security-games.md) pair
a break event with a containment showing the event covers the property, then bound it — the same
three moves as `failure`, `witness_statement`, and `knowledge_sound`. Keeping the record generic
is what stops the second circuit's contract from becoming a second bespoke tree.
