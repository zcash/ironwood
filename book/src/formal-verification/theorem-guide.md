# Guide to the Theorems

**Who this is for.** This page is for anyone deciding how much to trust Ironwood's
verifier-soundness proof — a protocol engineer, a reviewer, or an auditor. It assumes one
idea from cryptography: that a proof system lets someone convince you of a claim without
showing you the data behind it. It assumes nothing else — not Lean, not Halo 2, and no
background in proof systems.

**What it gives you.** The claim in plain words, the assumptions it rests on, and — the point
of the page — **the list of things Lean does not prove, which somebody has to check by other
means.** Names from the development are kept out of the prose and collected in
[one table at the end](#where-this-lives-in-lean), so the page reads as English while still
telling a specialist where to look.

**What it is not.** This page is not a file-by-file walkthrough of the proofs. The
[proof map](proof-map.md) traces how the results connect, the
[source map](source-map.md) indexes the tree file by file, and the
[definitions](definitions.md) page defines the development's coined terms. Where this page
summarizes a model, [Security Models](security-models.md) states it in full. The capstone
itself — what a run is, what extraction returns, and what a returned witness certifies — is
read field by field in the [Knowledge-Soundness Contract](knowledge-contract.md). This page
covers knowledge soundness for the Action circuit; for the protocol properties built on top
of it — balance, key binding, and the ledger games — see
[Ledger Security Games](ledger-security-games.md).

## The claim, in one sentence

> If the deployed verifier accepts a proof, then whoever produced that proof could have
> handed you the secret data it is a proof *about* — unless they solved a problem the field
> believes is infeasible, or hit an event the theorem shows is vanishingly unlikely.

Two phrases in it are narrower than they look, and each marks a boundary of the result.

*The secret data* means an assignment of numbers that satisfies the circuit's equations.
Whether satisfying those equations amounts to a legitimate Orchard action — a well-formed
note, balanced value, a correctly derived nullifier, an authorized spend — is a separate
claim, and it is not proven. That is the output-side boundary.

*The deployed verifier* means the verifier checked against a description of the circuit
that Lean derives itself and certifies against a captured artifact, reading a proof that has
already been decoded into typed points and numbers. That the captured artifact is the one
Zcash actually deploys, down to its byte serialization, and that the bytes on the wire decode
to what the model is handed, are both checked outside Lean. That is the input-side boundary.

Everything below is the fine print between those two boundaries.

## What you need to know first

Six ideas carry the whole statement, and most of the difficulty sits in them rather than
in the proofs.

**A circuit, and a witness for it.** The Action circuit is a large system of equations over
a finite field. The secret data — which note is being spent, its value, the key authorizing
the spend — is an assignment of numbers to that system's variables. An assignment that
makes every equation come out true is a **witness**.

**Commitments, and opening them.** A commitment is a short value that pins down a much
longer one. Publishing it fixes your choice without revealing it; **opening** it later means
producing the long value and convincing everyone it is the one you committed to. A
commitment scheme is useful only if you cannot open one commitment to two different values,
a property called **binding**. Ironwood commits to field elements as weighted sums of curve
points drawn from a fixed public list that everyone agrees on in advance.

**The proof, and what accepting means.** Halo 2, the proof system Orchard uses, lets someone
holding a witness produce a short proof of that fact, which the verifier checks without ever
seeing the witness. Ironwood runs this over the Vesta elliptic curve, and the verifier's work
collapses almost entirely into one arithmetic test: it combines the commitments carried in
the proof, the public inputs, and the circuit description into a single weighted sum of curve
points, and checks that the sum comes out to zero — the curve's identity element. Acceptance
is that test together with the structural checks made while assembling it, and the Lean model
starts from a proof already decoded into typed points and numbers rather than from its bytes.

**Challenges, and where they come from.** A proof of this kind is not a static document the
verifier merely inspects. The protocol underneath it is a conversation: the prover sends
something, the verifier picks a random number and sends it back, the prover answers, and so
on for several rounds. Those random numbers are **challenges**, and they are what stops a
cheating prover from preparing everything in advance, since it has to answer questions it
cannot predict. The deployed verifier is not interactive, so the conversation is
simulated: each challenge is computed by hashing everything sent so far, a standard
construction called the **Fiat–Shamir transform**. A prover can compute those challenges just
as easily as the verifier can, but only after fixing the earlier messages they are derived
from, which is the same constraint the live conversation imposed.

**Knowing, rather than merely existing.** A weaker claim would say a witness *exists*. That
claim is worth something — it says the accepted statement is true — but it is not enough for
a payment system. The statement behind an Orchard action can be perfectly true while the
person proving it is not the one entitled to spend: the note is real and somebody holds the
key authorizing it, just not them. What rules that out is the claim that *this* prover holds
a witness, and cryptography makes it precise by demanding an **extractor**: a procedure that,
given access to the prover, produces the witness. If the witness can be extracted, the prover
demonstrably knew it. Every claim on this page is of that stronger kind.

**Reductions, and the one hard problem.** For a proof system of this kind, nobody can prove
outright that a prover cannot cheat, since that would settle open problems in complexity
theory. What can be proven is a
trade: any prover that cheats can be turned, mechanically and cheaply, into a solver for a
problem believed to be infeasible. That trade is a **reduction**, and every theorem here has
that shape. The infeasible problem is the same one throughout — given the fixed list of
curve points, find multipliers, not all zero, that make them cancel to the identity. Such a
set of multipliers is a **nontrivial discrete-log relation**. Binding is the same assumption
wearing a different hat, because two different openings of one commitment *are* such a
relation.

## What Lean actually proves

The argument runs in three steps, and reading them in order shows what each one adds.

**Step 1 — the acceptance test the deployed verifier runs.** Lean assembles the weighted sum
of curve points in the same order Halo 2's Rust verifier does, and acceptance means two
things together: the assembly succeeds, every structural check the verifier makes along the
way passing, and the resulting sum is the identity. A first proof step rewrites that compact
test into a longer, explicit equation, which is the same condition in the form the rest of
the argument consumes.

**Step 2 — classifying one accepting proof.** Step 1 establishes that an
equation holds. It says nothing about who knew what, so on its own it is not yet a soundness
claim. What closes that gap is the algebraic-adversary assumption described in the next
section: the prover is required to show its work, declaring for every curve point it sends a
recipe that builds the point out of the points it was handed. Given those recipes, the
accepting equation can be read as a statement about the recipes themselves, and at least one
of three things must then be true.

* The recipes describe a genuine opening. The prover really does hold data satisfying the
  circuit, and the argument writes that data down.
* The recipes cancel for the wrong reason. The equation holds not because the prover knew
  anything, but because the fixed curve points satisfy a relation the prover managed to find.
  The argument writes the relation down instead, and the next section explains why finding
  one is believed to be infeasible.
* Neither, in which case the challenge fell in the small set of values that can mask a false
  equation. The equation the prover satisfied would have failed for almost any other
  challenge the verifier could have drawn, and step 3 bounds how often that happens.

Nothing is re-run with different answers, and no tree of alternative conversations is built.
The classification costs a fixed, small number of runs — the combined finder invokes the
prover at most four times, inside the eight-fold envelope the endpoint this page quotes
accounts for — which matters because an extractor's cost is a count of prover runs, and a
count that grew with the size of the field would be worth nothing in practice.

The adversary is also allowed to pick its target. These are *adaptive-statement* results: it
outputs the public inputs and the proof together, rather than being handed a statement to
attack. The verifying key and every selected instance commitment enter the transcript before
the first challenge, so it cannot choose the statement after seeing one.

Two features of what comes out are worth pausing on.

* The result is **computed data**, not an assertion that something exists. That distinction
  is load-bearing rather than stylistic: on a curve of prime order a nontrivial relation
  always exists, so a theorem that merely claimed one existed would say nothing. The
  development's [breaks as computed data](../formal-verification.md#breaks-as-computed-data)
  convention exists to rule out exactly that failure.
* The witness that comes out satisfies the **full constraint system** — the custom gates,
  the copy constraints that force the same value to appear in cells the circuit declares
  equal, and the lookup arguments. Gates alone would have been close to meaningless, since
  they do not force the circuit's wiring to be respected.

**Step 3 — the probability bound.** Steps 1 and 2 are deterministic: given the proof and the
recipes, the outcome follows. What remains is the third branch above, and it is a question
about probability rather than algebra.

That branch exists because the verifier compresses its work. The Action circuit has far too
many equations to check one at a time, so the verifier checks a single equation instead — a
weighted combination of all of them, with the weights drawn from the challenges. If every
original equation holds, the combination holds. If even one of them fails, the combination
fails too, unless the weights happened to fall in the small set of values that make the
failure cancel. Lean bounds that set: at the captured key it contains at most $20470$ values,
out of a field with roughly $2^{254}$ of them, and the adversary is charged for it once per
query it is permitted to make.

A second, similar cost pays for reading that combined equation backwards. Knowing the
weighted combination holds is not the same as knowing that this gate holds in this row, that
this copy constraint is respected, or that this lookup value really does appear in its table.
Recovering those row-level statements draws four further challenges, and each one carries its
own priced chance of hiding a failure rather than exposing it. None of the four is waved
through as an assumption.

Together they give a bound on the probability that the deployed verifier accepts while
extraction fails, stated for every consensus-valid bundle size. It holds against an adversary
allowed a generous number of hash queries, and it splits in two: a discrete-log term, whose
size is the caller's premise rather than the theorem's, and a statistical remainder of
at most $2^{-83}$, which the theorem bounds outright. That remainder is a probability rather than a
work factor, so it is not the same kind of quantity as a bit-security level. A reviewer has
to judge the first term and can simply read the second.

## What you are trusting

The theorems trade cheating for a break of some primitive. Trusting the conclusion therefore
means trusting several quite different things, and it is worth keeping them apart, because
they fail in different ways.

### One computational hardness assumption

**Finding a discrete-log relation on Vesta is infeasible.** No efficient adversary can find
multipliers, not all zero, that cancel the fixed points to the identity, which is what
discharges every branch where the argument computes a relation instead of a witness.

There is a nuance here that is easy to read past. Lean proves the *resource arithmetic* — how
many hash queries and how much group work the reduction costs, each against an explicit
ceiling — but the final step, that an adversary with those resources has only a small chance
of solving discrete log on Vesta, is supplied to the theorems as a premise rather than
derived. That premise is where a concrete security estimate for Vesta enters, and it enters
from outside.

### Two restricted-adversary heuristics

The next two are **not** hardness assumptions, and reading them as though they were
overstates the result. They do not claim that any problem is difficult, but instead replace
the real world with a more convenient one: an idealized hash in place of a real one, or a
handicapped attacker in place of a real one. Nothing deployed satisfies them literally; they
are modelling choices, believed sound for protocols that were not built to exploit the gap.

* **The hash behaves like a truly random function.** Challenges are derived by hashing, and
  the proof treats that hash as a source of fresh randomness with no structure an attacker
  can exploit — the **random-oracle model**. This covers Blake2b, the conversion of hash
  output into field elements, and — for the statements that derive the public point list by
  hashing — that derivation too. Blake2b is not formalized anywhere in the development; the
  model treats the hash as an opaque black box and the security layer assumes that box is
  random.
* **The attacker is algebraic.** For the probability bound, the adversary is *assumed* to
  declare, for every curve point it outputs, a recipe building that point out of points it
  was given. Real attackers owe no such explanation. This assumption is what lets the
  reduction read a relation off the adversary's own output, and it is what makes extraction
  possible from a single accepting proof.

### The fixed list of curve points

The reduction treats the public list of curve points as *independent*, which is what turns
"find a relation among these points" into the discrete-log problem: each point is modelled as
a random multiple of one generator, and the reduction hides its challenge in that randomness.
The deployed protocol does not sample them. It produces the list once, by hashing public
strings to the curve, and bakes the result into the protocol as a reference string. So
security is proved for the family of protocols that sample the list, and the deployed
protocol is argued to inherit it — no Lean theorem instantiates the endpoints at the deployed
points.

That gap carries a caveat worth stating plainly, because it is not the usual asymptotic
hand-wave. An adversary has the protocol's *entire lifetime* to attack one specific list, and
the cost of finding a relation is amortized over every transaction ever made against it. A
single such computation breaks binding and knowledge soundness for the whole protocol at
once, rather than for one transaction or one user. [Security
Models](security-models.md#fixed-bases-hash-to-curve-and-the-reference-string) develops this
at length.

### How Fiat–Shamir is modelled

Lean models the hashing schedule exactly: which points and numbers get absorbed into the
transcript, and in what order, matching Halo 2's own verifier. Two consequences follow.

The order is load-bearing, and it is checked. Each round's message enters the transcript
*before* the challenge derived from it is drawn, so a later message cannot bend an earlier
challenge — which is what makes it harmless that the prover can compute the challenges too.
Lean proves this of its own model, and the fixtures check that model against transcripts
captured from the Rust implementation, so the identification with Halo 2 rests on those captures
rather than on inspection alone.

The byte layer beneath the schedule is not modelled: the typed sequence of transcript
elements is verified, but the encoding of those elements into bytes, the domain-separator
bytes, and Blake2b itself are not. Modelling that encoding would narrow the gap without
closing it, since the hash itself would remain outside the proof
([#66](https://github.com/zcash/ironwood/issues/66)).

### Facts established by computation rather than by the kernel

A handful of closed numeric facts — the fingerprint match described next, and CompElliptic's
facts about the Vesta curve, including its group order — are established by compiling a
program and running it rather than by checking the fact inside Lean's small trusted kernel.
Each records an axiom noting that the compiler was trusted, and the
[trust discipline](../formal-verification.md#trust-discipline) pins every one at build time.

These facts *are* rigorously established; what is not established is that they hold on the
kernel alone. The Vesta group order, for instance, was
[computed in Sage](https://github.com/zcash/pasta/blob/f0f7068552a3565786cb338448cb58bc36a8314a/amicable.sage#L184)
by an entirely different method when the Pasta curves were designed, so a Lean compiler bug
would have to arrive at exactly the same wrong answer to slip through unnoticed.

### The tie to the Rust verifier

One numeric check per captured fixture connects the Lean model to the shipped code. The
**fingerprint match** confirms that the weighted sum Lean assembles is identical to the one
the Rust verifier assembles, for the specific captured proofs and circuits checked into the
repository rather than for the verifier in general. Being re-checkable, it fails loudly: a
wrong answer shows up as a disagreement with an independent recomputation rather than
passing on faith.

## The assumption register

This is the part of the page worth printing out: everything the result rests on, in one
place, so a reader can count the items rather than gather them. Some are restated from
[above](#what-you-are-trusting), so that the list is complete on its own.

They are sorted into three tiers, because the tiers fail differently and only one of them can
ever shrink. **Terminal model assumptions** are intentional and permanent — they are what a
result of this kind is built on, not work left undone, and no future formalization discharges
them. **Deployment bindings** identify a Lean object with a shipped artifact; each could in
principle be closed by further work, but none is a cryptographic assumption. **Residuals** are
genuinely incomplete work, and each carries a tracker.

Compiler trust is deliberately absent from all three. It is not an assumption in this sense
but a property of *how* certain closed facts are checked, it is enforced at build time rather
than accepted by the reader, and it is covered
[above](#facts-established-by-computation-rather-than-by-the-kernel).

### Tier 1 — terminal model assumptions

| Assumption | What fails if it is false |
| --- | --- |
| **Discrete-log hardness on Vesta.** No adversary within the covered resource envelope can find multipliers, not all zero, that cancel the fixed points to the identity. Note where this enters: it is not a premiss of any theorem. The theorems are generic in an advantage function and exhibit an explicit relation finder, and you supply the judgement about what that finder can achieve. | Everything. Every branch where the argument computes a relation instead of a witness stops discharging, and binding goes with it. |
| **The adversary is algebraic.** Every curve point it outputs carries a recipe over the points it received. This is part of the adversary's *type* rather than a named hypothesis, which makes it easy to miss when reading a theorem statement. | Non-algebraic adversaries are outside the claim entirely — not covered with a worse bound. The extractor reads its witness off the recipes; with no recipe there is nothing to read. |
| **The hash behaves like a random oracle.** Challenges, and the derivation of the public point list, are treated as fresh randomness with no exploitable structure. Blake2b is not formalized anywhere in the development. | The Fiat–Shamir step. Interactive soundness would no longer carry to the deployed non-interactive check, and the challenge budgets below would lose their meaning. |
| **The fixed point list inherits the sampled one.** Security is proved for the family of protocols that *sample* the list; the deployed protocol *fixes* it by hashing public strings to the curve. | The transfer of every bound to the deployed system. The lifetime caveat above is the sharp form: one relation, found at leisure against one fixed list, breaks the protocol as a whole. |

### Tier 2 — deployment bindings

| Binding | What fails if it is false | Status |
| --- | --- | --- |
| **The byte layer under Fiat–Shamir.** The typed transcript schedule is modelled and checked against the captures; the encoding of those elements into bytes, the domain-separator bytes, and Blake2b itself are not. | The identification of the Lean verifier with the shipped one. The argument would still hold of the model, but would no longer be about the deployed verifier. | Tracked — [#66](https://github.com/zcash/ironwood/issues/66) |
| **The right circuit went in.** Lean derives the verifying key itself and certifies it against the captured artifact, so the derivation is no longer assumed. What remains is identifying that capture with Orchard's deployed key, down to its byte serialization. | The result would be about a circuit that is not the deployed one. This is the input-side boundary named at the top of the page. | Key-granularity anchoring in place; serialization external |
| **The challenge conversion.** Halo 2 draws a challenge by reducing hash output to a field element; the theorems draw one exactly uniform. The two are not definitionally equal, and the gap is carried as an explicit one-sided statistical-distance premiss rather than assumed away. | Every challenge budget shifts by the bias. The endpoints expose the transport, so a quantified bias can be substituted rather than invalidating the statement. | Explicit in the endpoint conclusion |
| **The circuit-side layout fixtures.** The layout dumps behind the circuit comparisons came from one-off instrumentation that was never published, so unlike the verifier captures they have no regenerate-and-diff pipeline. CI pins their bytes, and the pins live in the repository they guard. | Row-level layout content below the verifying key — and the base-circuit dump, which has no capture-side anchor at all — could be wrong with no check to catch it. | Pinned plus review; regeneration from released sources is follow-up |

### Tier 3 — residuals

| Residual | What fails if it is false | Tracker |
| --- | --- | --- |
| **The circuit means what we think it means.** Lean proves that a satisfied Action circuit yields either an explicit break or a genuine ledger action, so the correspondence itself is established. What is missing is that it is established without handing back the ledger witness as reusable data, so knowledge soundness for the circuit does not yet compose into knowledge soundness for the ledger. | The output-side boundary named at the top of the page, and the largest remaining gap. | [#147](https://github.com/zcash/ironwood/issues/147) |
| **Hash-to-curve is not adversary-queryable.** A realistic adversary can evaluate the group hash on inputs of its choice, obtaining points it holds with no recipe — so it is not algebraic over any fixed list. Each game instead fixes an enumerated list. | Games whose honest parties themselves derive points — spendability and spend authority — cannot express strategies a real adversary performs routinely. | [#188](https://github.com/zcash/ironwood/issues/188) |
| **Hidden group work is not measurable.** The cost language charges only the operations a program writes as explicit nodes; work performed inside an unreified callback would go uncharged. That no such work exists is a named premiss carried into the endpoints, and re-exported as a conclusion conjunct. | The resource accounting, and with it the meaning of the coverage numbers. The bound would still hold, but at counts the theorem no longer certifies. | A deep embedding would discharge it, at the cost of rewriting the reduction in that syntax |
| **Some hypotheses are still assumed inside Lean.** The direct-decode bound follows from a representation-length cap the generic development does not instantiate at a concrete deployed family. Smaller structural side conditions sit alongside it; the [definitions](definitions.md) page itemizes each with its Lean anchor. | The corresponding term of the bound, for a family exceeding the cap. | Open |
| **The reductions are efficient.** Lean counts the concrete costs — prover runs, hash queries, group operations, and the field operations of decoding what comes back — against explicit ceilings. What it does not formalize is efficiency in the complexity-theoretic sense: "runs in polynomial time" never appears, so the step from counted costs to an efficient adversary is read off the code rather than proved. | Nothing collapses; the counts are proved. What you supply is that a straight-line count is what efficiency means here. | By inspection. The extractor used to be the worrying case, since a rewinding extractor's proven bound grew with the field size; the straight-line construction removes that |

Tier 1 and tier 2 are the intended trusted base — the assumptions and identifications a
mechanized proof is *meant* to rest on. Tier 3 is the currently open surface: the distance
between "the extracted witness satisfies the deployed circuit's constraints over Vesta" and
"the deployed Orchard verifier is sound for real transactions." Being able to read that
distance off in full is the reason this page exists.

## Where this lives in Lean

For readers who want to check the prose against the source: everything above is described in
English precisely so this table can carry the names. Paths are relative to `Zcash/`.

| Described above as | In Lean | File |
| --- | --- | --- |
| The acceptance test | `DeployedAccepts` | `Snark/Soundness/Main.lean` |
| Rewriting it into the explicit equation | `deployedAccepts_verifierEq` | `Snark/Soundness/Main.lean` |
| The tie to the Rust verifier | `nonInteractiveFingerprint_matches_derived`, one per capture | `Snark/Fixtures/*/Boundary.lean` |
| One witness, opening *and* satisfying | `SnarkRelation` | `Snark/Soundness/Relation/KnowledgeSoundness.lean` |
| Gates, copy constraints, and lookups together | `circuitSatViaConstraints` | `Snark/Soundness/Relation/KnowledgeSoundness.lean` |
| Extraction from one accepting proof | `straightLineBindingAttackZIndexedRootOrRelation` | `Snark/Soundness/AGM/StraightLineIpa.lean` |
| Reading a relation off an algebraic adversary | `ProgrammedBasisEmbedding` | `Common/AlgebraicRelation.lean` |
| The challenges that would hide a false identity | `szBadSet` | `Snark/Soundness/Constraint/Constraints.lean` |
| Bounding how often such a challenge is drawn | `uniformChallenge_szBadSet` | `Snark/Soundness/Pricing/ChallengePricing.lean` |
| The adaptive-statement game | `AdaptiveStatementModel` | `Snark/Soundness/Action/AdaptiveStatementModel.lean` |
| The four row-level promotion budgets | `semanticEvent` | `Snark/Soundness/Action/AdaptiveStatementEvent.lean` |
| Accepting while extraction fails | `adaptiveStatementKnowledgeFailureEvent` | `Snark/Soundness/Action/AdaptiveStatementKnowledge.lean` |
| What extraction returns | `ActionTerminal.ActionBundleWitness` | `Snark/Soundness/Action/StraightLineTerminal.lean` |
| The probability bound quoted above | `orchard_action_knowledgeFailure_adaptiveStatement_2pow123_workFactor_generatorRO_for` | `Snark/Capstones/Action.lean` |
| Its resource accounting | `adaptiveStatementKnowledgeExtractorGroupWork`, `…RandomOracleQueries` | `Snark/Soundness/Action/AdaptiveStatementProfile.lean` |
| Soundness as the weaker consequence | `acceptFalseStatement_subset_knowledgeFailure` | `Snark/Soundness/Action/AdaptiveStatementKnowledge.lean` |
| The auditor-facing reading of all of it | `actionKnowledgeContract` | `Snark/Contract/Action.lean` |
| Hidden group work, as a named premiss | `CostedLabeledOracleComp.StagedGroupWorkFaithful` | `Snark/Soundness/AGM/CostedOracle.lean` |
| The sampled point list, and its oracle | `orchardGeneratorROBasis`, `orchardGeneratorROSetup` | `Snark/Soundness/AGM/ProbabilityVesta.lean` |
| The challenge-conversion gap | `PMFEventBiasLE` | `Snark/Soundness/Oracle/Model.lean` |
| The verifying key, derived and certified | `Keygen.certificate`; `vk_eq_toVerifierKey` against the capture | `Snark/Keygen/Certificate.lean`, `Snark/Fixtures/MultiAction/Honest/VkCertificate.lean` |
| The transcript absorb order | `deriveChallenges` | `Snark/Verifier/FiatShamir.lean` |
| The hash, as an opaque black box | the `squeeze` field of `FiatShamir` | `Snark/Verifier/FiatShamir.lean` |
| Build-time pins on all of the above | `assert_axioms`, `assert_computable` | `TrustBoundary.lean`, `Snark/Fixtures/*/TrustBoundary.lean` |
