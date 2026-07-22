# Guide to the Theorems

**Who this is for.** Anyone deciding how much to trust Ironwood's
verifier-soundness proof — a protocol engineer, a reviewer, an auditor. It
assumes you know roughly what a zero-knowledge proof is *for*: a prover
convinces a verifier that some statement is true without revealing why. It does
not assume you have read any Lean, and it does not assume you work on proof
systems.

**What it gives you.** The claim in plain words, the assumptions it rests on,
and — the point of the page — **the list of things Lean does not prove, which
somebody has to check by hand.** Lean names are kept out of the prose and
collected in [one table at the end](#where-this-lives-in-lean), so the page reads
as English while still telling a specialist exactly where to look.

**What it is not.** Not a tour of how the proofs work. The shape of the argument
is in the [proof map](proof-map.md) and the [proof journey](proof-journey.md);
terms of art are in the [glossary](glossary.md); the two development-wide
conventions are on the [Formal Verification](../formal-verification.md) landing
page.

This page focuses on claims relating to the knowledge soundness of the
Action circuit with respect to its intended statement. For a map of how that
will be used to prove some of the high-level security properties of the Zcash
protocol, see the [Security Definitions](security-definitions.md) page.

## The claim, in one sentence

> If the deployed verifier accepts a proof, then whoever produced that proof
> could have handed you the secret data it is a proof *about* — unless they
> solved a problem the field believes is infeasible.

Everything below is the fine print: what each of those words means, how much of
the sentence Lean actually establishes, and where the sentence is currently
weaker than you might read it as being.

## The cast

Five ideas carry the whole statement. They are worth pinning down before the
theorems, because most of the difficulty is in the definitions rather than the
proofs.

**The circuit.** Zcash's Action circuit is a large system of equations over a
finite field. The secret data — which note is being spent, its value, the key
authorizing the spend — is an assignment of numbers to that system's variables.
An assignment that makes all the equations come out true is called a **witness**.
The circuit is designed so that witnesses correspond to genuine Orchard actions:
a well-formed note, balanced value, a correctly derived nullifier, an authorized
spend.

**Proof and verifier.** Halo 2, the proof system Orchard uses, lets someone
holding a witness produce a short proof of that fact. The verifier checks the
proof without ever seeing the witness. Ironwood runs this over the Vesta elliptic
curve, against a fixed public list of curve points that everyone agrees on in
advance.

**Accepting.** The entire Halo 2 verifier boils down to a single arithmetic test.
It combines the proof and the public list into one big weighted sum of curve
points, and checks that the sum comes out to zero — the curve's identity element.
That test *is* acceptance, and it is exactly what the Lean model encodes.

**Knowing, not merely existing.** A weak soundness claim would say a witness
*exists*. That is nearly worthless here: for almost any statement someone,
somewhere, could have a witness. The useful claim is that *this prover has one*,
and cryptography makes it precise by demanding an **extractor** — a procedure
that, given access to the prover, produces the witness. If you can extract it,
the prover demonstrably knew it. Everything on this page is a claim of this
stronger kind.

**Reduction.** Nobody can prove outright that a prover cannot cheat; that would
settle open problems in complexity theory. What can be proven is a trade:
*any* prover that cheats can be turned, mechanically and cheaply, into a solver
for a problem believed to be infeasible. That trade is a **reduction**, and every
theorem here has that shape. Throughout this development the infeasible problem
is always the same one: given a handful of fixed curve points, find multipliers,
not all zero, that make them cancel out to zero. Such a set of multipliers is
called a **nontrivial discrete-log relation**.

## What Lean actually proves

The statements form a ladder. Each rung takes something the rung above assumed
and replaces it with something proven. Reading them in order shows exactly what
is and is not established.

**Rung 1 — the honest placeholder.** At the top, "the verifier accepts" is left
as an unspecified condition, and the two hard steps — that acceptance yields a
witness, and that a witness means what we want it to mean — are written down as
explicit assumptions rather than proven. This rung claims nothing about the real
verifier. It exists so that the hard parts are quarantined somewhere visible
instead of being smuggled in later.

**Rung 2 — the real acceptance test.** Here the placeholder is replaced by the
test the deployed verifier actually runs: assemble the weighted sum of curve
points in the same order Halo 2's Rust verifier does, and check it is zero. A
first proof step rewrites that compact test into the explicit equation Halo 2's
inner-product argument works with — the same condition, in a form the rest of the
argument can consume.

**Rung 3 — extraction, with its escape hatch.** This is the heart of it. From an
accepting proof, the argument **rewinds**: it re-runs the prover from the same
starting point but answers its questions differently, collecting several
accepting runs that agree on their early history and diverge later. Two things
can happen, and the theorems cover both:

* The collected runs fit together, and the argument **computes** a witness —
  one that both opens the commitment and satisfies the circuit's equations. Along
  the way, the verifier's spot-check of the circuit at a single random point gets
  lifted to the full polynomial identity: were the identity false, only a tiny
  fraction of points could have hidden that, so a passing spot-check is
  overwhelmingly likely to mean it really holds. Lean bounds that tiny fraction,
  but the step from "unlikely" to "this particular challenge was fine" is taken as
  a hypothesis rather than discharged — see the checklist.
* The runs do *not* fit together, and the argument **computes** a nontrivial
  discrete-log relation — the thing assumed infeasible.

Both branches produce actual data, not an assertion that something exists. That
distinction is load-bearing rather than stylistic: on a curve of prime order a
nontrivial relation always exists, so a theorem that merely claimed one existed
would be saying nothing at all. The development's
[breaks as computed data](../formal-verification.md#breaks-as-computed-data)
convention exists to prevent exactly that failure.

**Rung 4 — the probability statement.** The rungs above take "we obtained several
accepting runs" as given. The top rung constructs them, from an adversary allowed
a bounded number of hash queries, and pays for the chance that rewinding fails to
produce what is needed. The result is a bound: the probability of producing an
accepting proof that resists extraction is small, so long as the discrete-log
problem is hard. A companion statement covers binding — that a prover cannot open
one commitment two different ways.

## What you are trusting

The theorems trade cheating for a break of some primitive. Trusting the
conclusion therefore means trusting several quite different things, and it is
worth keeping them apart, because they fail in different ways.

### One computational hardness assumption

**Finding a discrete-log relation is infeasible.** No efficient prover can find
multipliers, not all zero, that cancel the fixed generators to zero. This is what
discharges every "the runs didn't fit together" branch. Commitment binding is the
same assumption wearing a different hat: two different openings of one commitment
*are* such a relation.

This is a genuine hardness assumption — a claim that a specific computational
problem is hard, of the kind the field has studied for decades.

### Two restricted-adversary heuristics

The next two are **not** hardness assumptions, and reading them as though they
were overstates the result. They do not claim any problem is difficult. They
replace the real world with a more convenient one: a hash function with an
idealized one, or a real attacker with a handicapped one. Nothing deployed
satisfies them literally. They are modelling choices, believed sound for
protocols that were not built to exploit the gap.

* **The hash behaves like a truly random function.** Challenges are derived by
  hashing; the proof treats that hash as a source of fresh randomness with no
  structure an attacker can exploit. This covers Blake2b, the conversion of hash
  output into field elements, and — for the statements that derive the public
  point list by hashing — that derivation too. Blake2b itself is not formalized
  in Lean anywhere; the model treats the hash as an opaque black box, and the
  security layer assumes that box is random.
* **The attacker is algebraic.** For the probability statement of rung 4, the
  adversary is *assumed* to declare, for every curve point it outputs, a recipe
  building that point out of points it was given. Real attackers owe no such
  explanation. This assumption is what lets the reduction read a relation off the
  adversary's own output.

### What the Fiat–Shamir model buys and costs

The deployed verifier is non-interactive: rather than an actual back-and-forth,
every challenge is computed by hashing everything sent so far. Lean models that
sequence exactly — which points and numbers get absorbed, and in what order,
matching Halo 2's own verifiers. Three consequences an auditor should internalize:

* **The order is load-bearing, and it is checked.** Each round's message enters
  the transcript *before* the challenge that depends on it is drawn, so a later
  message cannot bend an earlier challenge. Lean proves this. But it proves it of
  *the model's* ordering, which is trusted to match Halo 2's.
* **Rewinding is only meaningful in the idealized world.** "Re-run the prover and
  answer differently" means reprogramming the hash mid-conversation. That is a
  legitimate move against a random oracle and a meaningless one against Blake2b,
  which is a fixed function. Extraction rests on this, so it inherits the
  idealization.
* **The gap between Blake2b and a random oracle is yours to accept.** Nothing in
  Lean argues that Blake2b behaves like a random oracle. That identification is
  an act of judgement, made outside the proof.

### One assumption about the input

**The verifying key describes the real circuit.** The verifier is handed a
compact description of the circuit it is checking against. Everything proven here
is relative to that description. That it faithfully encodes the Action circuit
Zcash actually deploys is assumed, not proven.

### Compiler trust

Separately from all the above, the statements about the concrete Vesta curve rest
on **compiler trust**. A few closed numeric facts — the captured fingerprint
match described below, and CompElliptic's facts about the Vesta curve, its group
order among them — are established by compiling a program and running it, rather
than by checking the fact inside Lean's small trusted kernel. Each such fact adds
an axiom recording that the compiler was trusted.

These facts *are* rigorously established; what is not established is that they
hold on the kernel alone. The Vesta group order, for instance, was
[computed in Sage](https://github.com/zcash/pasta/blob/f0f7068552a3565786cb338448cb58bc36a8314a/amicable.sage#L184)
by an entirely different method when the Pasta curves were designed, so a Lean
compiler bug would have to arrive at exactly the same wrong answer to slip
through unnoticed.

### The tie to the Rust verifier

One more numeric check connects the Lean model to the shipped code: the
**fingerprint match** confirms that the weighted sum Lean's model assembles is
identical to the one the Rust verifier assembles. Read the scope carefully — it
holds **for the specific captured proofs and circuits checked in**, not for the
verifier in general. It is a re-checkable numeric fact: another implementation,
or careful hand computation, would produce the same number, so a wrong answer
should be catchable by disagreement rather than by faith.

## What Lean does not prove

This is the part of the page worth printing out. To trust the end-to-end result
you have to satisfy yourself of each of the following independently; none is
established inside the soundness theorems.

1. **The assumptions and idealizations hold.** Discrete-log relation hardness on
   Vesta — the one real hardness assumption — plus the two restricted-adversary
   heuristics: that the hash behaves randomly, and that the attacker is
   algebraic.

2. **The numeric oracles are right.** The fingerprint match against the Rust
   verifier, and CompElliptic's Vesta curve facts. Both are closed, re-checkable
   computations, so an error should surface as a disagreement with an independent
   recomputation. The [trust discipline](../formal-verification.md#trust-discipline)
   pins them at build time.

3. **The right circuit went in.** That the verifying key handed to the verifier
   encodes the *real* deployed circuit — its equations, its query layout, its
   fixed commitments. Outside Lean; not started.

4. **The circuit means what we think it means.** That satisfying the circuit's
   equations really does amount to a valid Orchard action — well-formed note,
   balanced value, correctly derived nullifier, authorized spend. In the theorems
   this is a free-floating placeholder statement, connected to circuit
   satisfaction by an assumption rather than a proof. The chain currently stops at
   "the extracted witness satisfies the equations," and everything from there to
   "this is a legitimate transaction" is unproven. This is the mirror image of
   *the right circuit went in*, on the output side. Outside Lean; not started.

5. **Only the gate equations are covered.** A Halo 2 circuit is enforced by three
   kinds of constraint: the gate equations, the copy constraints that force the
   same value to appear in cells the circuit declares equal, and the lookup
   arguments. Only the gate equations are formalized. This matters a great deal,
   because gate equations alone constrain very little — without copy constraints
   nothing forces the circuit's wiring to be respected. Folding in the
   permutation and lookup arguments is tracked in
   [#36](https://github.com/zcash/ironwood/issues/36).

6. **Some hypotheses are still assumed inside Lean.** The most consequential is
   the **decode gap**. The extracted witness is a list of field elements; using it
   as circuit data requires decoding it into the circuit's columns. That decoding
   is currently a free function, not tied to the extracted witness — so as the
   statement stands, the circuit-satisfaction half may not constrain the extracted
   witness *at all*. The lemma that would tie them together is proven but not yet
   wired in. Until it is, treat the constraint side as open rather than merely
   incomplete. Alongside it sit several smaller structural side conditions and the
   good-challenge and accept-probability hypotheses, assumed and accounted for
   rather than discharged; the [glossary](glossary.md) itemizes each with its Lean
   anchor.

7. **The reductions are efficient.** Lean cannot express efficiency at all, so it
   is argued by reading the code: each reduction is a straight-line manipulation
   of its inputs, with no loops or search. The extractor is the exception, and it
   is the one number worth understanding. It works by re-running the prover, so
   its cost is a *count of prover runs*, and that count must stay manageable as
   proofs grow. Writing $k$ for the number of rounds and $|F|$ for the size of the
   field — astronomically large for Vesta — the bound proven with no extra
   hypothesis is $(2\cdot|F|+1)^k$. That grows with the field size, so as a
   practical guarantee it is worth nothing. A usable bound, $(6/\delta)^k$, is
   also proven, but only under an additional hypothesis: that wherever the
   extractor rewinds, at least a $\delta$ fraction of the possible challenges
   would lead to an accepting run. Proving a bound that is both usable and
   unconditional is open work. Separately, "efficient prover" in the formal
   complexity-theoretic sense never appears in Lean at all.

The first two are the intended trusted base — the assumptions and re-checkable
computations a mechanized proof is *meant* to rest on. The remaining five are the
currently open surface: the distance between "the extracted witness satisfies the
gate equations over Vesta" and "the deployed Orchard/Ironwood verifier is sound
for real transactions." Being able to read that distance off in full is the
reason this page exists.

## Where this lives in Lean

For readers who want to check the prose against the source. Everything above is
described in English precisely so this table can carry the names.

| Described above as | In Lean | File |
| --- | --- | --- |
| Rung 1, the honest placeholder | `orchard_verifier_sound_conditional` (Vesta: `orchard_verifier_sound_vesta_conditional`) | `Soundness/Main.lean`, `Soundness/Vesta.lean` |
| "acceptance yields a witness", assumed at rung 1 | `ExtractableFromAcceptance` | `Soundness/Main.lean` |
| "a witness means what we want", assumed at rung 1 | the `hencodes` hypothesis, concluding a free proposition `S` | `Soundness/Main.lean` |
| Rung 2, the real acceptance test | `DeployedAccepts`, built by `assemble?` | `Soundness/Main.lean`, `Verifier/Assemble.lean` |
| Rewriting it into the explicit equation | `deployedAccepts_verifierEq`, yielding `DeployedIpaVerifierEq` | `Soundness/Main.lean`, `Soundness/Deployed/Verification.lean` |
| The collected accepting runs | `ForkedTranscript` | `Soundness/Main.lean` |
| Rung 3, runs fit ⇒ opening | `orchard_verifier_deployed_opening_of_forked` (Vesta: `orchard_verifier_vesta_opening_of_forked`) | `Soundness/Main.lean`, `Soundness/Vesta.lean` |
| Rung 3, runs fit ⇒ circuit satisfaction | `orchard_verifier_deployed_constraint_of_forked` (Vesta: `orchard_verifier_vesta_constraint_of_forked`) | `Soundness/Main.lean`, `Soundness/Vesta.lean` |
| Lifting the spot-check to the full identity | `circuitSatViaGates_of_check`, with error bound `soundness_error` | `Soundness/KnowledgeSoundness.lean` |
| Rung 3, runs don't fit ⇒ computed relation | `NontrivialRelation.ofUnopenedFork` (Vesta: `…ofUnopenedForkVesta`) | `Soundness/Main.lean`, `Soundness/Vesta.lean` |
| Rung 4, the probability statement | `knowledgeSoundness_under_DL`, `binding_under_DL`, over `ComputedAlgebraicFSFamily` | `Soundness/Forking/Adversary/Algebraic.lean` |
| Discrete-log relation hardness | `DiscreteLogRelationHardFor` | `Soundness/Forking/Adversary/Algebraic.lean` |
| "one witness, opening *and* satisfying" | `SnarkRelation`, pairing `IpaRelation` with a circuit predicate | `Soundness/KnowledgeSoundness.lean`, `Soundness/InnerProduct.lean` |
| Gate equations only (checklist 5) | the predicate is instantiated to `circuitSatViaGates` | `Soundness/KnowledgeSoundness.lean` |
| The decode gap (checklist 6) | the unused `batch_open_soundV`; see the comment above `SnarkRelation` | `Soundness/IpaSoundness.lean`, `Soundness/KnowledgeSoundness.lean` |
| The hash, as an opaque black box | the `squeeze` field of `FiatShamir` | `Verifier/FiatShamir.lean` |
| The transcript absorb order | `deriveChallenges` | `Verifier/FiatShamir.lean` |
| The fingerprint match | `fingerprint_matches`, one per captured fixture | `Fixtures/SingleAction/Fixture.lean`, `Fixtures/MultiAction/Fixture.lean` |
| Build-time pins on all of the above | the `TrustBoundary` modules | `Snark/Soundness/TrustBoundary.lean` and siblings; `TrustBoundary.lean` for the protocol layer |

Paths are relative to `Zcash/`.
