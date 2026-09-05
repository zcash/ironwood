# Guide to the Ironwood Formalization

This page is for anyone deciding what to conclude, and what not to conclude, from this
formalization. This section is general; later sections of the page focus on the verifier
knowledge-soundness proof.

## The place of formalization in security assurance

A protocol formalization such as this one is not a "proof of security". It is a set of
claims that constrain the difficulty of various classes of attacks, relative to breaking
the cryptographic problems on which the protocol's security was intended to rest.
The classes of attacks it rules out are not exhaustive; they are relative to a particular
model of what adversaries are able to do.

Sometimes a formalization is presented as something that *has* to be complete in order
to be valuable. This idea might come from the fact that the formal logic in which it is
grounded has a "[principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion)",
such that if we make a mistake then it is possible to prove "false". In that case, it would
be possible to prove that a protocol is secure when it is not. But this does not take into
account how protocol formalization actually works. How it works is that we progressively
extend the model to cover ways in which the protocol could be vulnerable. If a flaw lies
in a particular piece, and we try to formalize that piece within the framework we've set,
then we won't be able to do it, and then we are very likely to find the flaw. This can only
really give confidence once the framework is mostly complete —which it is— because we need
to know that we are proving the right kinds of thing, that will eventually be composable.

Formalization cannot replace other forms of security assurance: informal security arguments;
conservative cryptographic design; detailed and complete specification; incident response
processes; careful software engineering practices; unoptimized reference implementations;
thorough code reviews; internal and third party audits; automated and manual testing;
supply chain integrity checks, etc. On the contrary, it should be interwoven with them, for
instance by checking that the formalized objects are consistent with the specification and
(where possible) that they match the same test vectors as the production implementation and
the unoptimized reference.

So, modelling gaps and the long-term task of closing them, gaining more and more confidence
as we go —and then maintaining the formalization in sync with the spec as the protocol
evolves— are not a side-issue; that process is the entire point. It is a process that finds bugs
just like any other assurance technique, but it is deeply more thorough than conventional
auditing or testing. If, as a protocol designer, you're having sleepless nights about a class of
potential security problems in a specific part of the protocol, then competently formalizing
that part gives you a very meaningful improvement in assurance. And it *is* feasible to be
thorough enough in coverage to *approach* what we might naively expect from "proven security"
more closely than by other methods.

On the flip side, there have been cases where formalization was used as an excuse to skip
other forms of assurance, which is positively harmful. See for example Nadim Kobeissi's paper
[Verification Theatre: False Assurance in Formally Verified Cryptographic Libraries](https://eprint.iacr.org/2026/192).
Even when we don't make the kind of mistakes described in Kobeissi's paper, it's easy to be
speaking in good faith and still end up overclaiming — as we have seen a number of times
during this formalization effort. It takes substantial labour to educate readers about what
they should *not* conclude from a formalization, and that is as much a matter of good
technical writing and teaching as of proof.

In particular, it turns out that AIs are very good at writing a lot of Lean code (and
comments) quickly. That is what made this development possible, but it also presents a
huge challenge to reining in complexity, verbosity, and overclaims. The path of least
resistance is to let the AI produce more output than is humanly reviewable. Using a
proof-oriented language like Lean makes this less terrible than it could be, but it is still
terrible: not only does it hide the wood for the trees; it introduces some biases in the
direction of "it's complicated, but trust us" that we need to actively resist. If this
formalization oversimplifies or fails to properly explain something, that's a deficiency
and needs to be fixed. We are still in the process of removing a lot of redundancy and
rewriting excessively jargon-laden documentation. This page aims to help by focussing
attention on the things most important for a human reader to assess.

# Scope

There are three foci for this formalization effort: the Action circuit, the Halo 2 SNARK,
and the ledger layer (the high-level protocol security properties). Ideally they should
fit together. They don't quite do so yet.

## Scope at the ledger layer

The formalization of *Spendability* and *Spend authority* properties is not yet
finished. It needs significant attention to the way honest parties are modelled: the
properties need to be strengthened by giving the adversary oracles that allow it to
control how the honest parties create transactions, generate keys (without telling the
adversary those keys), etc. That is how these properties were originally defined at
Zcon3 in [Understanding the Security of Zcash](https://raw.githubusercontent.com/daira/zcash-security/main/zcash-security.pdf).

The formalization of *Balance integrity* is in better shape (modelling honest parties is
not an issue for Balance properties; the adversary merely has to exhibit an unbalanced
consensus-valid ledger). All the important pieces have been completed, and the ledger
security arguments are now tied into the Action circuit knowledge soundness proof: the
composed extraction experiment annotates the ledger games' chains with the witnesses
that the circuit's extractor computes, at the deployed value bases. What remains on that
route is quantitative — per-bundle-size knowledge-soundness terms at a k·maxActions
factor ([#214](https://github.com/zcash/ironwood/issues/214)) — while the Spendability
and Spend Authority games still consume annotations directly
([#155](https://github.com/zcash/ironwood/issues/155)). Additional caveats are stated on
the [Ledger Security Games](ledger-security-games.md) page.

For tractability, the modelled ledger also abstracts away from the real protocol in
several directions:

* The real protocol has, at the time of writing, six chain value pools: the transparent pool;
  the lockbox (also transparent), and four shielded pools for Sprout, Sapling, Orchard, and
  Ironwood. The modelled ledger has one transparent pool, and one Orchard-protocol shielded
  pool (similar to either Orchard or Ironwood). We argue that this simplification is enough
  to capture realistic attacks, because the interaction of all other pools with a given
  shielded pool is as though the other pools are transparent. (It is a bit of an
  oversimplification for Orchard and Ironwood because they share addresses and key material;
  we may decide to either model this explicitly or justify more rigorously why that isn't
  needed.)
* Modelling of the hash-to-curve in the ledger games is not complete. This also particularly
  affects the formalization of the Spendability and Spend authority properties, because they
  depend on diversified address generation using $\mathsf{DiversifyHash}$, and so a realistic
  adversary has to be able to invoke the hash-to-curve. The first step is delivered: the
  deployed hash-to-curve is proven indifferentiable from a random oracle onto the group,
  with a concrete advantage bound, modelling the underlying field-element hash as a random
  oracle — see [Group-Hash Indifferentiability](group-hash-indifferentiability.md). What
  remains is to give the games' adversaries oracle access to it
  ([#188](https://github.com/zcash/ironwood/issues/188)).

# Circuit and SNARK layers

## Guide to the Circuit and SNARK Theorems

The verifier knowledge-soundness proof for the Orchard protocol (and therefore the
Ironwood pool) can be followed with one idea from cryptography — that a proof system lets
someone convince you of a claim without showing you the data behind it. Understanding that
idea needs no Lean, no Halo 2, and no background in formal or succinct proof systems. The
rest of this page tries to explain the modelling assumptions and heuristics the verifier
soundness claim rests on that are not established by a formal theorem, and therefore have
to be assessed by other means.

It is not a walkthrough of the proofs. The [proof map](proof-map.md) shows how the results
connect, the [source map](source-map.md) indexes the tree, [definitions](definitions.md)
covers the coined terms, [Security Models](security-models.md) states the models in full, and
the [Knowledge-Soundness Contract](knowledge-contract.md) reads the theorem field by field.
From here on, the subject is the Action circuit; for the protocol properties built on top
of it, see [Ledger Security Games](ledger-security-games.md).

## The claim

> If the deployed verifier accepts a proof, then whoever produced that proof could have
> handed you the secret data it is a proof *about* — unless they solved a problem that
> most cryptographers believe has been infeasibly difficult (although quantum computers
> could change this in a few years), or hit an event the theorem shows is vanishingly unlikely.

Two phrases are worth pinning down.

*The secret data* means numbers satisfying the circuit's equations. That satisfying them
amounts to a legitimate Orchard action — well-formed note, balanced value, correctly derived
nullifier, authorized spend — is itself proven.

*The deployed verifier* means the verifier as Lean models it: checked against a circuit
description Lean derives itself and compares against a captured copy, reading a proof already
decoded from bytes into points and numbers. That the captured copy is what Zcash ships, and
that the bytes on the wire decode to what the model is handed, are checked outside Lean.

## What you need to know first

**Circuit and witness.** The Action circuit is a large system of equations. The secret data —
which note is spent, its value, the key authorizing the spend — assigns numbers to its
variables. An assignment making every equation true is a **witness**.

**Commitments.** A commitment is a short value pinning down a much longer one: publishing it
fixes your choice without revealing it, and **opening** it means producing the long value and
convincing everyone it is what you committed to. Ironwood's commitments are weighted sums of
curve points from a fixed public list agreed in advance.

**Accepting.** Halo 2 lets a witness-holder produce a short proof the verifier checks without
seeing the witness. Ironwood runs it over the Vesta curve, and the verifier's work collapses
into one arithmetic test: combine the proof, the public inputs, and the circuit description
into a single weighted sum of curve points, and check it comes out to zero.

**Challenges.** Underneath, the protocol is a conversation — the prover sends something, the
verifier picks a random number and sends it back, for several rounds. Those numbers are
**challenges**, and they stop a cheating prover preparing everything in advance. The deployed
verifier is not interactive, so the conversation is simulated: each challenge is computed by
hashing everything sent so far, the **Fiat–Shamir transform**. The prover can compute them
too, but only after fixing the earlier messages they derive from.

**Knowing, not merely existing.** A weaker claim would say a witness *exists*. Not enough for
a payment system: the statement behind an Orchard action can be true while the person proving
it is not entitled to spend — the note is real and somebody holds the key, just not them. So
the claim is that *this* prover holds a witness, made precise by demanding an **extractor**, a
procedure that produces the witness given access to the prover.

It is vanishingly unlikely that the hardness of the problems on which Orchard's security
depends could be proven outright. What can be proven is a
trade: any prover that cheats can be turned, cheaply and mechanically, into a solver for a
problem believed (for now) infeasible. That trade is a **reduction**, and every theorem here has that
shape. Within the algebraic-adversary model that we consider, the assumed-infeasible
problem is always the same — given the fixed list of curve points, find multipliers,
not all zero, that cancel them to zero: a **nontrivial discrete-log relation**.

## What Lean actually proves

### The acceptance test

Lean assembles the weighted sum in the same order Halo 2's Rust verifier does. Acceptance
means the assembly succeeds, the structural checks pass, and the sum is zero. A first proof
step rewrites that compact test into the explicit equation the rest of the argument consumes.

### Classifying one accepting proof

An equation holding says nothing about who knew what. What closes the gap in this
formalization is the algebraic-adversary assumption below: the prover must show its work.
For every curve point it sends, it must declare a recipe of how to build it from points that
it was given. Read against those recipes, the equation forces one of three things.

* The recipes describe a genuine opening — the prover holds data satisfying the circuit, and
  the argument writes it down.
* The recipes cancel for the wrong reason: the prover found a relation among the fixed points.
  The argument writes the relation down instead.
* Neither, meaning the challenge fell in the small set of values that can mask a false
  equation. The bound below covers how often that happens.

Nothing is re-run with different answers: the prover runs once, and the classification
reads what that single run declared. That matters, because an extractor's cost is a count of
prover runs, and a count growing with the size of the field would be worth nothing in
practice. The adversary
also picks its own target, producing the public inputs and the proof together; everything
identifying that statement is hashed in before the first challenge, so it cannot be chosen
after the fact.

What comes out is **computed data**, not an assertion that something exists — load-bearing,
because on this curve a relation always exists, so a theorem merely claiming one existed would
say nothing at all (the
[breaks as computed data](../formal-verification.md#breaks-as-computed-data) convention rules
that out). And the witness satisfies the **whole** constraint system: not just the equations,
but the constraints forcing the same value into cells the circuit declares equal, and the
table lookups. Equations alone would be close to meaningless, since they do not force the
circuit's wiring to be respected.

### The probability bound

The two parts above are deterministic. The third branch is not, and it exists because the
verifier compresses its work: rather than checking far too many equations one at a time, it
checks a single weighted combination, the weights drawn from the challenges. If one equation
fails, the combination fails too — unless the weights land in the set that makes the failure
cancel. Lean bounds the size of that set, tiny against the field it is drawn from, and charges
the adversary for it once per hash query it is allowed.

A second, similar cost pays for reading the combination backwards, since knowing it holds is
not knowing that a particular equation holds in a particular row. Recovering those row-level
facts draws further challenges, each with its own priced chance of hiding a failure. None is
waved through as an assumption.

Together they bound the probability that the verifier accepts while extraction fails, for
every bundle size consensus allows. The bound splits in two: a discrete-log term, whose size
is the reader's premiss rather than the theorem's, and a statistical leftover the theorem
establishes outright. A reviewer judges the first term and simply reads the second.

## What you are trusting

### A hardness assumption on each curve

**Finding a discrete-log relation on each of Pallas and Vesta is infeasible** — for each
curve, no efficient adversary finds multipliers, not all zero, cancelling the points
output by the group hash to zero. This discharges every branch where the argument computes
a relation instead of a witness.

Pallas is relied on for security of the application protocol, both inside and outside the
Action circuit. Vesta is relied on for knowledge soundness of the SNARK, via the binding
property of the verifier's commitments.

In all cases, Lean proves the arithmetic of the cost — how many hash queries and how much
group work the reduction spends, each against an explicit ceiling. It falls on readers of
these proofs, outside the formalization, to interpret consequences for Zcash's security
properties according to their assessment of discrete-log hardness of Pallas and Vesta.
The latter is not a binary property; a reader might reasonably come to different conclusions
for different timescales based on their assessment of the timeline for quantum computer
development, for example.

### Three idealizations

These are not hardness assumptions; instead, they swap the real world for a more convenient
one. They are choices we took to make this formalization more tractable, with the trade-off
that attacks depending on the differences between the real world and the idealized one could
be missed.

* **The hash behaves like a truly random function** — the **random-oracle model**. This covers
  BLAKE2b, the conversion of hash output into numbers, and the derivation of the public point
  list. BLAKE2b is not formalized anywhere: the model treats it as an opaque box and assumes
  the box is random.
* **The attacker is algebraic** — assumed to declare, for every curve point it outputs, a
  recipe building it from points it was given. Real attackers owe no such explanation. This is
  what lets the reduction read a relation off the adversary's own output. Note where it sits:
  built into what counts as an adversary at all, rather than appearing as a hypothesis you can
  read off a theorem. An attacker that does not play along is outside the claim entirely — not
  covered with a weaker bound.
* **Attacks do not depend on specific encodings**. The formalization does not cover the
  concrete, byte-level encodings used to represent curve points, field elements, etc., either
  in transmitted protocol messages or in the Fiat–Shamir transcript. Instead, the formalization
  is expressed in terms of the abstract types used in the specification. This is a potentially
  significant category of gap, because (despite substantial attention to this area in audits
  and code review) Zcash implementations have had quite a few significant security bugs due to
  unintentionally non-canonical encodings, mishandling of exceptional cases in decoding, etc.
  It is a longer-term goal to extend the formalization to cover the byte-level encodings.

### The fixed list of curve points

The reduction treats the public list as *independent*, which is what turns "find a relation
among these points" into the discrete-log problem. The deployed protocol does not sample them:
it produces the list once by hashing public strings onto the curve and bakes the result in. So
security is proved for the family of protocols that sample the list, and the deployed protocol
is argued to inherit it — no theorem is ever instantiated at the real points.

The caveat is not the usual asymptotic hand-wave. An adversary has the protocol's *entire
lifetime* to attack one specific list, and the cost is amortized over every transaction ever
made against it. One such computation breaks the whole protocol at once, rather than one
transaction or one user. [Security
Models](security-models.md#fixed-bases-the-group-hash-and-the-reference-string) develops this at
length.

### How Fiat–Shamir is modelled

Lean models the hashing schedule exactly — what gets hashed, in what order, matching Halo 2's
verifier. The order is load-bearing and it is checked: each round's message is hashed in
*before* the challenge derived from it is drawn, so a later message cannot bend an earlier
challenge, which is what makes it harmless that the prover can compute challenges too. Lean
proves this of its own model, and captured fixtures check that model against real transcripts.

The byte layer beneath is not modelled. The sequence of things hashed is verified; how they
become bytes, and BLAKE2b itself, are not. Modelling the encoding would narrow the gap without
closing it, since the hash would remain outside the proof.

### Facts checked by running code, not by the kernel

A few closed numeric facts are established by compiling a program and running it rather than
by checking them inside Lean's kernel. Each records an axiom noting the compiler was trusted,
and the [trust discipline](../formal-verification.md#trust-discipline) pins every one at build
time. Alongside facts about the Vesta curve, the **fingerprint match** is the one tying the
model to the shipped code: it confirms Lean's assembled sum is identical to the Rust
verifier's — for the captured proofs in the repository, not for the verifier in general.

The programs those evaluations run are not small. They include the whole fast native
arithmetic: field operations, curve group operations, and the multi-scalar multiplication
the fingerprint match assembles. The algorithms themselves are proven correct against the
group law, inside the kernel, and every proof-carrying replacement of a slow definition by
a fast one is checked and censused. What the axiom records as trusted is the compiler's
translation of that proven code into the code that actually ran.

These facts *are* rigorously established; what is not established is that they hold on the
kernel alone. Being closed and re-checkable, they fail loudly rather than silently — the curve
facts were computed by an entirely different method when the Pasta curves were designed, so a
compiler bug would have to arrive at exactly the same wrong answer to slip through.

### The whole set, in one place

Everything above, collected.

1. **Discrete log is hard for considered adversaries on both Pasta curves** — Vesta carries
   the verifier's knowledge soundness; Pallas carries the Action circuit and the ledger
   properties built on it. Discrete log hardness is not a binary property; the feasibility
   of attacks may vary over time and according to the capabilities of an adversary.
2. **The hash behaves like a random oracle.** BLAKE2b is treated as fresh randomness with no
   exploitable structure, and is not formalized anywhere.
3. **The attacker is algebraic** — it shows its work for every curve point it outputs. One
   that does not is outside the claim rather than covered by it.
4. **Attacks do not depend on specific encodings.** The formalization speaks the
   specification's abstract types; how curve points and field elements become bytes, in
   protocol messages or in the transcript, is not covered.
5. **The deployed list of curve points is as good as a sampled one.** Security is proved for
   protocols that sample it; the real one is hashed into existence and baked in.
6. **The byte layer under the hashing schedule.** What gets hashed, and in what order, is
   checked; how those things become bytes is not.
7. **Facts established by running code trust the compiler.** Each is pinned to its
   owning declaration at build time, and each is independently re-checkable — but the
   compiled code they run is the whole fast native arithmetic, proven correct in the
   kernel and executed as the compiler translated it.
