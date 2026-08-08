# Guide to the Theorems

**Who this is for.** This page is for anyone deciding how much to trust Ironwood's
verifier-soundness proof — a protocol engineer, a reviewer, or an auditor. It assumes one
idea from cryptography: that a proof system lets someone convince you of a claim without
showing you the data behind it. It assumes nothing else — not Lean, not Halo 2, and no
background in proof systems.

**What it gives you.** The claim in plain words, and — the point of the page — **what it
rests on that no theorem establishes, and that somebody therefore has to judge by other
means.** Names from the development are kept out of the prose; the pages below carry them.

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
of curve points in the same order Halo 2's Rust verifier does. Acceptance means the assembly
succeeds, every structural check made along the way passes, and the resulting sum is the
identity. A first proof step rewrites that compact test into a longer, explicit equation —
the same condition, in the form the rest of the argument consumes.

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
The classification invokes the prover at most four times, inside the eight-fold envelope the
endpoint this page quotes. That matters because an extractor's cost is a count of prover
runs, and a count that grew with the size of the field would be worth nothing in practice.

The adversary also picks its own target. These are *adaptive-statement* results: it outputs
the public inputs and the proof together, rather than being handed a statement to attack. The
verifying key and every selected instance commitment enter the transcript before the first
challenge, so it cannot choose the statement after seeing one.

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

One nuance is easy to read past. Lean proves the *resource arithmetic* — how many hash
queries and how much group work the reduction costs, each against an explicit ceiling — but
the final step, that an adversary with those resources has only a small chance of solving
discrete log on Vesta, is supplied as a premise rather than derived. That premise is where a
concrete security estimate for Vesta enters, and it enters from outside.

### Two restricted-adversary heuristics

The next two are **not** hardness assumptions, and reading them as though they were
overstates the result. Rather than claiming a problem is difficult, they replace the real
world with a more convenient one: an idealized hash in place of a real one, a handicapped
attacker in place of a real one. Nothing deployed satisfies them literally; they are
modelling choices, believed sound for protocols not built to exploit the gap.

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
  possible from a single accepting proof. Note where it sits: the restriction is part of the
  adversary's *type* rather than a named hypothesis on any theorem, so it does not appear in
  the statements the way the discrete-log premise does. An adversary that is not algebraic is
  outside the claim entirely — not covered with a weaker bound.

### The fixed list of curve points

The reduction treats the public list of curve points as *independent*, which is what turns
"find a relation among these points" into the discrete-log problem: each point is modelled as
a random multiple of one generator, and the reduction hides its challenge in that randomness.
The deployed protocol does not sample them. It produces the list once, by hashing public
strings to the curve, and bakes the result into the protocol as a reference string. So
security is proved for the family of protocols that sample the list, and the deployed
protocol is argued to inherit it — no Lean theorem instantiates the endpoints at the deployed
points.

The caveat that comes with that gap is not the usual asymptotic hand-wave. An adversary has
the protocol's *entire lifetime* to attack one specific list, and the cost of finding a
relation is amortized over every transaction ever made against it. One such computation
breaks binding and knowledge soundness for the whole protocol at once, rather than for one
transaction or one user. [Security
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

A handful of closed numeric facts are established by compiling a program and running it,
rather than by checking the fact inside Lean's small trusted kernel. Each records an axiom
noting that the compiler was trusted, and the
[trust discipline](../formal-verification.md#trust-discipline) pins every one at build time.

The **fingerprint match** is the one that ties the model to the shipped code: it confirms
that the weighted sum Lean assembles is identical to the one the Rust verifier assembles —
for the captured proofs and circuits checked into the repository, not for the verifier in
general. CompElliptic's facts about the Vesta curve, including its group order, are the
others.

These facts *are* rigorously established; what is not established is that they hold on the
kernel alone. Being closed and re-checkable, they fail loudly rather than silently: the Vesta
group order was
[computed in Sage](https://github.com/zcash/pasta/blob/f0f7068552a3565786cb338448cb58bc36a8314a/amicable.sage#L184)
by an entirely different method when the Pasta curves were designed, so a Lean compiler bug
would have to arrive at exactly the same wrong answer to slip through unnoticed.
