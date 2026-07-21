# Guide to the Theorems

A prose reading of what the verifier-soundness theorems actually claim, the
assumptions they rest on, and — the point of the page — **everything a human
auditor must still check to trust the result.**

This is deliberately *not* a tour of the proof mechanics, the internal lemma
DAG, or the per-declaration API. Those live in the [proof map](proof-map.md),
the [proof journey](proof-journey.md), and the Lean source itself. Here we stay
on the *trusted surface*: the top-level statements, the definitions you need to
read them, and the boundary between what Lean proves and what you are trusting.
New terms are collected in the [glossary](glossary.md); the two development-wide
conventions (["breaks as computed data"](../formal-verification.md#breaks-as-computed-data)
and the ["trust discipline"](../formal-verification.md#trust-discipline)) are on
the [Formal Verification](../formal-verification.md) landing page.

## What is being claimed, in one paragraph

For the deployed Halo 2 verifier that Orchard/Ironwood runs over the Vesta
curve, a proof the verifier *accepts* can be turned — by an efficient
extractor — into a witness that both **opens the IPA commitment** and
**satisfies the circuit's gates**. The only escape hatch is that the prover
instead computed a nontrivial discrete-log relation among the fixed generators
$(g, U, W)$ — and the discrete-log assumption says no efficient prover can do
that. Everything below is the fine print: which theorem states which half of
this, what "accept" and "opens" and "satisfies" mean precisely, and which
pieces of the sentence are assumed rather than proven.

## The theorems, in words

The soundness statements come in a deliberate ladder, from a fully abstract
*conditional* form down to the concrete deployed verifier at Vesta. Reading them
in order shows exactly what each layer adds.

### Conditional soundness — `orchard_verifier_sound_conditional`

The top of the ladder (`Zcash/Snark/Soundness/Main.lean`) takes acceptance as an
**opaque `Prop`**. It says: *if* an accepting proof yields extraction data (the
hypothesis `ExtractableFromAcceptance` — a consistent transcript, an
`IpaRelation` opening, and a circuit witness), *and if* gate satisfaction
encodes the intended high-level statement (the hypothesis `hencodes`), then that
statement `S` holds.

Read it as a *quarantine*: the theorem is honest that it assumes the two hard
things — extraction and semantic adequacy — rather than proving them. It says
nothing about the fingerprint, because `accepts` is a free proposition unrelated
to the real verifier. Its Vesta specialization is
`orchard_verifier_sound_vesta_conditional`, identical in content, with the curve
pinned to `SWPoint Vesta.curve`.

### Deployed acceptance — `DeployedAccepts` and `deployedAccepts_verifierEq`

The deployed layer replaces the opaque `accepts` with the *real* accept
predicate. `DeployedAccepts` holds exactly when the verifier's MSM assembler
`assemble?` succeeds and the assembled multi-scalar multiplication **evaluates
to the group identity** against the URS. This is the concrete accept — the same
$\text{MSM} = 0$ condition the [fingerprint](glossary.md) pins to the Rust
verifier.

`deployedAccepts_verifierEq` is the first reduction step: it converts that
compact $\text{MSM} = 0$ accept into halo2's **explicit IPA verifier equation**
(`DeployedIpaVerifierEq`), the readable form the inner-product argument consumes.

### The deployed reduction — opening, constraint, and the binding branch

From an accepting deployed proof, a fork of the Fiat–Shamir transcript is
produced (a `ForkedTranscript`: a rewound, accepting IPA tree that opens the
pinned commitment after removing its declared $U$/$W$ components). The fork then
splits two ways:

* **Clean fork ⇒ extraction.**
  `orchard_verifier_deployed_opening_of_forked` extracts the opening witness $a$
  for the declared commitment (the blinded opening
  $\text{deployedCommitment} = \langle a, g\rangle + [p_U]U + [p_W]W$, with
  $\langle a, b\rangle$ equal to the pinned `multiopenValue`).
  `orchard_verifier_deployed_constraint_of_forked` additionally derives circuit
  satisfaction, lifting the verifier's gate point-check (`hquot`) at the
  challenge $x$ to the full polynomial gate identity via Schwartz–Zippel
  (`hgood`) — so the check constrains the *single extracted witness* $a$. Their
  Vesta forms are `orchard_verifier_vesta_opening_of_forked` and
  `_constraint_of_forked`.

* **Unclean fork ⇒ a computed break.**
  `NontrivialRelation.ofUnopenedFork` (Vesta: `…ofUnopenedForkVesta`) takes a
  forked transcript that does *not* project to a clean IPA tree and **computes**
  a nontrivial discrete-log relation among $(g, U, W)$. It does not merely assert
  one exists — at prime order one always does; it returns the coefficients as
  data, the object the discrete-log assumption forbids an efficient prover from
  finding.

### The computed Fiat–Shamir endpoints — `knowledgeSoundness_under_DL` / `binding_under_DL`

The legacy ladder above bundles the forking step as a hypothesis. The *computed*
reduction (`ComputedAlgebraicFSFamily` in
`Zcash/Snark/Soundness/Forking/Adversary/Algebraic.lean`) instead constructs the
forks from a bounded-query adversary and charges the query loss.
`knowledgeSoundness_under_DL` bounds the probability of an accepting proof that
resists extraction; `binding_under_DL` is its binding-side dual. Both are stated
in the AGM with an ideal random oracle, gated by per-family discrete-log
hardness (`DiscreteLogRelationHardFor`) and by the extractor's call bound.

## The security model — what you are trusting

The theorems are *reductions*: they convert a verifier that accepts a false
statement into a concrete break of an underlying primitive. Trusting the
conclusion therefore means trusting that those primitives are hard and that the
model faithfully represents the deployed system. The assumptions are:

* **Discrete-log relation hardness.** No efficient prover finds a nontrivial
  relation among the fixed generators $(g, U, W)$. This is where every "unclean
  fork" and "no clean opening" branch is discharged. Commitment binding is the
  same assumption in another guise: two openings of one commitment *is* a
  relation.
* **An ideal random oracle** for Blake2b and for field-element challenge
  conversion — and, on the generator-RO endpoints, for the hash-to-curve URS
  derivation. Identifying the deployed hash with a random oracle is external to
  Lean (see below).
* **The algebraic group model (AGM)** for the computed reduction: the adversary
  declares algebraic representations of the group elements it outputs.
* **CompElliptic's Vesta point-count.** A closed numeric fact discharged by
  `native_decide`, which adds one compiler-trust axiom. Concrete-curve endpoints
  inherit it; the per-theorem `#print axioms` pins record exactly where.
* **Verifying-key correctness** (input side): that the `VerifyingKey` handed to
  the verifier faithfully encodes the real deployed circuit. Assumed, not proven
  — see the checklist.

Two model limits are worth stating plainly. Reduction **efficiency** is the one
property Lean does not express: it is argued by inspection (the reductions are
straight-line manipulations of their inputs), and a *field-independent
polynomial* bound on the extractor's adversary-run count is still open — the
present bound is the exponential $(2\cdot|F|+1)^k$ fallback, with a polynomial
$(6/\delta)^k$ available only under a fork-spread hypothesis. And adversary
running time as a PPT bound is external throughout.

## How Fiat–Shamir is modeled

The deployed verifier is non-interactive: every challenge is derived by hashing
the transcript absorbed so far. The model (`Zcash/Snark/Verifier/FiatShamir.lean`)
records halo2's absorb/squeeze order exactly — points, scalars, and challenge
markers written in the same sequence as halo2's PLONK, multiopen, and commitment
verifiers — and treats the hash as an abstract `FiatShamir.squeeze`. **Blake2b
itself is not formalized.** The security layer then idealizes `squeeze` as a
random oracle.

The consequences an auditor should internalize:

* **The transcript order is load-bearing.** Round-by-round soundness means each
  IPA round point sits in the transcript *before* the challenge that folds it is
  drawn, so a later message cannot bend an earlier challenge. This ordering is a
  proven property, not an assumption — but it is a property *of the model's
  absorb order*, which is trusted to match halo2.
* **Forking is oracle rewinding.** The forking lemma re-runs the schedule with
  the random oracle reprogrammed at a round prefix; redrawing the IPA round
  vector *is* reprogramming the deployed oracle. Extraction rests on this, so it
  rests on the random-oracle idealization.
* **The Blake2b ↔ random-oracle gap is yours.** Nothing in Lean argues that
  Blake2b with halo2's field-conversion behaves like a random oracle. That
  identification, and the hash-to-curve URS derivation on the relevant
  endpoints, are trusted.

## The accept predicate and the halo2 correspondence

The definitions you must read to interpret the statements:

* **The accept predicate.** The whole verifier collapses to one MSM; it accepts
  exactly when that MSM is the identity. `DeployedAccepts` is that predicate;
  `assemble?` builds the MSM in the exact order of halo2's `plonk/verifier.rs`.
* **The relation.** `SnarkRelation` is the extraction target: *one* witness $a$
  that both opens the IPA commitment (`IpaRelation`) and satisfies the circuit
  (`circuitSat`). The conclusion of soundness is that such an $a$ exists (or a
  break is exhibited).
* **The correspondence to the Rust verifier.** The fingerprint match
  `fingerprint_matches` is a single `native_decide` check that the Lean
  assembler's MSM equals the Rust verifier's captured MSM — **for the specific
  captured proof and circuit under analysis.** This is what ties the Lean
  `DeployedAccepts` to the deployed verifier's accept. It is a numeric oracle,
  independently re-checkable by another implementation or by hand.

## The trusted surface — what the auditor must personally check

Collecting the boundary in one place. To trust the end-to-end result you must
independently satisfy yourself of each of the following; none is discharged
inside the soundness theorems.

1. **The computational assumptions hold.** Discrete-log relation hardness on
   Vesta, the random-oracle idealization of Blake2b and challenge conversion
   (and hash-to-curve for the URS), and the AGM for the computed reduction.
2. **The `native_decide` oracles are correct.** The fingerprint match
   `fingerprint_matches` and CompElliptic's Vesta point-count. Both are closed,
   re-checkable numeric facts; a miscompiled or buggy oracle would be caught by
   an independent recomputation disagreeing. The
   [trust discipline](../formal-verification.md#trust-discipline) pins them at
   build time via `assert_no_sorry` and a `#guard_msgs`-frozen `#print axioms`.
3. **Verifying-key correctness (input side).** That the `VerifyingKey` fed to
   the verifier encodes the *real* deployed circuit — gate polynomials, query
   layouts, fixed/permutation commitments. Outside Lean; not started.
4. **Semantic adequacy (output side).** That gate satisfaction (`SnarkRelation`)
   actually encodes a *valid Orchard action* — a well-formed note, balanced
   value, a correctly derived nullifier, an authorized spend. In the theorems
   this is the free proposition `S` reached through the assumed `hencodes`; the
   chain stops at "the extracted witness satisfies the gates." Instantiating `S`
   to the concrete statement and proving `hencodes` is the output-side dual of
   item 3. Outside Lean; not started.
5. **The open in-Lean hypotheses the capstones still carry.** The multiopen
   *decode binding* — tying the decoded columns back to the committed columns via
   `batch_open_soundV` — is proven but not yet wired into the constraint capstone,
   so the constraint side is not yet closed end-to-end. Alongside it the priced
   structural residuals ($z \neq 0$, $g_0 \neq 0$, the $S$-opening
   $\text{commit}\,s = \text{ipaS}$, value recovery $\xi\cdot\langle s,b\rangle = 0$)
   and the accept-probability / good-challenge hypotheses (`hprob`, `hquot`,
   `hgood`) are assumed in-Lean and priced rather than discharged. The
   [glossary](glossary.md) itemizes each (its *Capstones & hypotheses* group)
   with its Lean anchor.
6. **Reduction efficiency.** That the reductions are efficient (argued by
   inspection) and that the missing field-independent polynomial extractor bound
   does not hide a super-polynomial cost.

Items 1–2 are the intended trusted base — the assumptions and re-checkable
oracles a mechanized proof is *meant* to rest on. Items 3–6 are the currently
open surface: the gaps between "the extracted witness satisfies the gates over
Vesta" and "the deployed Orchard/Ironwood verifier is sound for real
transactions." Reading them off in full is exactly the check this page exists to
enable.
