# Assumption Register

Every assumption the Action knowledge-soundness result rests on, in one place. The pages this
links to explain each at length; what this page adds is the *inventory* — so a reader can count
them, and can tell at a glance which kind each one is.

The register is sorted into three tiers, because the tiers fail differently and only one of them
can ever shrink:

- **Tier 1 — terminal model assumptions.** Intentional, permanent, and standard for a result of
  this kind. They are not unfinished Lean obligations, and no future work discharges them. What
  changes over time is the community's confidence in them, not their status here.
- **Tier 2 — concrete deployment bindings.** Identifications between a Lean object and a shipped
  artifact. Each *could* in principle be closed by further formalization, but none is a
  cryptographic assumption: they are questions of "is this the same bytes / the same
  distribution".
- **Tier 3 — tracked residuals.** Engineering and proof work that is genuinely incomplete. Each
  has a tracker.

A reader who accepts tiers 1 and 2 and is satisfied with the tier-3 status has accepted the
result. The [Guide to the Theorems](theorem-guide.md) is the entry point; the
[Knowledge-Soundness Contract](knowledge-contract.md) reads the capstone itself.

## Tier 1 — terminal model assumptions

| Assumption | What fails if it is false | Where it is discussed |
| --- | --- | --- |
| **Vesta discrete-log hardness.** No adversary within the covered resource envelope achieves a meaningful advantage at computing discrete logs on Vesta. Note the framing: this is *not* a premiss of any theorem. The theorems are generic in an advantage function and exhibit an explicit relation finder; you supply the judgement about what that finder can achieve. | Everything. A single discrete-log computation against the fixed bases breaks binding and knowledge soundness for the whole protocol at once — not per transaction, not per user. | [Security Models](security-models.md#what-a-reduction-in-these-models-says) |
| **The online algebraic-group model.** Every group element the adversary outputs carries a representation over the elements it has received. This is part of the adversary's *type*, not a named hypothesis — which makes it easy to miss when reading a theorem statement. | Adversaries that are not algebraic are outside the claim entirely. The extractor reads its witness off the representations; with no representation there is nothing to read. | [Security Models](security-models.md#the-algebraic-adversary-restriction) |
| **Blake2b as a random oracle.** The deployed verifier derives each challenge by hashing the transcript with Blake2b. The development models that as a uniform random oracle. Nothing in Lean argues the two agree. | The Fiat–Shamir step. Interactive soundness would no longer carry to the deployed non-interactive check, and the pinned-root and Schwartz–Zippel budgets would lose their meaning. | [Modelling boundaries](../formal-verification.md#modelling-boundaries) |
| **The fixed-URS / hash-to-curve heuristic.** Security is proved for the family of protocols that *sample* the reference string; the deployed protocol *fixes* it by hashing public strings to the curve. No Lean theorem instantiates the endpoints at the deployed bases. | The transfer of every bound to the deployed system. The known caveat is sharp: an adversary has the protocol's entire lifetime to attack one fixed reference string, and the cost amortizes over every transaction ever made against it. | [Security Models](security-models.md#fixed-bases-hash-to-curve-and-the-reference-string) |

## Tier 2 — concrete deployment bindings

| Binding | What fails if it is false | Status |
| --- | --- | --- |
| **Transcript and verifying-key byte encoding.** The captures and ε theorems support a typed, post-decoding boundary between the Rust and Lean verifiers — not universal byte-level refinement. Byte encoding, transcript domain-prefix bytes, and Blake2b itself remain external. | The identification of the Lean verifier with the shipped one. The soundness argument would still hold of the Lean model, but would no longer be about the deployed verifier. | Tracked — [#66](https://github.com/zcash/ironwood/issues/66) |
| **The challenge conversion.** halo2 draws a challenge by reducing 64 hash bytes to a field element; the theorems draw one exactly uniform. The two are not definitionally equal, and the gap is carried explicitly as a one-sided statistical-distance premiss rather than being assumed away. | Every challenge-surface budget shifts by the bias. The endpoints already expose the transport, so a quantified bias can be substituted rather than invalidating the statement. | Explicit in the endpoint conclusion (`PMFEventBiasLE`) |
| **The verifying key is Orchard's.** Lean derives the verifying key from the ported circuit and checks it against a release-regenerated capture. Identifying that capture with Orchard's canonical deployed artifact and byte serialization is external. | The result would be about a circuit that is not the deployed one — the input-side mirror of the ledger gap in tier 3. | Key-granularity anchoring in place; serialization external |
| **The circuit-side layout fixtures.** The CS and layout dumps behind the `CircuitCheck` comparisons were emitted by one-off instrumentation that was never published, so unlike the verifier-fingerprint captures they have no regenerate-and-diff pipeline. CI pins their bytes, and those pins live in the repository they guard. | Row-level layout content below the verifying key, and the base-circuit dump — which has no capture-side anchor at all — would be wrong with no check to catch it. | Pinned plus review; regeneration from released sources is recorded as follow-up |

## Tier 3 — tracked residuals

| Residual | What fails if it is false | Tracker / status |
| --- | --- | --- |
| **Staging fidelity of the costed programs.** The group-work accounting language reifies only the operations a program writes as nodes; work performed inside an unreified host callback goes uncharged. The judgement that no such work exists is a named premiss carried into the endpoints — and re-exported as a conclusion conjunct — rather than a theorem. | The resource accounting, and with it the meaning of the coverage numbers. The bound would still hold, but at counts the theorem no longer certifies. | `StagedGroupWorkFaithful`; a deep embedding would discharge it, at the cost of rewriting the reduction in that syntax |
| **The three-decode representation-length invariant.** The direct-decode bound follows from a required family representation-length cap. The generic development does not construct a concrete deployed family satisfying it. | The direct-decode term of the bound. A deployed family exceeding the cap would not be covered by the instantiated endpoints. | Open — no concrete deployment instance constructed |
| **Circuit-to-ledger composition.** The capstone ends at the deployed Action circuit's private witnesses. Carrying those into the abstract Orchard ledger relation crosses named circuit-correctness side conditions rather than a proved implication. | The step from "the extracted witness satisfies the deployed circuit" to "this is a legitimate transaction". This is the largest remaining gap, and it is on the output side. | `TopLevelCircuitCorrectness`; subject of the circuit soundness proof |
| **Hash-to-curve is not adversary-queryable.** A realistic adversary can evaluate the group hash on inputs of its choice, obtaining group elements it holds with no representation — so it is not algebraic over any fixed finite basis. Each game instead fixes an enumerated basis. | Games whose honest parties themselves derive bases — spendability and spend authority — cannot express strategies a real adversary performs routinely, so their capstones do not yet carry their intended weight. | [#188](https://github.com/zcash/ironwood/issues/188) |
| **RedDSA ±-randomized unforgeability.** A named hypothesis on the ledger side rather than a terminal assumption: its intended discharge route is named, but not formalized. | The spend-authority capstone's forgery arm. | [#121](https://github.com/zcash/ironwood/issues/121) |
| **Binding-signature glue.** The remaining composition of the per-arm oracle-model discharges into one experiment, and the games' named ε hypotheses. | The end-to-end ledger capstones would remain conditional on ε's that are named but not discharged. | [#107](https://github.com/zcash/ironwood/issues/107) |

## What is *not* on this list

**Compiler trust** is not an assumption in the above sense — it is a property of *how* certain
closed facts are checked, and it is enforced at build time rather than accepted by the reader.
The curve point-count and the captured fingerprint matches are discharged by running compiled
code, each adding a recorded axiom, and each is independently re-checkable by another
implementation. See the [trust discipline](../formal-verification.md#trust-discipline).

**Completeness** is not an assumption but an absent claim. Nothing here says an honest prover's
proof extracts, or that any run accepts at all.
