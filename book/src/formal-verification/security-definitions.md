# Security Definitions

The [proof map](proof-map.md) traces *verifier soundness* — the deployed Halo 2 verifier
under `Zcash/Snark/`. This page is its companion for the other half of the development: the
protocol **security properties** under `Zcash/Security/` — binding-signature *balance*, *key
binding*, and the *ledger-model security games* — and how each one connects, by reduction,
to a primitive hardness assumption and to the verifier-soundness proof.

Every argument here has the same shape, the development-wide
[*breaks as computed data*](../formal-verification.md#breaks-as-computed-data) convention:

> A security property, if violated, **exhibits** a concrete break of an underlying
> primitive — a discrete-log relation, a hash collision, a commitment-opening collision —
> computed as data. Hardness is assumed only at the computational layer, against the
> exhibited break.

So each definition sits on a three-layer stack:

- **Layer A — vocabulary.** The break events, as structures carrying their data
  (`RandomOracle.Collision`, `NontrivialRelation`, `NoteCommitBreak`). Deterministic; no
  probability.
- **Layer B — reduction.** A computable `def` that turns a property violation into a
  Layer-A break (`NontrivialRelation.ofImbalance`, `Merkle.collisionOfWrongLeaf`,
  `noteCommitBreakOfNe`). Deterministic; no hardness assumption.
- **Layer C — probability.** The bound that producing the break is hard: the birthday bound
  `q(q-1)/|𝔽|`, or the discrete-log advantage. The only layer that consumes an assumption.

## One connected picture

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 20, "rankSpacing": 50, "padding": 6, "diagramPadding": 4, "subGraphTitleMargin": {"top": 4, "bottom": 18}}, "themeCSS": ".cluster-label { font-weight: 700; font-size: 1.1em; font-family: raleway, sans-serif; }"}}%%
flowchart TD
  subgraph GAMES["Ledger capstones"]
    BAL["Balance integrity<br/>orchardBalanceIntegrity_measure_le"]
    SPEND["Spendability<br/>faerieGoldCore<br/>validLedger_append"]
    SPENDAUTH["Spend authority<br/>orchardSpendAuthority_measure_le"]
  end

  BAL --> BS["Binding-signature<br/>balance"]
  BAL --> NCB["Note-commitment<br/>binding"]
  BAL --> MERK["Merkle-path<br/>binding"]
  BAL --> KB["Key binding<br/>ZIP 2005"]
  SPEND --> BAL
  SPEND ---> NCB
  SPEND ---> MERK
  SPEND ---> KB
  SPEND ---> NFB["Nullifier binding"]
  SPEND ---> SPENDAUTH
  SPENDAUTH --> KB

  subgraph ASSUMPTIONS["Hardness assumptions"]
    DL[("Discrete log")]
  end

  subgraph MODELS["Heuristic adversary models"]
    ROM[("Random oracle")]
  end

  BS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/Balance.lean'>non-balancing<br/>bundle computes</a>"| NDLR["NontrivialRelation<br/>(<span class='katex'><span class='mord mathcal'>V</span></span>,&nbsp;<span class='katex'><span class='mord mathcal'>R</span></span>) discrete-log<br/>relation"]
  BS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionArm.lean'>verifying signature<br/>the extractor misses</a>"| KERR["RedDSA<br/>extractability"]
  BS --> STMT["Witness or replay<br/>evidence<br/>ActionSatisfied<br/>§4.17.4"]
  NCB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean'>wrong note<br/>opening computes</a>"| NCBK["NoteCommitBreak"]
  NCB --> STMT
  MERK --> STMT
  MERK --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Merkle.lean'>wrong Merkle<br/>path computes</a>"| MC["DefinedCollision<br/>one height,<br/>encoding domain"]
  KB --> STMT
  KB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/KeyBindingDLR.lean'>Orchard-protocol<br/>CommitIvkCollision<br/>computes</a>"| SDLR
  KB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/KeyBinding/Basic.lean'>conflicting ivk<br/>witnesses compute</a>"| CUS["CollisionUpToSign<br/>shifted oracle,<br/>distinct queries"]
  NFB --> STMT
  NFB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean'>distinct derive-inputs +<br/>equal nullifier<br/>computes</a>"| NFC["NullifierCollision"]
  SPENDAUTH --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SpendAuthority.lean'>verified signature over<br/>unsigned sighash computes</a>"| SAF["SpendAuthForgery<br/>(randomization<br/>of ±ak)"]

  STMT -. "<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Composition/Bridge.lean'>justified by<br/>the extractor;<br/>circuit-correctness<br/>conditions</a>" .-> KS["Knowledge soundness:<br/>accepting proof yields<br/>witness or break data"]
  NCBK --> SDLR["Sinsemilla<br/>discrete-log<br/>relation"]

  KERR -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/RedDSA/Extraction.lean'>good challenge<br/>computes</a>"| NDLR
  KERR --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/RedDSA/KnowledgeError.lean'>challenge hash as random<br/>oracle; query-time labels<br/>pin the bad challenge (AGM)</a>"| ROM
  NDLR -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/DiscreteLog.lean'>independent<br/>hash-to-curve bases</a>"| DL
  SDLR -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/DiscreteLog.lean'>independent<br/>hash-to-curve bases</a>"| DL
  KS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Action/AdaptiveStatementKnowledge.lean'>online AGM +<br/>independent<br/>hash-to-curve bases</a>"| DL
  KS -->|"<a target='_blank' href='https://github.com/zcash/ironwood/tree/main/Zcash/Snark/Soundness/FiatShamir'>Fiat–Shamir<br/>heuristic</a>"| ROM
  MC --> SDLR
  CUS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Common/Birthday.lean'>birthday counting<br/>q(q-1)/|𝔽|,<br/>no assumption</a>"| ROM
  NFC -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Nullifier.lean'>distinct-note openings<br/>compute</a>"| SDLR
  SAF ---> RDSA["RedDSA unforgeability,<br/>±-randomized keys"]
  RDSA -->|"re-rand reduction<br/><a target='_blank' href='https://eprint.iacr.org/2015/395'>[FKMSSS2016]</a> +<br/>forking extraction"| DL
  RDSA -->|"challenge hash<br/>as random oracle"| ROM

  click BAL "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Balance.lean" _blank
  click SPEND "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean" _blank
  click SPENDAUTH "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SpendAuthority.lean" _blank
  click BS "https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/Balance.lean" _blank
  click NCB "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean" _blank
  click MERK "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Merkle.lean" _blank
  click KB "https://github.com/zcash/ironwood/blob/main/Zcash/Security/KeyBinding/Basic.lean" _blank
  click NFB "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean" _blank
  click STMT "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean" _blank
  click NCBK "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean" _blank
  click MC "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Merkle.lean" _blank
  click CUS "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Common/RandomOracle.lean" _blank
  click NFC "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean" _blank
  click SAF "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SpendAuthority.lean" _blank
  click NDLR "https://github.com/zcash/ironwood/blob/main/Zcash/Common/DiscreteLogRelation.lean" _blank
  click SDLR "https://github.com/zcash/ironwood/blob/main/Zcash/Common/DiscreteLogRelation.lean" _blank
  click KS "https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Relation/KnowledgeSoundness.lean" _blank
  click DL "https://github.com/zcash/ironwood/blob/main/Zcash/Common/DiscreteLogRelation.lean" _blank
  click ROM "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Common/RandomOracle.lean" _blank
  click KERR "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionKappaArm.lean" _blank
  click RDSA "https://github.com/zcash/ironwood/issues/121" _blank

  classDef proven fill:#1a7f37,stroke:#116329,color:#ffffff
  classDef checked fill:#0969da,stroke:#0550ae,color:#ffffff
  classDef partial fill:#9a6700,stroke:#7d4e00,color:#ffffff
  classDef hyp fill:#cf222e,stroke:#a40e26,color:#ffffff
  classDef assumed fill:#57606a,stroke:#424a53,color:#ffffff
  class BAL,SPEND,SPENDAUTH,KS partial
  class NCB,BS,KB,MERK,NFB,STMT,NDLR,CUS,NCBK,MC,NFC,SAF,SDLR,KERR checked
  class RDSA hyp
  class DL,ROM assumed
```

<p>
<span style="color:#1a7f37">■</span> fully proven — nothing here yet<br/>
<span style="color:#0969da">■</span> stated and machine-checked in Lean, over abstract primitives<br/>
<span style="color:#9a6700">■</span> partly machine-checked; remainder tracked (discharging the capstones' named ε's end to end: composing the per-arm oracle-model discharges into one experiment, RedDSA unforgeability; knowledge soundness's circuit-correctness conditions)<br/>
<span style="color:#cf222e">■</span> named hypothesis; formalization deferred<br/>
<span style="color:#57606a">■</span> assumption or heuristic model; terminal by design
</p>

This picture is a deliberate approximation, and is likely to change as the formalization
proceeds. The RedDSA node is a named hypothesis rather than a terminal assumption: its
discharge edge names the reduction for security of signatures with re-randomizable keys
[<a href="https://eprint.iacr.org/2015/395">FKMSSS2016</a>, section 3], adapted to the
±-randomized variant, together with forking extraction of the Schnorr witness. The
binding-signature extractability node, by contrast, is discharged via the straight-line
AGM+ROM extraction of Fuchsbauer–Plouviez–Seurin
[<a href="https://eprint.iacr.org/2019/877">2019/877</a>, Theorem 1], at
$(q_H + 2)/|\mathbb{F}| + \varepsilon_{\mathrm{DL}}$. In that setting there is
no signing oracle to simulate, because the signature extracted from is the adversary's
own.

Every solid arrow reads "rests on"; where an edge carries a label, the label names the
computed break object flowing along it, or the adversary model or side condition under which
the reduction holds (the AGM restriction, base independence from hash-to-curve, the birthday
count). The games are the top-level capstones. The ledger model requires the adversary to
supply, along with any accepting proof, a **witness or replay evidence** for the Action
statement (`ActionSatisfied`) — in the replay case the ledger oracle can produce the
previously supplied witness. Each component argument consumes the statement's satisfaction
*on that witness*. Knowledge soundness is what justifies the modelling: whenever the ledger
layer needs a witness, the extractor computes one —or computes break data— from the accepting
proof. The dashed edge marks that justification, which crosses the remaining semantic bridge:
the Clean/Ironwood circuit-correctness conditions (`TopLevelCircuitCorrectness`) — named
component conditions rather than a proved implication. Discharging them is the subject of
the circuit soundness proof.

## Fixed bases and the reference-string heuristic

Several reductions above bottom out at discrete log by treating a set of group elements as
*independent* — for example the value-commitment bases $\mathcal{V}$ and $\mathcal{R}$, the
Sinsemilla generators, and the proof system's inner-product reference string. Independence
is what turns "find a nontrivial relation among these elements" into the discrete-log game:
the reduction models each base as a random multiple of one generator and embeds its
discrete-log challenge into that randomness.

In the deployed protocol, though, these bases are *fixed*. Each is produced once, by
hashing public strings to the curve, and the resulting outputs are baked into the protocol
as a Uniform Reference String. The gap between the two is the standard gap for protocols
with a URS. We prove security for the family of protocols that sample the bases at
random, over the distribution of that randomness. Then we argue heuristically that the
deployed protocol, which fixes them via hash-to-curve, inherits it — provided that the
hash-to-curve scheme admits no attack more efficient than the generic ones bounded by the
proven reductions. The same heuristic underlies every use of hash-to-curve for fixed bases
here, of which the value and note commitments, the Merkle hash, and the proof system's
reference string are examples.

This heuristic comes with an important caveat: an adversary has the protocol's *entire
lifetime* to attack that one specific reference string. A bound that holds for random
bases does not preclude an attack tuned to the deployed bases, and the cost of finding
one is amortized over every transaction ever made against them. That is a known,
acknowledged limitation of this development.

This sharpens the potential threat from quantum computers or other discrete-log attacks:
a single discrete-log computation is catastrophic to the protocol as a whole, rather than
localized to a specific user or key. Against these fixed bases, **one** discrete-log
computation is sufficient to break binding/knowledge-soundness properties for the
entire protocol, not just for a single transaction or user. That includes Balance
properties, Spendability, and Spend authority, although not privacy. Migrating away
from reliance on discrete-log binding/knowledge-soundness is therefore a whole-protocol
concern, not a per-transaction one. See
[ZIP 2005](https://zips.z.cash/zip-2005#effectsofdiscrete-logarithm-breakingattacksbeforetheswitchtotherecoveryprotocol)
for further discussion.

## The definitions

<style>
/* "One connected picture" links: labels keep their ordinary colour at rest
   (blue is reserved for the status coding); hover underlines. */
.mermaid .edgeLabel a { color: inherit; }
.mermaid .edgeLabel a:hover,
.mermaid a:hover .nodeLabel {
  /* The SVG is scaled down to fit the page, so the default (~1px) underline
     can fall below one device pixel and drop out on some line boxes; an
     em-based thickness scales with the text instead. */
  text-decoration: underline;
  text-decoration-thickness: 0.12em;
  text-underline-offset: 0.12em;
}
.iw-glossary { margin: 1.3rem 0; display: grid; gap: 26px; }
.iw-glossary section { display: grid; gap: 9px; }
.iw-glossary .grp {
  font-size: .92rem; font-weight: 700; text-transform: uppercase;
  letter-spacing: .06em; opacity: .78; margin: 0;
}
.iw-glossary .g {
  border: 1px solid var(--table-border-color, rgba(128,140,170,.28));
  border-left: 3px solid var(--links, #0e8fa3);
  border-radius: 8px; padding: 9px 13px;
  background: var(--quote-bg, rgba(128,140,170,.05));
}
.iw-glossary .g-head {
  display: flex; justify-content: space-between; align-items: baseline;
  gap: 6px 16px; flex-wrap: wrap;
}
.iw-glossary .term { font-weight: 650; }
.iw-glossary .term code { font-weight: 650; }
.iw-glossary .anchor {
  font-family: "SFMono-Regular", Consolas, "Liberation Mono", Menlo, monospace;
  font-size: .78em; opacity: .6; white-space: nowrap;
}
.iw-glossary .def { margin-top: 3px; line-height: 1.5; opacity: .9; }
</style>

<div class="iw-glossary">

<section>
<div class="grp">Binding-signature balance — value preservation</div>
<div class="g"><div class="g-head"><span class="term">balance</span><span class="anchor">Security.BindingSignature.Balance</span></div><div class="def">No transaction creates or destroys value (spec §4.13 Sapling / §4.14 Orchard). Value commitments are <code>cv v rcv = v • V + rcv • R</code>; a bundle's binding verification key collects to <code>bvk = A • V + B • R</code> with <code>A</code> the net value imbalance. The property is <em>not</em> "no discrete-log relation between <code>V</code> and <code>R</code> exists" — one always does in a prime-order group — but the reduction below.</div></div>
<div class="g"><div class="g-head"><span class="term">NontrivialRelation</span><span class="anchor">BindingSignature.NontrivialRelation · .ofImbalance</span></div><div class="def">The break, as computed data: a nontrivial <code>F</code>-linear relation between the value base <code>Vbase</code> and randomness base <code>Rbase</code>. <code>ofImbalance</code> (and the bundle forms <code>ofBundleModImbalance</code>, <code>ofOrchardImbalance</code>, <code>ofSaplingImbalance</code>) computes one from a non-balancing verifying bundle, with no cryptographic hypothesis — equivalently the discrete log <code>dlog_Rbase Vbase</code> (<code>imbalance_yields_discrete_log</code>).</div></div>
<div class="g"><div class="g-head"><span class="term">integer no-overflow lift</span><span class="anchor">intBalance_eq_zero_of_lt · orchard_natAbs_lt · sapling_natAbs_lt</span></div><div class="def">Lifts field balance (<code>A = 0</code> in <code>ZMod r</code>) to integer balance: with per-action 64-bit value ranges and a bounded action count, <code>|A| &lt; r</code>, so the residue being zero forces the integer to be zero. Discharged per pool from the value-type subranges.</div></div>
<div class="g"><div class="g-head"><span class="term">reduces to DL</span><span class="anchor">Security.BindingSignature.DiscreteLog</span></div><div class="def">Turns the computed Orchard/Sapling relations into plain discrete-log solutions: <em>if you can unbalance, you can solve DL</em>. DLR and DL are tightly equivalent (Jaeger–Tessaro, <a href="https://eprint.iacr.org/2020/1213">2020/1213</a>, Lemma 3), so this assumes no more than DL hardness, given the independence of the hash-to-curve bases.</div></div>
</section>

<section>
<div class="grp">Key binding — ZIP 2005 theorem (ROM)</div>
<div class="g"><div class="g-head"><span class="term">key binding</span><span class="anchor">Security.KeyBinding.KB</span></div><div class="def">A verifying Recovery-Statement witness pins its key components — <code>ak</code> (up to y-sign), <code>nk</code>, and the <code>qk</code>/<code>sk</code> branch with its key — to <code>ivk</code>, unless a break is exhibited (<a href="https://zips.z.cash/zip-2005#thm-key-binding-rom">ZIP 2005 key-binding theorem</a>). Factors as <code>KB = KBOpening ∧ KBDerivation</code>: the <code>Commit^ivk</code> opening and the derivation constraints.</div></div>
<div class="g"><div class="g-head"><span class="term">commit_scalar_pm</span><span class="anchor">KeyBinding.commit_scalar_pm · OpeningBreak</span></div><div class="def">Algebraic core: two openings of the same <code>Commitivk</code> value force their Pedersen scalars equal or negated. An <code>OpeningBreak</code> (two valid openings differing in the opening data) is the break structure the games layer produces.</div></div>
<div class="g"><div class="g-head"><span class="term">reduces to an RO collision</span><span class="anchor">CollisionUpToSign.ofBreak · Birthday.birthday_closed_form</span></div><div class="def">The reduction computes a <code>±</code>-collision of the <code>rivk</code>-derivation random oracle at distinct derivation queries from a break (Layer B). Producing that collision within <code>q</code> queries is bounded by the birthday bound <code>ε_kb ≤ q(q-1)/|RIVK|</code>, which is <code>q(q-1)/r_ℙ</code> at the intended Pallas instantiation (Layer C).</div></div>
</section>

<section>
<div class="grp">Ledger-model games — the abstract Action statement</div>
<div class="g"><div class="g-head"><span class="term">Action statement satisfied</span><span class="anchor">Security.Ledger.ActionSatisfied</span></div><div class="def">The games-relevant conjuncts of an Orchard-shaped Action statement (spec §4.17.4) over abstract primitives: commitment integrity, Merkle-path validity, nullifier integrity, the key-binding condition, address integrity, value-commitment integrity. This is the interface the games consume, and the target the verifier-soundness proof is meant to deliver.</div></div>
<div class="g"><div class="g-head"><span class="term">pinning lemmas</span><span class="anchor">ivk_pinned · nk_eq_or_break · nf_old_eq_or_break</span></div><div class="def">The deterministic steps of the Balance argument: an address <code>(g_d, pk_d)</code> determines <code>ivk</code> (needs only <code>g_d ≠ 0</code> and torsion-freeness), hence <code>nk</code> is determined up to an exhibited key-binding break, and spends of the same note tuple reveal the same nullifier up to a break.</div></div>
<div class="g"><div class="g-head"><span class="term">NoteCommitBreak</span><span class="anchor">Ledger.NoteCommitBreak · noteCommitBreakOfNe</span></div><div class="def">A note-commitment opening collision, as data. <code>noteCommitBreakOfNe</code> computes one when an <code>extract</code>-equal commitment fails to pin the note tuple <code>(rcm, note)</code>. Prequantumly, note-commitment binding reduces to a Sinsemilla / discrete-log-relation break.</div></div>
<div class="g"><div class="g-head"><span class="term">Merkle position binding</span><span class="anchor">Ledger.Merkle.collisionOfWrongLeaf</span></div><div class="def">Fixed-depth Merkle trees are position-binding up to a hash collision: a validating authentication path for a leaf that is <em>not</em> the committed one, against a defined tree, computes a <code>DefinedCollision</code> of one height’s compression — escaped (⊥) evaluations never count as collisions. The vector-commitment property the Balance and Spendability arguments require of the note-commitment tree. Prequantumly, the Sinsemilla compression’s collision resistance reduces to a discrete-log-relation break (SDLR) — the same terminal as note-commitment binding — so BLAKE2b collision resistance does not enter the pre-quantum Balance argument.</div></div>
</section>

<section>
<div class="grp">Probabilistic capstones · Ledger/Capstone + Ledger/OrchardCapstone</div>
<div class="g"><div class="g-head"><span class="term">Balance integrity</span><span class="anchor">Model.balanceIntegrityOrBreak · balanceIntegrityPerTxViolation</span></div><div class="def">The shielded pool is non-negative and the pools sum to the minted issuance. The deterministic <code>balanceIntegrityOrBreak</code> proves it up to a computed break; the probabilistic violation events mirror its conclusion (the transparent conjunct cannot fail on the valid sample space). The interval consequence <code>pool ∈ [0, issuanceTotal]</code> is weaker, and survives as the separate shielded-balance-cap capstones.</div></div>
<div class="g"><div class="g-head"><span class="term">events as branch preimages</span><span class="anchor">Model.balanceSubsetBreakEvent · txBalanceBreakEvent</span></div><div class="def">An adversary is a <code>PMF</code> over valid annotated ledgers; each event is "the computed reduction lands in this branch on this sample", so no choice is needed to extract break data. Violation events are contained in unions of break events, and each break event's probability is a named ε hypothesis.</div></div>
<div class="g"><div class="g-head"><span class="term">all-prefixes bounds, no factor of k</span><span class="anchor">Model.balanceIntegrity_measure_le · *Before / *UpTo</span></div><div class="def">One ε per shared break event bounds the violation at <em>every</em> prefix below a bound, where a naive union bound would pay <code>k · ε</code>. Prefix-indexed value events are named <code>*Before</code> and step-indexed Balance-subset events <code>*UpTo</code> (EWD 831 half-open ranges, exclusive bound as the parameter); the one step/prefix crossing is confined to <code>_succ</code>-marked lemmas.</div></div>
<div class="g"><div class="g-head"><span class="term">the Orchard single-ε collapse</span><span class="anchor">Bridge.orchardRelationEvent · orchardBalanceIntegrity_measure_le</span></div><div class="def">At the Orchard-protocol bases, every Balance-subset arm's break computes a nontrivial discrete-log relation among the fixed Sinsemilla bases, so one <code>ε_sinsemilladlr</code> replaces the three per-arm ε's — and every prefix lands in the same relation event, so the all-prefixes bounds cost no factor of <code>k</code>. <code>ε_sinsemilladlr</code> reduces tightly to discrete-log hardness (Jaeger–Tessaro, <a href="https://eprint.iacr.org/2020/1213">2020/1213</a> Lemma 3, re-proved as <code>relation_prob_le_of_textbookDL</code>); the witness-level model abstracts away Halo 2 knowledge soundness, a separate, lossy reduction on the different Halo 2 bases. <code>ε_bindsig</code> names the bound on the conservation side; the extractor-plus-knowledge-error forms and the κ discharge below replace it with named bounds further down the reduction (<a href="https://github.com/zcash/ironwood/issues/107">#107</a> tracks the remaining glue).</div></div>
<div class="g"><div class="g-head"><span class="term">the knowledge error κ, discharged</span><span class="anchor">RedDSA.kappaEvent_measure_le · Model.balanceConservation_extractFailArm_measure_le</span></div><div class="def">The binding signature is a signature of knowledge of <code>bsk</code>, the discrete log of <code>bvk</code> base $\mathcal{R}$; the conservation reduction's extraction-failure arm is bounded at $(q_H + 2)/|\mathbb{F}| + \varepsilon_{\mathrm{DL}}$ for any query-bounded algebraic ledger adversary — the straight-line AGM+ROM extraction of Fuchsbauer–Plouviez–Seurin (<a href="https://eprint.iacr.org/2019/877">2019/877</a>, Theorem 1), in the key-only setting — no signing oracle, because the signature extracted from is the adversary's own. Challenge queries carry the adversary's representations as labels the oracle never sees. The representation in effect at the output's query point — the run's first annotation there, or the announced output representation when the run never queried the point — pins the query's one bad challenge before the answer is drawn, and away from it the verification equation computes a relation over the presented basis. The extractor reads the key's $\mathcal{R}$-coefficient off that effective representation, and the reference-string heuristic above carries the random-basis game to the deployed bases.</div></div>
</section>

<section>
<div class="grp">Shared foundation · Zcash/Security/Common</div>
<div class="g"><div class="g-head"><span class="term">collision vocabulary</span><span class="anchor">Security.RandomOracle.Collision · CollisionUpToSign</span></div><div class="def">Layer-A break events for the classical ROM: a <code>Collision</code> is two distinct queries with equal outputs; a <code>CollisionUpToSign</code> (<code>a =± b</code>) is the shape produced by arguments passing through the <code>Extract</code> coordinate extractor, whose fibres are <code>{P, −P}</code>. Key binding bottoms out here, as does the nullifier (Faerie-Gold) argument for the Recovery Statement; the deployed nullifier argument bottoms out in the Sinsemilla discrete-log relation instead.</div></div>
<div class="g"><div class="g-head"><span class="term">birthday bound</span><span class="anchor">Security.Birthday.birthday_closed_form</span></div><div class="def">The Layer-C probability: the shifted <code>±</code>-collision event over <code>q</code> uniform oracle outputs has probability at most <code>q(q-1)/|𝔽|</code>, by union-bounding the per-pair fraction <code>2/|𝔽|</code>. Counted in the random-oracle model with no hardness assumption; proven as a probability statement over the uniform oracle table (#73).</div></div>
</section>

</div>

New to the shorthand? See the [**Glossary**](glossary.md). &nbsp;·&nbsp; For the verifier-soundness half, the [**Proof Map**](proof-map.md).
