# Ledger Security Games

The [proof map](proof-map.md) traces *verifier knowledge soundness* — the deployed Halo 2 verifier
under `Zcash/Snark/`. This page is its companion for the other half of the development: the
protocol **security properties** under `Zcash/Security/`. It covers:
* the top-level capstones — the *ledger-model security games* of *Balance integrity*, *Spendability*, and *Spend authority*;
* how each capstone connects, by reduction via intermediate security properties such as
  *binding-signature balance* and *key binding*, to an exhibited break of a cryptographic
  primitive in a specified adversary model — and where the intended hand-off to *verifier
  knowledge soundness* remains open.

Every argument here follows the *breaks as computed data* convention and the layered
stack described in [Security Models](security-models.md).

## One picture, not yet connected

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 20, "rankSpacing": 50, "padding": 6, "diagramPadding": 4, "subGraphTitleMargin": {"top": 4, "bottom": 18}}, "themeCSS": ".cluster-label { font-weight: 700; font-size: 1.12em; font-family: raleway, sans-serif; } marker { overflow: visible !important; } marker path { transform-box: fill-box !important; transform-origin: center !important; transform: scale(1.25) !important; }"}}%%
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

  subgraph TARGETS["Main target problems"]
    NDLR{{"<span style='display:block; height:0.5em'></span>NontrivialRelation<br/>  (<span class='katex'><span class='mord mathcal'>V</span></span>, <span class='katex'><span class='mord mathcal'>R</span></span>)<br/>  discrete-log relation  <br/>(Pallas)<span style='display:block; height:0.5em'></span>"}}
    SDLR{{"<span style='display:block; height:0.5em'></span>Sinsemilla<br/>discrete-log relation<br/>(Pallas)<span style='display:block; height:0.5em'></span>"}}
    VDLR{{"<span style='display:block; height:0.5em'></span>URS<br/>discrete-log relation<br/>(Vesta)<span style='display:block; height:0.5em'></span>"}}
    SADLR{{"<span style='display:block; height:0.3em'></span>Spend-auth<br/>discrete-log relation<br/>(Pallas, base +<br/>sampled keys)<span style='display:block; height:0.3em'></span>"}}
  end

  subgraph LAYER2["DLR → Discrete log"]
    DL{{"<span style='display:block; height:0.8em'></span>DLR → Discrete log<br/>in the AGM+RO<span style='display:block; height:0.8em'></span>"}}
  end

  BS -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/Balance.lean'>non-balancing<br/>bundle computes</a>"| NDLR
  BS -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionArm.lean'>verifying signature<br/>the extractor misses</a>"| KERR["RedDSA<br/>extractability"]
  BS --> STMT["Witness or replay<br/>evidence<br/>ActionSatisfied<br/>§4.17.4"]
  NCB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean'>wrong note<br/>opening computes</a>"| NCBK["NoteCommitBreak"]
  NCB --> STMT
  MERK --> STMT
  MERK --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Merkle.lean'>wrong Merkle<br/>path computes</a>"| MC["DefinedCollision<br/>one height,<br/>encoding domain"]
  KB --> STMT
  KB -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/KeyBindingDLR.lean'>Orchard-protocol<br/>CommitIvkCollision<br/>computes</a>"| SDLR
  KB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/KeyBinding/Basic.lean'>conflicting ivk<br/>witnesses compute</a>"| CUS{{"<span style='display:block; height:0.5em'></span>CollisionUpToSign<br/>shifted oracle,<br/>distinct queries<span style='display:block; height:0.5em'></span>"}}
  NFB --> STMT
  NFB -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean'>distinct derive-inputs +<br/>equal nullifier<br/>computes</a>"| NFC["NullifierCollision"]
  SPENDAUTH -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SpendAuthority.lean'>verified signature over<br/>unsigned sighash computes</a>"| SAF["SpendAuthForgery<br/>(randomization<br/>of ±ak)"]

  STMT STMTtoKS@-. "<a target='_blank' href='https://github.com/zcash/ironwood/issues/147'>intended hand-off:<br/>not yet formalized<br/>(#147, #155)</a>" .-> KS["Knowledge soundness:<br/>accepting proof yields<br/>witness or break data"]
  NCBK --> SDLR

  KERR KERRtoNDLR@==>|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/RedDSA/Extraction.lean'>good challenge<br/>computes</a>"| NDLR
  NDLR L2N@-.->|"programmed bases +<br/>group-hash<br/>indifferentiability"| DL
  SDLR L2S@-.->|"programmed bases +<br/>group-hash<br/>indifferentiability"| DL
  VDLR L2V@-.->|"programmed bases +<br/>group-hash<br/>indifferentiability"| DL
  SADLR L2K@-.->|"programmed bases +<br/>group-hash<br/>indifferentiability"| DL
  KS KStoVDLR@==>|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Action/AdaptiveStatementKnowledge.lean'>extraction failure<br/>computes URS relation</a>"| VDLR
  MC --> SDLR
  NFC -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Nullifier.lean'>distinct-note openings<br/>compute</a>"| SDLR
  SAF ---> RDSA["RedDSA unforgeability,<br/>±-randomized keys"]
  RDSA RDSAtoSADLR@==>|"re-rand reduction<br/><a target='_blank' href='https://eprint.iacr.org/2015/395'>[FKMSSS2016]</a> +<br/><a target='_blank' href='https://eprint.iacr.org/2019/877'>straight-line AGM extraction</a>"| SADLR

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
  click VDLR "https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/AGM/Adapter.lean" _blank
  click KS "https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Relation/KnowledgeSoundness.lean" _blank
  click DL "https://github.com/zcash/ironwood/blob/main/Zcash/Common/RelationProbability.lean" _blank
  click KERR "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionKnowledgeError.lean" _blank
  click RDSA "https://github.com/zcash/ironwood/issues/121" _blank

  classDef proven fill:#1a7f37,stroke:#116329,color:#ffffff
  classDef checked fill:#0969da,stroke:#0550ae,color:#ffffff
  classDef partial fill:#9a6700,stroke:#7d4e00,color:#ffffff
  classDef hyp fill:#a41826,stroke:#82071e,color:#ffffff
  class BAL,SPEND,SPENDAUTH,KS,DL partial
  class NCB,BS,KB,MERK,NFB,STMT,NDLR,CUS,NCBK,MC,NFC,SAF,SDLR,VDLR,KERR checked
  class RDSA,SADLR hyp
  classDef agmEdge stroke:#8858c8,stroke-width:4.2px
  classDef gapEdge stroke:#a41826,stroke-width:3.5px,stroke-dasharray: 7.5 3.2
  classDef l2Edge stroke-width:1.6px,stroke-dasharray: 5 4
  class KERRtoNDLR,KStoVDLR,RDSAtoSADLR agmEdge
  class STMTtoKS gapEdge
  class L2N,L2S,L2V,L2K l2Edge
```

<p>
<span style="color:#8858c8; font-weight: 700; font-size: 1.9rem">➞</span> Heavy purple edge: a reduction (or intended reduction) in the AGM+RO — the adversary is <a href="security-models.html#the-algebraic-adversary-restriction">algebraic</a> and the challenge oracle is a random oracle that the reduction may program.<br/>
<span style="color:#a41826; font-weight: 700; font-size: 1.9rem">⇢</span> Dashed red edge: an intended hand-off that is not yet formalized — the endpoints share no definition. (<a href="https://github.com/zcash/ironwood/issues/147">#147</a>, <a href="https://github.com/zcash/ironwood/issues/155">#155</a>)<br/>
<span style="font-size: 1.9rem">➝</span> Thin edge: depends on (a reduction, assumption, or model).<br/>
<span style="font-size: 1.9rem">⇢</span> Thin dashed edge into the "DLR → Discrete log" layer: the optional conversion from a nontrivial discrete-log relation to a plain discrete log. Programmed bases (Jaeger–Tessaro),
<a href="group-hash-indifferentiability.html">group-hash indifferentiability</a>, and the
<a href="group-hash-indifferentiability.html#the-first-ingredient-regularity">Weil bound</a> are used
here, and nothing outside that box depends on them.<br/>
<span style='display:block; height:0.5em'></span>
<span style="color:#1a7f37; font-size: 2rem"> ■ </span> Fully proven — nothing here yet.<br/>
<span style="color:#0969da; font-size: 2rem"> ■ </span> Stated and machine-checked in Lean, over abstract primitives.<br/>
<span style="color:#9a6700; font-size: 2rem"> ■ </span> Partly machine-checked. The remainder is tracked: discharging the capstones' named ε's end to end (composing the per-arm oracle-model discharges into one experiment); RedDSA unforgeability; knowledge soundness's circuit-correctness conditions; assembling the DLR → DL conversion from its machine-checked halves (Jaeger–Tessaro programmed bases; group-hash indifferentiability under the named Weil hypothesis).<br/>
<span style="color:#a41826; font-size: 2rem"> ■ </span> Named hypothesis; formalization deferred.<br/>
</p>

## What the Balance capstones assume

The Balance capstones are stated for a *Knowledge-Soundness-idealized* adversary
([`IdealizedKSBalanceAdversary`](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/OrchardIntegrityExperiment.lean)):
one that outputs a witness-annotated ledger, every Action carrying the witness for the
Action statement. The annotation is where knowledge soundness of the Action circuit enters:
nothing yet connects an accepting Halo 2 proof to those witnesses, so the `idealizedks` in
the capstones' names marks results that are complete over this idealized ledger model but
not yet composed with the circuit layer. That composition is the dashed red edge above
([#147](https://github.com/zcash/ironwood/issues/147)); until it lands, the Balance
integrity node stays amber even though every ledger-side arm is machine-checked. This is an
incompleteness of the proof, not an accepted modelling trade-off. The capstones' accepted
trade-offs —the binding challenge hash as a random oracle and elided byte encodings— are
documented at `IdealizedKSBalanceAdversary.violationEvent`. The value and binding bases
are the deployed ones: the conservation arm's target is a discrete-log relation over
those bases, not reprogrammed stand-ins for them.

This picture is a deliberate approximation, and is likely to change as the formalization
proceeds. The "RedDSA unforgeability" node is a named hypothesis rather than a terminal
assumption: its discharge edge names the reduction for security of signatures with
re-randomizable keys
([Efficient Unlinkable Sanitizable Signatures from Signatures with Re-Randomizable Keys](https://eprint.iacr.org/2015/395),
section 3), adapted to the ±-randomized variant, together with the same straight-line
AGM+ROM extraction of Fuchsbauer–Plouviez–Seurin
([Blind Schnorr Signatures and Signed ElGamal Encryption in the Algebraic Group Model](https://eprint.iacr.org/2019/877),
Theorem 1) that discharges the "RedDSA extractability" node at
$(q_H + 2)/\FieldSize + \varepsilon_{\mathrm{DLR}}$, where $\varepsilon_{\mathrm{DLR}}$
is the advantage against the $(\mathcal{V}, \mathcal{R})$ relation. The planned
discharge is to simulate
the signing oracle by programming the challenge oracle at the re-randomized key; the
randomizer, carried by the forgery, enters the extraction as a known coefficient. This
differs from the "RedDSA extractability" node in that the latter has no signing oracle to
simulate, because the signature extracted from is the adversary's own.

Every solid arrow reads "rests on"; where an edge carries a label, the label names the
computed break object flowing along it. Heavy purple arrows mark reductions (or intended
reductions) in the AGM+RO: both the source and the target of such an edge are interpreted
as games against online-AGM adversaries with the challenge oracle as a programmable
random oracle, so the model scopes the whole reduction rather than being one more
assumption it rests on — see
[Security Models](security-models.md#the-algebraic-adversary-restriction).

The "<span class='raleway'>Main target problems</span>" cluster is where the
protocol-specific reductions stop: per-curve discrete-log relations at the deployed
fixed bases, with the sampled spend-authorization keys joining the basis for Spend
authority. The reasons for splitting the "DLR → Discrete log" conversion into a separate
layer are covered [on the Security Models page](security-models.md#the-layered-organization).

The `CollisionUpToSign` arm is terminal without any assumption — its bound is the
birthday count over the oracle table, a pure counting argument. It is the one purely
random-oracle reduction on this page, and it belongs to the ZIP 2005 recovery analysis
rather than the pre-quantum story. The games are the top-level capstones.

As stated above, the KS-idealized ledger model requires the adversary to supply, along
with any accepting proof, a **witness or replay evidence** for the Action statement
(`ActionSatisfied`) — in the replay case the ledger oracle can produce the previously
supplied witness. Each component argument consumes the statement's satisfaction
*on that witness*. Knowledge soundness is what is *intended* to justify that modelling:
whenever the ledger layer needs a witness, the extractor would compute one —or compute
break data— from the accepting proof. That hand-off is not yet formalized in any form:
the games state `ActionSatisfied` over their own abstract types, and no definition is
shared with the SNARK development. The dashed red edge marks exactly this gap
([#147](https://github.com/zcash/ironwood/issues/147),
[#155](https://github.com/zcash/ironwood/issues/155)). Until it lands, the
witness-supply requirement is a modelling assumption of the ledger games, not a
consequence of verifier knowledge soundness.

<style>
/* "One picture, not yet connected" links: labels keep their ordinary colour at rest
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
</style>

New to the shorthand? See the [**Definitions**](definitions.md). &nbsp;·&nbsp; For the methodology, [**Security Models**](security-models.md). &nbsp;·&nbsp; For the verifier-soundness half, the [**Proof Map**](proof-map.md).
