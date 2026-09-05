# Ledger Security Games

The [proof map](proof-map.md) traces *verifier knowledge soundness* — the deployed Halo 2 verifier
under `Zcash/Snark/`. This page is its companion for the other half of the development: the
protocol **security properties** under `Zcash/Security/`. It covers:
* the top-level capstones — the *ledger-model security games* of *Balance integrity*
  (`orchardBalanceIntegrityExtraction_measure_le_of_dlogProfiles`), *Spendability*
  (`faerieGoldCore`, `validLedger_append`), and *Spend authority*
  (`orchardSpendAuthority_measure_le`);
* how each capstone connects, by reduction via intermediate security properties such as
  *binding-signature balance* and *key binding*, to an exhibited break of a cryptographic
  primitive in a specified adversary model — and where the intended hand-off to *verifier
  knowledge soundness* remains open.

Every argument here follows the *breaks as computed data* convention and the three-layer
stack described in [Security Models](security-models.md).

## One picture, not yet connected

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 20, "rankSpacing": 50, "padding": 6, "diagramPadding": 4, "subGraphTitleMargin": {"top": 4, "bottom": 18}}, "themeCSS": ".cluster-label { font-weight: 700; font-size: 1.1em; font-family: raleway, sans-serif; } marker { overflow: visible !important; } marker path { transform-box: fill-box !important; transform-origin: center !important; transform: scale(1.25) !important; }"}}%%
flowchart TD
  subgraph GAMES["Ledger capstones"]
    BAL["<span style='display:inline-block; padding:0.2em 0.45em; font-size:1.12em'>Balance integrity</span>"]
    SPEND["<span style='display:inline-block; padding:0.2em 0.45em; font-size:1.12em'>Spendability</span>"]
    SPENDAUTH["<span style='display:inline-block; padding:0.2em 0.45em; font-size:1.12em'>Spend authority</span>"]
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
  SPEND --> SPENDAUTH
  SPENDAUTH --> KB

  subgraph ASSUMPTIONS["Hardness assumptions"]
    DL{{"<span style='display:block; height:0.5em'></span>Discrete log<span style='display:block; height:0.5em'></span>"}}
  end

  BS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/Balance.lean'>non-balancing<br/>bundle computes</a>"| CDLR{{"<span style='display:block; height:0.5em'></span>Nontrivial discrete-log<br/>relation, combined<br/>deployed basis (Pallas)<span style='display:block; height:0.5em'></span>"}}
  BS --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionArm.lean'>verifying signature<br/>the extractor misses</a>"| KERR["RedDSA<br/>extractability"]
  BS --> STMT["Witness or replay<br/>evidence<br/>ActionSatisfied<br/>§4.17.4"]
  NCB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Statement.lean'>wrong note<br/>opening computes</a>"| NCBK["NoteCommitBreak"]
  NCB --> STMT
  MERK --> STMT
  MERK --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Merkle.lean'>wrong Merkle<br/>path computes</a>"| MC["DefinedCollision<br/>one height,<br/>encoding domain"]
  KB --> STMT
  KB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/KeyBindingDLR.lean'>Orchard-protocol<br/>CommitIvkCollision<br/>computes</a>"| CDLR
  KB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/KeyBinding/Basic.lean'>conflicting ivk<br/>witnesses compute</a>"| CUS{{"<span style='display:block; height:0.5em'></span>CollisionUpToSign<br/>shifted oracle,<br/>distinct queries<span style='display:block; height:0.5em'></span>"}}
  NFB --> STMT
  NFB --->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Spendability.lean'>distinct derive-inputs +<br/>equal nullifier<br/>computes</a>"| NFC["NullifierCollision"]
  SPENDAUTH -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SpendAuthority.lean'>verified signature over<br/>unsigned sighash computes</a>"| SAF["SpendAuthForgery<br/>(randomization<br/>of ±ak)"]

  STMT STMTtoKS@-->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/OrchardExtractionExperiment.lean'>Balance: extract<br/>witness-annotated chain<br/>(#155 for the other games)</a>"| KS["Knowledge soundness:<br/>accepting proof yields<br/>witness or break data"]
  NCBK --> CDLR

  KERR KERRtoCDLR@==>|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/RedDSA/Extraction.lean'>good challenge<br/>computes</a>"| CDLR
  CDLR -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/BindingSignature/DiscreteLog.lean'>independent<br/>group-hash bases<br/>(Pallas)</a>"| DL
  KS KStoDL@===>|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Action/AdaptiveStatementKnowledge.lean'>independent<br/>group-hash bases<br/>(Vesta)</a>"| DL
  MC --> CDLR
  NFC -->|"<a target='_blank' href='https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/Nullifier.lean'>distinct-note openings<br/>compute</a>"| CDLR
  SAF ---> RDSA["RedDSA unforgeability,<br/>±-randomized keys"]
  RDSA RDSAtoDL@===>|"re-rand reduction<br/><a target='_blank' href='https://eprint.iacr.org/2015/395'>[FKMSSS2016]</a> +<br/><a target='_blank' href='https://eprint.iacr.org/2019/877'>straight-line AGM extraction</a>"| DL

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
  click CDLR "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SinsemillaDLR.lean" _blank
  click KS "https://github.com/zcash/ironwood/blob/main/Zcash/Snark/Soundness/Relation/KnowledgeSoundness.lean" _blank
  click DL "https://github.com/zcash/ironwood/blob/main/Zcash/Common/DiscreteLogRelation.lean" _blank
  click KERR "https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/ExtractionKnowledgeError.lean" _blank
  click RDSA "https://github.com/zcash/ironwood/issues/121" _blank

  classDef proven fill:#1a7f37,stroke:#116329,color:#ffffff
  classDef checked fill:#0969da,stroke:#0550ae,color:#ffffff
  classDef partial fill:#9a6700,stroke:#7d4e00,color:#ffffff
  classDef hyp fill:#a41826,stroke:#82071e,color:#ffffff
  classDef assumed fill:#57606a,stroke:#424a53,color:#ffffff
  class SPEND,SPENDAUTH partial
  class BAL,NCB,BS,KB,MERK,NFB,STMT,CDLR,CUS,NCBK,MC,NFC,SAF,KERR,KS checked
  class RDSA hyp
  class DL assumed
  classDef agmEdge stroke:#8858c8,stroke-width:4.2px
  class KERRtoCDLR,KStoDL,RDSAtoDL,STMTtoKS agmEdge
```

<p>
<span style="color:#8858c8; font-weight: 700; font-size: 1.9rem">➞</span> heavy purple edge: a reduction (or intended reduction) in the AGM+RO — the adversary is <a href="security-models.html#the-algebraic-adversary-restriction">algebraic</a> and the challenge oracle is a random oracle that the reduction may program<br/>
<span style="font-size: 1.9rem">➝</span> thin edge: depends on (a reduction, assumption, or model)<br/>
<span style="color:#1a7f37"> ■ </span> fully proven — nothing here yet<br/>
<span style="color:#0969da"> ■ </span> stated and machine-checked in Lean, over abstract primitives<br/>
<span style="color:#9a6700"> ■ </span> partly machine-checked; remainder tracked (discharging the capstones' named ε's end to end; the effect of undischarged RedDSA unforgeability on the Spendability and Spend authority goals)<br/>
<span style="color:#a41826"> ■ </span> named hypothesis; formalization deferred<br/>
<span style="color:#57606a"> ■ </span> assumption; terminal by design<br/>
</p>

This picture is a deliberate approximation, and is likely to change as the formalization
proceeds.

## What the Balance capstones assume

The composed Balance capstones are stated for a proof-emitting adversary
([`ExtractionBalanceAdversary`](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/OrchardExtractionExperiment.lean)):
one that outputs a ledger whose Actions carry accepting proofs, with no witnesses
supplied. Knowledge soundness of the Action circuit enters through the extractor:
[`OrchardExtractionExperiment`](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/OrchardExtractionExperiment.lean)
builds a *Knowledge-Soundness-idealized* adversary
([`IdealizedKSBalanceAdversary`](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/OrchardIntegrityExperiment.lean))
—one whose every Action carries the witness for the Action statement— by annotating the
chain with the witnesses that the extractor computes from the sampled runs. Per bundle,
[`actionSpecToLedgerData`](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Ledger/SinsemillaDLR.lean)
refines each extracted circuit witness to the games-facing ledger data or a computed
Sinsemilla break, and `bundleLedgerData` traverses the whole bundle. Each component
argument consumes the Action statement's satisfaction (`ActionSatisfied`) on the
annotated witness; in the model's replay case, the ledger oracle reproduces the
previously supplied witness. The composed endpoints bound the extraction-failure arm
together with the deployed violation events.
The `_idealizedks` endpoints remain, stated directly over that annotated model —their
names mark it— and the composed capstones consume them at the constructed adversary.

On the composed route to the Balance goals, the `_of_dlogProfiles` endpoints carry no
per-arm hypotheses at all. The knowledge arm is discharged by the adaptive-statement
capstone, applied once per slot-size pair, and every relation arm —the per-pair escapes,
the Sinsemilla reducer's relations, and the value-DLR finder's— is carried by the single
term `combinedDLRAdvantage`: one event over the composed deployed experiment, whose
samples all compute nontrivial relations over the combined deployed basis
(`orchardPoints`). The k·maxActions factor multiplies only the knowledge arm and is
tracked as [#214](https://github.com/zcash/ironwood/issues/214). The deployed forms
state validity at the deployed value bases: the value commitment is definitionally the
deployed one, with no reference-string step on the value side. Their accepted
trade-offs —the binding challenge hash as a random oracle, the per-size finite
presentation of the Fiat–Shamir oracle, and elided byte encodings— are documented at
`IdealizedKSBalanceAdversary.deployedViolationEvent`. For Spendability and Spend
Authority the annotations remain a modelling assumption: those games are not yet
composed with the circuit layer, and
[#155](https://github.com/zcash/ironwood/issues/155) tracks the oracle-machine layer
for their capstone slots.

Also open is RedDSA unforgeability. The RedDSA node is a named hypothesis rather than a
terminal assumption: its discharge edge names the reduction for security of signatures
with re-randomizable keys
([Efficient Unlinkable Sanitizable Signatures from Signatures with Re-Randomizable Keys](https://eprint.iacr.org/2015/395),
section 3), adapted to the ±-randomized variant, together with the same straight-line
AGM+ROM extraction of Fuchsbauer–Plouviez–Seurin
([Blind Schnorr Signatures and Signed ElGamal Encryption in the Algebraic Group Model](https://eprint.iacr.org/2019/877),
Theorem 1) that discharges the binding-signature extractability node at
$(q_H + 2)/\FieldSize + \varepsilon_{\mathrm{DL}}$. The two arms differ in the signing
oracle: the binding-signature extraction has none to simulate, because the signature
extracted from is the adversary's own, while the RedDSA unforgeability game has one.
The planned discharge is to simulate the signing oracle by programming the challenge
oracle at the re-randomized key; the randomizer, carried by the forgery, enters the
extraction as a known coefficient.

Every solid arrow reads "rests on"; where an edge carries a label, the label names the
computed break object flowing along it, or the side condition under which the reduction
holds (base independence from the group hash). Heavy purple arrows mark reductions (or
intended reductions) in the AGM+RO: both the source and the target of such an edge are
interpreted as games against online-AGM adversaries with the challenge oracle as a
programmable random oracle, so the model scopes the whole reduction rather than being
one more assumption it rests on — see
[Security Models](security-models.md#the-algebraic-adversary-restriction). The
`CollisionUpToSign` arm is terminal without any assumption — its bound is the
[birthday count](https://github.com/zcash/ironwood/blob/main/Zcash/Security/Common/Birthday.lean)
over the oracle table, a pure counting argument. It is the one purely random-oracle
reduction on this page, and it belongs to the ZIP 2005 recovery analysis rather than
the pre-quantum story. The games are the top-level capstones.

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
