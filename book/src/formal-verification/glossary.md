# Glossary

Coined terms and shorthand used across the [proof map](proof-map.md) and the Lean
development. Anchors point to a module + name under `Zcash/`.

<style>
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
<div class="grp">The fingerprint</div>
<div class="g"><div class="g-head"><span class="term">fingerprint</span><span class="anchor">Verifier.Assemble.assemble · Fingerprint.Match.msmMatch_eval</span></div><div class="def">The whole verifier collapsed into one multi-scalar multiplication; the proof accepts exactly when that MSM is the group identity. Checked equal to the Rust verifier's captured MSM on four captures — two honest accepting runs and two match-only ones — for the specific circuit under analysis. The map's <em>pinned to Rust</em> node.</div></div>
<div class="g"><div class="g-head"><span class="term">match-only capture</span><span class="anchor">Fixtures.SingleAction.Random.Boundary · nonInteractiveFingerprint_matches_derived</span></div><div class="def">A capture of the deployed verifier run on a <em>random</em> proof string: deliberately non-accepting, it witnesses coefficient-for-coefficient agreement without an accepting run. Random inputs reach the proof slots honest proofs cannot vary, so these captures carry the trust-boundary invariant.</div></div>
<div class="g"><div class="g-head"><span class="term">deployed acceptance</span><span class="anchor">Main.DeployedAccepts</span></div><div class="def">The concrete verifier decision: the MSM assembled from the proof, instances, verifying key, and derived challenges evaluates to the group identity.</div></div>
<div class="g"><div class="g-head"><span class="term">verifier equation</span><span class="anchor">Main.deployedAccepts_verifierEq</span></div><div class="def">halo2's explicit IPA verifier equation, recovered from the compact <code>MSM = 0</code> accept — the readable form the IPA argument consumes.</div></div>
</section>

<section>
<div class="grp">Fiat–Shamir &amp; oracle execution</div>
<div class="g"><div class="g-head"><span class="term">querying adversary</span><span class="anchor">FiatShamir.Adversary.OracleComp</span></div><div class="def">An adaptive oracle-query computation with eager whole-table semantics, an explicit query bound, and a log of the points read on each execution. The straight-line reduction uses this model to price fresh-query and pinned-root events without constructing a transcript tree.</div></div>
<div class="g"><div class="g-head"><span class="term">IPA splice</span><span class="anchor">FiatShamir.Execution.spliceIpa</span></div><div class="def">Replacing only a proof's IPA fields while preserving the pre-IPA proof data. The adaptive AGM handoff uses this data operation when assembling the proof returned by its algebraic adversary; it is not a rewind extractor.</div></div>
<div class="g"><div class="g-head"><span class="term">round-by-round soundness</span><span class="anchor">FiatShamir.Ordering</span></div><div class="def">The transcript-ordering guarantee: each IPA round point sits in the transcript prefix before its challenge is drawn, so later messages cannot bend earlier challenges.</div></div>
</section>

<section>
<div class="grp">Straight-line IPA extraction</div>
<div class="g"><div class="g-head"><span class="term">U / W</span><span class="anchor">Deployed.Binding</span></div><div class="def">The auxiliary generators the deployed verifier folds into the MSM alongside the main <code>g</code> basis — the fold and blinding terms.</div></div>
<div class="g"><div class="g-head"><span class="term">IPA classification</span><span class="anchor">AGM.StraightLineIpa.straightLineBindingAttackZIndexedRootOrRelation</span></div><div class="def">From one algebraically represented accepting proof, compute either the required opening data, an explicit relation over the augmented basis, or a pinned low-degree challenge event. No recursive transcript tree is constructed.</div></div>
<div class="g"><div class="g-head"><span class="term">adjusted commitment</span><span class="anchor">InnerProduct.ipaRelation_unshift · ipaRelation_unblind_value</span></div><div class="def">Folding the claimed value and synthetic blinder into the opened commitment: <code>P′ = P − [v]g₀ + [ξ]S</code>. The un-shift/un-blind lemmas move an opening of <code>P′</code> back to the actual multiopen commitment at its true value.</div></div>
</section>

<section>
<div class="grp">Binding &amp; the AGM</div>
<div class="g"><div class="g-head"><span class="term">NontrivialRelation</span><span class="anchor">Security.BindingSignature.NontrivialRelation</span></div><div class="def">A nontrivial discrete-log relation, carried as data with its coefficients explicit. One always exists at prime order, so an ∃-closed <code>Prop</code> version (or an <code>∨</code>-branch concluding it) is vacuous <em>as a statement</em>; the reductions <em>compute</em> one from a break, and the force is the computational assumption that no efficient adversary can <em>find</em> one.</div></div>
<div class="g"><div class="g-head"><span class="term">programmed-basis</span><span class="anchor">AGM.Adapter.ProgrammedBasisEmbedding · ProgrammedRelationOutcome</span></div><div class="def">The AGM reduction: program every basis slot from the discrete-log challenge as <code>x·B + y·C</code> with fresh uniform pairs (Jaeger–Tessaro, Lemma 3). A relation with nonzero challenge component yields the discrete log of the challenge; a miss retains the exact same returned relation and proves it annihilates the programming — a single <code>1/|F|</code> hyperplane, with no slot guess and no <code>|basis|</code> factor.</div></div>
<div class="g"><div class="g-head"><span class="term">straight-line AGM extractor</span><span class="anchor">AGM.StraightLinePinnedRoots.StraightLineIpaOnlineTrace · Composition.StraightLineDeployed.ComputedStraightLineDeployedFSFamily.ofCovered · Composition.StraightLineConstraint</span></div><div class="def">The deployed AGM route, and since ironwood#133 the only one. Each IPA round exposes an executable pre-squeeze polynomial computation, proves that it has not queried that round's squeeze point, and connects its result to the final proof. One accepting transcript therefore yields a clean decode, explicit DLOG relation, or pinned quadratic event. The combined finder uses at most four prover invocations, so no expected-runs truncation or Markov tail appears anywhere in the bound. <code>ofCovered</code> packages the representation-carrying online prover with caller-supplied executable root, IPA, and constraint-<code>x</code> stages plus freshness proofs; the captured endpoint applies existing verifier metadata without a new proof fixture. The representations are ghost extractor data, not Halo2 proof bytes; this is an AGM-and-random-oracle result. The verifying key, instance commitments, and initial transcript prefix are fixed per basis before oracle access. Only the adaptive-statement capstone permits online statement choice.</div></div>
<div class="g"><div class="g-head"><span class="term">DL reduction bound</span><span class="anchor">AGM.Probability.TextbookDLAdvantageLE · AGM.StraightLineFiniteSecurity.StraightLineDirectDlogProfile · Action.AdaptiveStatementProfile.AdaptiveStatementDirectDlogProfile</span></div><div class="def">The programmed-basis reduction turns a computed relation into either a discrete-log solution or one <code>1/|Fp|</code> miss hyperplane. The straight-line and adaptive profiles record random-oracle queries, group work, and direct-decode work separately. The adaptive-statement finder retains one output/annotation execution for every provenance and source comparison, then charges the quotient, identity, and terminal stages separately. Thus a <code>2^123</code> computational work target maps to at most <code>2^126</code> Vesta DLOG queries and group work, while the consensus-generic statistical soundness error is independently at most <code>2^-83</code>. Lean proves the resource arithmetic and executable reduction boundary but leaves the finite-security Vesta DLOG advantage at that ceiling as a caller-supplied cryptographic premise.</div></div>
</section>

<section>
<div class="grp">Constraints &amp; multiopen</div>
<div class="g"><div class="g-head"><span class="term">circuit satisfaction</span><span class="anchor">KnowledgeSoundness.circuitSatViaConstraints</span></div><div class="def">The decoded columns satisfy the verifier's full compressed constraint identity, including custom gates, permutation constraints, and lookups — the constraint half of <code>SnarkRelation</code>.</div></div>
<div class="g"><div class="g-head"><span class="term">opened batch</span><span class="anchor">Multiopen.Opened.OpenedBatchOpenings</span></div><div class="def">A family of explicit AGM-supplied openings in flat <code>x₄</code>-power form, with witness, <code>U</code>, and <code>W</code> components carried as data. It is not constructed from an accept-measure rewind.</div></div>
<div class="g"><div class="g-head"><span class="term">decoded columns</span><span class="anchor">Multiopen.Opened.openedColumnDecode</span></div><div class="def">The <code>x₄</code>-level point-set aggregates recovered by applying the Vandermonde inverse componentwise to explicit opened-batch data.</div></div>
<div class="g"><div class="g-head"><span class="term">challenge batch (x₄) · challenge unbatch (x₁)</span><span class="anchor">Multiopen.Deployed.deployedCommitment_x4_batch · AGM.DecodeToOpened.DeployedAlgebraicDecode.toMemberDecode</span></div><div class="def">The deployed <code>x₄</code> fold is proved to have the flat power-batch shape. The AGM <code>x₁</code> layer then supplies explicit openings for the individual queried member commitments.</div></div>
<div class="g"><div class="g-head"><span class="term">bad set</span><span class="anchor">Constraints.Vanishing.szBadSet · GoodChallenge</span></div><div class="def">The challenge values that fool the gate check — the roots of the constraint-difference polynomial; a uniform random-oracle challenge lands in it with probability ≤ <code>d/p</code> (Schwartz–Zippel). A challenge outside it is the map's <em>sound challenge</em>.</div></div>
<div class="g"><div class="g-head"><span class="term">x-squeeze schedule · εₓ</span><span class="anchor">Composition.ScheduleBudget · Fixture2.deployedConstraintXSqueezeSchedule_captured</span></div><div class="def">The straight-line pricing of the constraint-evaluation challenge: the pre-<code>x</code> constraint difference's root set is capped by the degree walk — <code>εₓ = 20470/|𝔽|</code> at the captured key, consumed as <code>(Q+1)·εₓ</code>. Its causal half (the set is pinned before the <code>x</code> squeeze) is the named premise.</div></div>
<div class="g"><div class="g-head"><span class="term">captured knowledge-error bound</span><span class="anchor">Fixture2.orchard_deployed_knowledge_error_captured_straightLine_generatorRO</span></div><div class="def">The additive deployed extraction bound at the captured key. The straight-line AGM endpoint uses the staged representations and a fixed four-call finder, adding the <code>2k</code> IPA-root term and no expected-runs or Markov term. It includes the tight DLOG term, the shape's root budget, and the concrete <code>(Q+1)·20470/|𝔽|</code> constraint-root term. It is a compressed-identity statement; row-level gate, permutation, and lookup semantics carry the four explicitly priced <code>y</code>/<code>β</code>/<code>γ</code>/<code>θ</code> budgets through the matching semantic promotion (<code>straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile</code>).</div></div>
</section>

<section>
<div class="grp">Capstones</div>
<div class="g"><div class="g-head"><span class="term">capstones</span><span class="anchor">Capstones/Action.lean</span></div><div class="def">The adaptive-statement capstone proves knowledge soundness for the deployed Action verifier, for algebraic adversaries (the online Algebraic Group Model), with the challenge derivation modelled as a random oracle. The adversary chooses the public statement and the proof together after making its oracle queries. The statement is bound into the challenge derivation through the vk representation and its instance commitments. For every consensus-valid Action count, the probability that the verifier accepts while executable witness extraction fails is at most <code>Adv_DLOG(2^126, 2^126) + 2^-83</code> at the <code>2^123</code> computational work target. The arguments to <code>Adv_DLOG</code> are upper bounds on the number of random-oracle queries and group operations respectively. This states that within a <code>2^123</code> adversary work envelope, the constant term of the soundness error does not exceed <code>2^-83</code>; it is not an unqualified failure-probability claim. The random oracle ranges over bounded transcripts of the deployed schedule. AGM representations accompany every query but are erased before the oracle answers. The family fixes its key digest and verifier representations per basis before oracle access. Bundle size is public and universally quantified up to the consensus maximum.</div></div>
<div class="g"><div class="g-head"><span class="term">knowledge-failure event</span><span class="anchor">ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeFailureEvent</span></div><div class="def">The event that the deployed Action verifier accepts but the executable extractor does not return private witnesses for the entire bundle. The capstone bounds this event directly.</div></div>
<div class="g"><div class="g-head"><span class="term">semantic residuals</span><span class="anchor">ComputedAdaptiveActionStatementFSFamily.semanticEvent</span></div><div class="def">The explicitly priced <code>y</code>, <code>β</code>, <code>γ</code>, and <code>θ</code> challenge surfaces needed to promote the compressed constraint identity to row-level gate, permutation, and lookup semantics.</div></div>
<div class="g"><div class="g-head"><span class="term">high-level relation · VK provenance</span><span class="anchor">ActionBundleWitness · Keygen.Certificate</span></div><div class="def">The composed capstone returns the deployed Action circuit's private witnesses and satisfaction proofs. The remaining output-side floor is the bridge from that compiled circuit specification to the abstract Orchard ledger relation. On the input side, Lean derives the verifying key and checks it against the capture; identifying that capture with Orchard's canonical deployed artifact and byte serialization remains external.</div></div>
</section>

<section>
<div class="grp">Conventions</div>
<div class="g"><div class="g-head"><span class="term">breaks as computed data</span><span class="anchor">Security.RandomOracle · Security/Ledger · Security/BindingSignature</span></div><div class="def">Break events are structures carrying the breaking data (colliding queries, relation coefficients); the reductions producing them are plain computable <code>def</code>s. An ∃-closed break <code>Prop</code> is vacuously true at the instantiations of interest (relations always exist at prime order; compressing hashes always have collisions), so the content lives in the data, protected by compiler-checked computability and pinned axiom sets. See <a href="../formal-verification.html#breaks-as-computed-data">Breaks as computed data</a>.</div></div>
<div class="g"><div class="g-head"><span class="term">checked trust boundary</span><span class="anchor">Zcash.TrustBoundary</span> (and <code>Zcash.Snark.Fixtures.*.TrustBoundary</code> modules)</div><div class="def">Build-time pins on what a theorem may rest on: <code>assert_axioms</code> asserts a bound on the axioms used by a definition, so that a stray <code>sorry</code> or a new axiom fails the build instead of silently widening the trusted base. <code>assert_computable</code> additionally asserts that the definition is a plain <code>def</code>, ensuring constructivity of security reductions. Some of the <code>TrustBoundary</code> modules also use <code>#guard_msgs</code>-pinned <code>#print axioms</code> checks, e.g. to pin specific native axioms. See <a href="../formal-verification.html#trust-discipline">Trust discipline</a>; what the fixture boundaries <em>check</em> is each family's <code>Boundary.lean</code> statement of record.</div></div>
</section>

</div>
