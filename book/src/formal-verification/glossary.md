# Glossary

Coined terms and shorthand used across the [proof map](proof-map.md) and the Lean
development. Anchors point to a module + name under `Zcash/`.

<style>
.iw-glossary { margin: 1.3rem 0; display: grid; gap: 26px; }
.iw-glossary section { display: grid; gap: 9px; }
.iw-glossary .grp {
  font-size: .8rem; font-weight: 700; text-transform: uppercase;
  letter-spacing: .11em; opacity: .55; margin: 0;
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
<div class="g"><div class="g-head"><span class="term">fingerprint</span><span class="anchor">Verifier.Assemble.assemble · Fingerprint.Match.msmMatch_eval</span></div><div class="def">The whole verifier collapsed into one multi-scalar multiplication; the proof accepts exactly when that MSM is the group identity. Checked equal to the Rust verifier's captured MSM, for the specific circuit under analysis. The map's <em>pinned to Rust</em> node.</div></div>
<div class="g"><div class="g-head"><span class="term">conditional vs deployed</span><span class="anchor">Main.DeployedAccepts</span></div><div class="def"><em>Conditional</em> capstones take an opaque <code>accepts : Prop</code> — a scaffold, not finished soundness; <em>deployed</em> capstones take the concrete accept (assembled MSM = identity).</div></div>
<div class="g"><div class="g-head"><span class="term">verifier equation</span><span class="anchor">Main.deployedAccepts_verifierEq</span></div><div class="def">halo2's explicit IPA verifier equation, recovered from the compact <code>MSM = 0</code> accept — the readable form the IPA argument consumes.</div></div>
</section>

<section>
<div class="grp">Fiat–Shamir &amp; rewinding</div>
<div class="g"><div class="g-head"><span class="term">forking lemma</span><span class="anchor">Forking.Probability.extractable_of_prob</span></div><div class="def">Rewinding the random oracle to get three accepting continuations per round at distinct, nonzero challenges; assembled into the transcript tree the extractor consumes. Proven (an averaging argument) once the accept probability beats the knowledge error <code>kerr/Nᵏ</code>.</div></div>
<div class="g"><div class="g-head"><span class="term">rewind</span><span class="anchor">Forking.Rewind.roChallenges_reprogramRounds</span></div><div class="def">Re-running the schedule with the oracle reprogrammed at a round prefix: redrawing the IPA round vector is exactly reprogramming the deployed oracle (<code>roChallenges_reprogramRounds</code>) — the bridge from the forking measure to the deployed rewound runs, and the load-bearing consumer of <em>transcript ordering</em>. The <code>_rewind</code> capstones state the accept probability over these runs.</div></div>
<div class="g"><div class="g-head"><span class="term">prover strategy</span><span class="anchor">Forking.Rewind.deployedVerifierEq_iff_flatAccept</span></div><div class="def">halo2's verifier equation recast as the accept predicate of a concrete prover strategy read off the proof — the <em>proven</em> half of the prover-as-oracle bridge; only the random-oracle measure underneath stays a floor.</div></div>
<div class="g"><div class="g-head"><span class="term">round-by-round soundness</span><span class="anchor">Forking.Ordering</span></div><div class="def">The transcript-ordering guarantee: each IPA round point sits in the transcript prefix before its challenge is drawn, so later messages cannot bend earlier challenges.</div></div>
</section>

<section>
<div class="grp">Peel &amp; IPA extraction</div>
<div class="g"><div class="g-head"><span class="term">U / W</span><span class="anchor">Deployed.Binding</span></div><div class="def">The auxiliary generators the deployed verifier folds into the MSM alongside the main <code>g</code> basis — the fold and blinding terms.</div></div>
<div class="g"><div class="g-head"><span class="term">peel</span><span class="anchor">Deployed.IpaPeel.deployed_to_acceptV</span></div><div class="def">Stripping the <code>U</code>/<code>W</code> terms off the deployed transcript tree to recover a clean, <code>g</code>-only IPA tree — or, failing that, a discrete-log relation.</div></div>
<div class="g"><div class="g-head"><span class="term">three-special-soundness</span><span class="anchor">Ipa.Soundness.ipa_soundV</span></div><div class="def">Extraction of the witness from three accepting transcripts at pairwise-distinct, nonzero challenges per round.</div></div>
<div class="g"><div class="g-head"><span class="term">adjusted commitment</span><span class="anchor">Ipa.InnerProduct.ipaRelation_unshift · ipaRelation_unblind_value</span></div><div class="def">Folding the claimed value and synthetic blinder into the opened commitment: <code>P′ = P − [v]g₀ + [ξ]S</code>. The un-shift/un-blind lemmas move an opening of <code>P′</code> back to the actual multiopen commitment at its true value — the value-placement step <code>deployed_forking_relation</code> performs on the equation-to-tree edge.</div></div>
</section>

<section>
<div class="grp">Binding &amp; the AGM</div>
<div class="g"><div class="g-head"><span class="term">NontrivialRelation</span><span class="anchor">Security.BindingSignature.NontrivialRelation</span></div><div class="def">A nontrivial discrete-log relation, carried as data with its coefficients explicit. One always exists at prime order, so an ∃-closed <code>Prop</code> version (or an <code>∨</code>-branch concluding it) is vacuous <em>as a statement</em>; the reductions <em>compute</em> one from a break, and the force is the computational assumption that no efficient adversary can <em>find</em> one.</div></div>
<div class="g"><div class="g-head"><span class="term">algebraic certificate</span><span class="anchor">AGM.Prover.AlgebraicDForkCert · AGM.Capstone.deployedAlgebraicForkingRelation</span></div><div class="def">A deployed fork certificate whose every prover round point carries coefficients over the complete original <code>(g,U,W)</code> basis. The computed capstone erases it into the deployed validity check and returns either the opening or the explicit relation consumed by the DL reduction; no relation is selected with <code>Classical.choice</code>.</div></div>
<div class="g"><div class="g-head"><span class="term">fixed-slot</span><span class="anchor">AGM.Adapter.FixedSlotEmbedding · FixedSlotRelationOutcome</span></div><div class="def">The AGM trick: hide a discrete-log challenge in one basis slot fixed before the adversary runs. A hit yields the discrete log; a miss retains the exact same returned relation and proves its coefficient at that slot is zero.</div></div>
<div class="g"><div class="g-head"><span class="term">DL reduction bound</span><span class="anchor">AGM.ProbabilityVesta.orchard_deployed_relation_prob_le_of_generatorRO_textbookDL</span></div><div class="def">The random-slot accounting instantiated with the deployed relation producer: its computed relation branch is exactly <code>relSet</code>, and its probability is bounded by <code>|basis|</code> times the textbook-DL advantage. For distinct parameter queries, <code>orchard_uniformURSIdentification_of_generatorRO</code> derives the complete basis-distribution equality in the group-valued generator-RO model; identifying halo2's concrete hash-to-curve with that oracle remains the setup idealization.</div></div>
</section>

<section>
<div class="grp">Constraints &amp; multiopen</div>
<div class="g"><div class="g-head"><span class="term">circuit satisfaction</span><span class="anchor">KnowledgeSoundness.circuitSatViaGates</span></div><div class="def">The decoded columns satisfy the circuit gates — the constraint half of the SNARK relation, paired with the IPA opening.</div></div>
<div class="g"><div class="g-head"><span class="term">batch rewinds</span><span class="anchor">Multiopen.Deployed.deployedMultiopenRewind_of_x4Prob</span></div><div class="def">The <code>x₄</code> forking floor: given an accepting honest run, an accept measure beating the pair-count bound extracts an injective family of accepting <code>x₄</code>-rewound runs — one IPA witness per run, the batch the decode inverts.</div></div>
<div class="g"><div class="g-head"><span class="term">decoded columns</span><span class="anchor">Multiopen.Decode.decodedCols</span></div><div class="def">The <code>x₄</code>-level columns recovered from the batched multiopen witness by Vandermonde inversion of rewound openings — the point-set aggregates (<code>qᵢ</code>, <code>q′</code>), not yet circuit columns; the <code>x₁</code> unbatch reads the member commitments out of them.</div></div>
<div class="g"><div class="g-head"><span class="term">challenge batch (x₄) · challenge unbatch (x₁)</span><span class="anchor">Multiopen.Deployed.deployedCommitment_x4_batch · deployed_witness_member_binding</span></div><div class="def">The multiopen batching layers: <code>x₄</code> folds all opening claims into one by powers of the challenge; <code>x₁</code> bundles the commitments queried at each point set into an aggregate, which the unbatch opens back to the individual member commitments — pinning the extracted witness as the two-level power combination of their column witnesses.</div></div>
<div class="g"><div class="g-head"><span class="term">bad set</span><span class="anchor">Constraints.Vanishing.szBadSet · GoodChallenge</span></div><div class="def">The challenge values that fool the gate check — the roots of the constraint-difference polynomial; a uniform random-oracle challenge lands in it with probability ≤ <code>d/p</code> (Schwartz–Zippel). A challenge outside it is the map's <em>sound challenge</em>.</div></div>
</section>

<section>
<div class="grp">Capstones &amp; hypotheses</div>
<div class="g"><div class="g-head"><span class="term">capstones</span><span class="anchor">Soundness/Vesta.lean · AGM.ProbabilityVesta</span></div><div class="def">The top-level <code>orchard_verifier_vesta_*</code> ladder exposes opening and constraint forms across conditional, reduction, forking, deployed, adaptive, and rewind models. Its probability-to-fork rungs remain noncomputable because <code>Extractable</code> is propositional. The separate <code>orchardDeployedAlgebraicForkingFixedSlot</code> endpoint is computable from an explicit algebraic certificate and returns opening, DL solution, or an exact-relation fixed-slot miss.</div></div>
<div class="g"><div class="g-head"><span class="term">quotient check</span><span class="anchor">hquot · Soundness/Vesta.lean</span></div><div class="def">The verifier's gate/quotient point-check, plus carrying the gate challenge <code>x</code> over to the multiopen point <code>x₃</code>. Carried as the capstone hypothesis <code>hquot</code>; still open.</div></div>
<div class="g"><div class="g-head"><span class="term">sound challenge</span><span class="anchor">hgood · Soundness/Vesta.lean</span></div><div class="def">The challenge avoids the Schwartz–Zippel bad set, so the point-check at <code>x</code> implies the full gate identity. Carried as the capstone hypothesis <code>hgood</code>; discharged by the SZ territory's <code>_xgood</code> wrapper.</div></div>
<div class="g"><div class="g-head"><span class="term">accept probability</span><span class="anchor">hprob · Soundness/Vesta.lean</span></div><div class="def">The accepting-proof probability beats the knowledge error <code>kerr/Nᵏ</code> — enough for the forking lemma to extract. Carried as the capstone hypothesis <code>hprob</code>; the measure-side random-oracle floor.</div></div>
<div class="g"><div class="g-head"><span class="term">structural residuals</span><span class="anchor">hz · hg0 · hs · hξ · Soundness/Vesta.lean</span></div><div class="def">The remaining structural capstone hypotheses: <code>z ≠ 0</code> (every rung), <code>g₀ ≠ 0</code> (every forking rung), the S-opening <code>commit s = ipaS</code> (deployed/adaptive/rewind rungs), and value recovery <code>ξ·⟨s,b⟩ = 0</code> (constraint rungs only). Assumed in-Lean, priced rather than discharged.</div></div>
<div class="g"><div class="g-head"><span class="term">high-level relation · VK correctness</span><span class="anchor">hencodes · Verifier.Assemble</span></div><div class="def">The two gaps the composition does not yet cross: on the output side, <code>hencodes</code> — gate satisfaction (<code>SnarkRelation</code>) implies the intended high-level statement; on the input side, VK correctness — the verifying key fed to the verifier faithfully encodes the real deployed circuit. Both outside Lean; not started.</div></div>
</section>

<section>
<div class="grp">Conventions</div>
<div class="g"><div class="g-head"><span class="term">breaks as computed data</span><span class="anchor">Security.RandomOracle · Security/Ledger · Security/BindingSignature</span></div><div class="def">Break events are structures carrying the breaking data (colliding queries, relation coefficients); the reductions producing them are plain computable <code>def</code>s. An ∃-closed break <code>Prop</code> is vacuously true at the instantiations of interest (relations always exist at prime order; compressing hashes always have collisions), so the content lives in the data, protected by compiler-checked computability and pinned axiom sets. See <a href="../formal-verification.html#breaks-as-computed-data">Breaks as computed data</a>.</div></div>
<div class="g"><div class="g-head"><span class="term">checked trust boundary</span><span class="anchor">Fingerprint.TrustBoundary · Ledger.TrustBoundary · BindingSignature.TrustBoundary · AGM.TrustBoundary</span></div><div class="def">Build-time pins on what a theorem may rest on: <code>assert_no_sorry</code> over the elaborated dependency graph plus a <code>#guard_msgs</code>-pinned <code>#print axioms</code>, so a stray <code>sorry</code> or a new axiom fails the build instead of silently widening the trusted base. See <a href="../formal-verification.html#trust-discipline">Trust discipline</a>.</div></div>
</section>

</div>
