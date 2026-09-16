---
name: pr-preflight
description: Pre-PR audit of an ironwood branch against the violations reviewers flag most — census inclusion and reachability, unnecessary trust-base growth (native_decide, @[csimp]), noncomputable on reductions, break-event fabricability, overclaiming prose, and merge-artifact churn. Use before opening or updating a PR, when self-reviewing a branch, after a rebase or merge, when adding endpoints/native_decide/csimp/noncomputable/break structures, or when asked to "preflight", "pre-PR check", or "audit the branch".
---

# PR preflight (compiled from PR #4–#173 review feedback)

Every rule here is a violation reviewers have flagged more than once. The skill is an audit
procedure, not a style essay: run the checks against `git diff main...HEAD`, answer each
question, and fix or justify before handing over. Prose register and docstring structure are
owned by the `proof-comment-style` skill — this skill owns what the prose *claims* and what the
Lean *trusts*.

## 1. Census — every new trust-bearing declaration gets a direct pin that actually runs

A pin that exists but never elaborates is the worst outcome: CI stays green over a `sorry`.
Check all six failure modes; each has occurred in a merged or nearly-merged PR.

1. **Direct pin exists.** Every new endpoint (the capstone naming families, or the semantic
   suffixes `_error_bound`, `_finite_security`, `_measure_le`, `_probability_bound`,
   `_capstone`) has its own `assert_axioms` / `assert_computable` entry in
   `Zcash/TrustBoundary.lean` or a fixture-local trust-boundary module. Transitive coverage
   through a dependent's pin is not coverage — it vanishes when the dependent is refactored.
2. **The pinned module is reachable from some default target.** A census entry in a module
   nothing builds never runs. For each new `.lean` file, confirm it is reachable from one of
   the lakefile's `defaultTargets` — either in an import cone or matched directly by a lakefile
   glob (`Zcash.Snark.Soundness.+`), which covers a module no import reaches. Run
   `scripts/check_build_coverage.sh`, which asserts exactly this for every module in the
   package. A file with no consumer and no target membership is checked by nothing, however
   many assertions it contains.
3. **Fully qualified names.** `open Zcash.Snark` does not bring `Deployed.foo` into scope as
   bare `foo`; an unqualified census entry can silently resolve to the wrong homonym. Census
   entries write the full path.
4. **Endpoint names fit the census regex.** `scripts/check_endpoint_census.sh` only sees the
   listed families and semantic markers (`_prob_le`, `_error_bound`, `_finite_security`,
   `_capstone`, ...), matched in any position — a qualified name such as
   `_prob_le_of_textbookDL` or `_prob_le_at_consensus_max` is demanded, not exempt. A new
   endpoint is renamed to fit the pattern — the regex is not widened ad hoc. Refine the regex
   only when genuinely needed.
5. **Rebases drop entries silently.** After any rebase or merge, read
   `git diff main...HEAD -- Zcash/TrustBoundary.lean` and account for every *deleted* line by
   name. A consolidation that loses another PR's pins passes CI and loses the guarantee.
6. **The flags are automatic; the tier claim is not.** Don't audit flag minimality by hand — a
   missing `+choice` / `+native` fails, and so does a redundant one, so the build settles the
   flag set either way. A narrowing elsewhere in the PR that makes a flag unnecessary surfaces
   as a census error rather than as silent over-permission. What does need judgment: never
   `assert_no_sorry` — both census commands
   imply it and we always want an axiom assertion. `#guard_msgs`-pinned `#print axioms` is
   weaker than `assert_axioms +native(...)`, not stricter; don't describe or use it as the
   stronger check outside the fixture censuses where the exact axiom set is the claim.

Run `scripts/check_endpoint_census.sh` and `scripts/check_csimp_census.sh` before handing over.

## 2. Trust surface — every extension of the trusted base is argued for

The governing rule is general, not a per-feature quota: **we shouldn't be unnecessarily
increasing the trust base.** CompElliptic's
[Trust Discipline](https://github.com/daira/CompElliptic#trust-discipline) is the standard this
development follows, and
[lean-native-trust-research.md](https://github.com/daira/CompElliptic/blob/main/design/lean-native-trust-research.md)
records what `native_decide` and `@[csimp]` actually depend on.

Both extend the trusted base and neither is free. `@[csimp]` extends it further — its
equivalence proof rules out only a limited class of mistakes, not the expansion itself — so
removing an existing `@[csimp]` outranks removing a `native_decide`, and no *new* `@[csimp]` is
added at all. But `native_decide` is held to the same direction of travel, not a lower bar:
ideally it does not appear either. Audit every use stringently against the ladder below instead
of waving it through, and treat data anchoring as where a survivor may live, not as a standing
licence.

For each `native_decide` the diff adds, in order:

1. Does `decide` or `norm_num` close it? Then use that. (A reviewer caught `(-1 : Fp) ≠ 1`
   proved by `native_decide`.)
2. Does a compositional proof from existing lemmas exist? Then prove it. Prefer certifying one
   general fact (an element's order, a generic congruence) over native-deciding an
   instance-specific table.
3. Is the statement minimal — one fact, no fused conjunctions, no re-running `assemble` for a
   second claim that is cheap or already checked elsewhere?
4. Is it anchoring *captured data* (a fixture capture check, `fingerprint_matches` tier — facts
   with no other source)? That is the only category where a new native axiom is legitimate.
   Correctness properties of objects the repo derives itself are proved by construction or
   generically, not natively.

A survivor has to earn the trust it adds. It needs its census pin with the `+native(decl)`
origin, plus a justification in the PR that says which rungs above were tried and why each
failed — "it was easier" and "it is only a fixture" are not that. Native *execution*
(evaluation-based checks in the lane import cone) is an explicit documented opt-in — never
ambient.

The same tier logic bans bespoke axioms and `implemented_by` outright: when the fact is proven
upstream (CompElliptic, Mathlib), remove the axiom rather than pin it.

There should be no uses of `@[extern]`, `@[implemented_by]`, or `unsafe`, and no
new uses of `@[csimp]`. Despite the restrictions that this development puts on use of
`@[csimp]` (checked in CI), it pulls in a
[large trust surface](https://github.com/daira/CompElliptic/blob/main/design/lean-native-trust-research.md#appendix-a-extern-vs-implemented_by-vs-csimp),
which is not worth the potential performance improvement. The equivalence proof it
requires prevents only a limited class of mistakes; it does not address this expansion
of the trusted base.

## 3. `noncomputable` — props for specs, defs for reductions

The discipline applies to *reduction producers*: anything that computes break data or feeds a
`def`. Proof-side machinery (measure-valued, polynomial-valued, choice-selectors that appear
only inside theorems) may be `noncomputable` freely.

For each `noncomputable` the diff adds, and for each new reduction:

- A reduction producer is a plain `def` pinned `assert_computable`. `Classical.choice` entering
  only through erased `Prop` certificate fields is the `+choice` flag, not a reason to mark the
  def noncomputable.
- A `noncomputable` marker is acceptable only when inert — the declaration appears inside
  theorems and never feeds a def. If in doubt, drop the marker and let the compiler object.
- Don't forget computed witnesses to `∃` or `Nonempty`: a reduction that computes an opening
  and then existentially closes it cannot be consumed as data by the next reduction, and
  retrofitting extraction-friendly statements is expensive. If a downstream layer consumes the
  witness, return the data. `Nonempty` is basically equivalent to `∃` in introducing
  non-extractability.
- Each surviving exception is documented in the book, and un-marking one later obliges the
  census-tier upgrade and the book-paragraph deletion in the same PR.

Enforcement is the build, not a grep: the census and the fingerprint path elaborating under
`native_decide` are the guarantee.

## 4. Break events — can you fabricate an inhabitant standalone?

The highest-value audit in the repo; it has caught independent violations at least four times
(a purpose-collidable commitment map, an affine-cancellable nullifier collision, a value-bounds-
free note-commit break, an unsatisfiable augmented-binding hypothesis).

For each new break/violation structure and each new hypothesis on an endpoint:

- **Fabrication test.** Try to inhabit the structure with a degenerate witness — zero, the
  identity, an affine cancellation, `v + 2^64`. If you can, the structure certifies nothing;
  the missing bound travels *in the structure*, not at the call site (per the terminal-break
  convention settled in PR #50).
- **Terminal vs intermediate.** A terminal break event must, where it is instantiated, name the
  assumption or model under which producing an inhabitant is infeasible. An intermediate
  certificate only has to be computed data, is consumed by a further reduction, and is never
  presented as a break by itself.
- **Satisfiability.** Exhibit an instantiation satisfying each new hypothesis — a classically
  satisfiable extraction hypothesis once made a capstone vacuous, and knowingly unsatisfiable
  hypotheses don't merge even with a caveat note. `getD`-style defaults must fail safe (default
  ≠ the demanded identity, so short inputs unsatisfy rather than silently satisfy).
- **Adversary completeness.** The modeled adversary receives everything the deployed adversary
  knows (all oracles, all public points); a silently narrower class (coin-space-only indexing,
  a restricted representation basis, `numProofs = 1` fed to every index) narrows the theorem.
  State strictly-stronger-adversary framings as such.

## 5. Claims — the prose may not outrun the proof term

For every touched docstring, module doc, book sentence, and the PR body:

- Does the proof term actually contain the asserted connection? "The deployed instantiation
  of X" claims a wiring; if the wiring is planned, write "to be discharged by X". State a
  discharge as intended rather than done; qualify with the hypotheses and modelling gaps.
- Security figures distinguish design target from achieved bound — never present the
  accounting scale as a proven end-to-end bound.
- Proof-map edges: node colour carries done/not-done; an edge label states what the reduction
  *uses*. Don't draw composition that isn't formalized.
- No dev-history narration, no stale identifiers, no references to closed issues (open-issue
  references for tracked gaps stay — removing them is blocking). Constants cite the spec section
  and the upstream Rust identifier.
- **Every new theorem carries a description** — no exceptions for trivial or private lemmas, and
  none for a name that looks self-explanatory. The doc comment says what the statement means and
  why the declaration exists (what it is for downstream, what it assumes, where its hypotheses
  come from); it does not transliterate the name or restate the type in words. A statement whose
  purpose cannot be written down in a sentence is usually the wrong statement. Register and
  structure are owned by the `proof-comment-style` skill; the requirement itself is audited here,
  because an undocumented lemma is where an unexamined claim survives review.
- Cite papers that claims rely on, or that provide important context. Check that
  it's the right paper and covers what is claimed. Ask the user to download it if
  you can't. Use this citation format:
  `(Author(s), linked title[, section/theorem][, venue year])`.
  For example:
  ```
  (Jaeger–Tessaro, <a href="https://eprint.iacr.org/2020/1213">Expected-Time Cryptography: Generic Techniques and Applications to Concrete Soundness</a>, Lemma 3)
  ```
  Link to full text if at all possible. Include the venue and year only if it is
  not an eprint and the version referenced is the one we want readers to look at;
  don't link to one version and then give the venue and year for another
  substantially different conference or journal version. Publication precedent
  doesn't matter for our purposes, pointing readers to a full, preferably
  open-access copy with all corrections does.

## 6. Diff hygiene — the diff contains only its own changes

- Read `git diff main...HEAD` hunk by hunk. Unrelated comment rewording, blank-line churn, and
  spelling regressions get reverted — prefer main on any comment the PR isn't about. An
  incidental formatting change needs a stated reason.
- After a rebase, check for resurrections (a declaration deleted on main reappearing) and merge
  zombies (a file restored into no build target, never elaborated). Self-review trust-boundary
  files in particular.
- New public declarations with zero consumers are wired, deleted, or explicitly kept as a named
  result with a comment saying so.

## 7. Interface and proof hygiene (quick checklist)

- Abstract in the middle, concrete at both ends. Interfaces and lemmas are generic over the
  circuit (`circuit.domainExponent`, not `11`), so they say something beyond the deployed
  instance. Final capstone statements, which are not generic, state the deployed literals
  instead: `11` is the actual Zcash number that is trusted, where `actionCircuit.domainExponent`
  could a priori be anything, and a reviewer should not have to chase another definition to
  check a capstone. Tie the two ends together with one explicit censused bridge equation
  (`actionCircuit.domainExponent = 11`), so the literal cannot drift from the model and the
  correspondence has a single place to check. No raised `maxHeartbeats` — seal the concrete def
  (`irreducible` / opaque) instead.
- Never suppress the unused-section-variable lint file-wide
  (`set_option linter.unusedSectionVars false`); `omit` the unused instances instead. The reason
  is census-relevant rather than cosmetic: an unused instance argument is still a subterm that
  axiom collection traverses, so a concrete consumer passing an axiom-carrying instance
  propagates that axiom into its census footprint. `omit` removes the argument outright.
- `@[simp]` only where the RHS is a genuine normal form wanted everywhere; otherwise consumers
  invoke the lemma explicitly.
- No unearned wrappers or generality; check Mathlib / CompPoly / CompElliptic before deriving
  anything that smells standard. A superseded route is removed in the same PR that supersedes
  it, or kept only with a stated reason and a tracking issue for its removal — naming one
  "legacy" is how redundant routes outlive their pruning deadline. Durable comments must not
  describe the new route by comparison against the superseded one ("unlike the legacy X …"):
  that inverts the present-state rule in §5, and goes stale exactly when the pruning happens.
- Hypotheses that are general facts get proved, not assumed; write the result type on any def
  or theorem whose body is a partial application (Lean silently appends hypotheses otherwise).
- Named structure fields over tuples and numeric accessors; no field defaults (an inherited
  default has produced a real modeling bug).
- No Mathlib glob imports — import surgically. Neither `import Mathlib` nor `import
  Mathlib.Tactic` may appear (both CI-gated by `scripts/check_no_umbrella_imports.sh`); name the
  specific modules a file actually uses. The cost is build-wide rather than local: the full
  umbrella peaks around 6.5 GB RSS per Lean process, and even `Mathlib.Tactic` costs roughly
  +1.6 s of import-load and +1.3 GB RSS per process over the narrow modules. Nothing fails when
  one creeps back in — builds just quietly get slow again, which is why it is gated rather than
  left to review.
- When narrowing an import, expect breakage beyond name resolution. The umbrella supplies
  definitions *and* simp/`norm_num`/`deriving` extensions transitively, so narrowing can break a
  file the change never touched: a lost `norm_num` parity extension turned a passing proof into
  a `sorryAx` that surfaced as `assert_no_sorry` failures several modules away. Re-run the
  default-target build after any import trim and read failures for a dropped extension, not just
  a dropped name.
- No dead imports; generic lemmas live beside their definitions, not where first used; no
  imports from `Soundness/` into lower layers.

## 8. Fixtures and process

- Fixture files are byte-fingerprinted — never touch them, including comments. Regeneration
  goes through `scripts/regenerate-fingerprint-fixtures.sh` and the SHA-256 pins.
- Dependencies pin full SHAs on canonical repos, never personal forks or mutable refs.
- The PR description is part of the reviewed artifact: refresh it after force-pushes, and
  "Closes #N" only with per-task accounting. Follow-up work gets a tracking issue, not only a
  docstring. Confirm CI ran on the exact head that merges.

## Final sweep

Before handing over, run each of these:

- `scripts/check_endpoint_census.sh`;
- `scripts/check_csimp_census.sh`;
- `scripts/check_census_pins.sh`;
- `scripts/check_no_umbrella_imports.sh`;
- `scripts/check_build_coverage.sh`; and
- `lake build --wfail` on the default target (not `lake build Zcash`, which touches none of the
  `FixtureCheck`, `CircuitCheck`, `MetaCheck`, or `SecurityCheck` cones and so elaborates less
  than the coverage property in §1 item 2 demands).

Then one pass over the full diff with the census, trust-surface, noncomputable, and claims
questions above, reporting per file what was fixed, what is compliant, and what needs author
judgment.
