---
name: pr-preflight
description: Pre-PR audit of an ironwood branch against the violations reviewers flag most — census inclusion and reachability, native_decide necessity, noncomputable on reductions, break-event fabricability, overclaiming prose, and merge-artifact churn. Use before opening or updating a PR, when self-reviewing a branch, after a rebase or merge, when adding endpoints/native_decide/noncomputable/break structures, or when asked to "preflight", "pre-PR check", or "audit the branch".
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
2. **The pinned module is reachable from a build root.** A census entry in a file no target
   imports never runs. For each new `.lean` file, confirm it is in the import cone of
   `Zcash.lean` or `FixtureCheck`; a file with no consumer and no target membership is checked
   by nothing, however many assertions it contains.
3. **Fully qualified names.** `open Zcash.Snark` does not bring `Deployed.foo` into scope as
   bare `foo`; an unqualified census entry can silently resolve to the wrong homonym. Census
   entries write the full path.
4. **Endpoint names fit the census regex.** `scripts/check_endpoint_census.sh` only sees the
   listed families and suffixes. A new endpoint is renamed to fit the pattern — the regex is
   not widened ad hoc.
5. **Rebases drop entries silently.** After any rebase or merge, read
   `git diff main...HEAD -- Zcash/TrustBoundary.lean` and account for every *deleted* line by
   name. A consolidation that loses another PR's pins passes CI and loses the guarantee.
6. **Tightest true tier, minimal flags.** Try the census entry without `+choice` / `+native`;
   keep flags only if the build demands them. Never `assert_no_sorry` — both census commands
   imply it and we always want an axiom assertion. `#guard_msgs`-pinned `#print axioms` is
   weaker than `assert_axioms +native(...)`, not stricter; don't describe or use it as the
   stronger check outside the fixture censuses where the exact axiom set is the claim.

Run `scripts/check_endpoint_census.sh` and `scripts/check_csimp_census.sh` before handing over.

## 2. `native_decide` — data anchoring only, minimal, and trending to zero

The repo's stated direction is removal ("the performance gain is not worth the extension of the
trusted base"). For each `native_decide` the diff adds, in order:

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

Any survivor needs its census pin with the `+native(decl)` origin and a one-sentence
justification in the PR. Native *execution* (evaluation-based checks in the lane import cone)
is an explicit documented opt-in — never ambient.

The same tier logic bans bespoke axioms and `implemented_by` outright: when the fact is proven
upstream (CompElliptic, Mathlib), remove the axiom rather than pin it. `@[csimp]` with a
kernel-checked equality is the permitted counterpart, and every `@[csimp]` is censused.

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
  witness, return the data.
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
  references for tracked gaps stay — removing them is blocking). Every theorem, including
  trivial private lemmas, carries a doc comment. Constants cite the spec section and the
  upstream Rust identifier; papers get author, year, and link.

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

- Interfaces keep abstract spellings (`actionCircuit.domainExponent`, not `11`); concretization
  happens inside proofs or at the fixture boundary. No raised `maxHeartbeats` — seal the
  concrete def (`irreducible` / opaque) instead.
- `@[simp]` only where the RHS is a genuine normal form wanted everywhere; otherwise consumers
  invoke the lemma explicitly.
- No unearned wrappers or generality; prune a route the moment it is made redundant; check
  Mathlib / CompPoly / CompElliptic before deriving anything that smells standard.
- Hypotheses that are general facts get proved, not assumed; write the result type on any def
  or theorem whose body is a partial application (Lean silently appends hypotheses otherwise).
- Named structure fields over tuples and numeric accessors; no field defaults (an inherited
  default has produced a real modeling bug).
- No umbrella imports (CI-gated), no dead imports; generic lemmas live beside their
  definitions, not where first used; no imports from `Soundness/` into lower layers.

## 8. Fixtures and process

- Fixture files are byte-fingerprinted — never touch them, including comments. Regeneration
  goes through `scripts/regenerate-fingerprint-fixtures.sh` and the SHA-256 pins.
- Dependencies pin full SHAs on canonical repos, never personal forks or mutable refs.
- The PR description is part of the reviewed artifact: refresh it after force-pushes, and
  "Closes #N" only with per-task accounting. Follow-up work gets a tracking issue, not only a
  docstring. Confirm CI ran on the exact head that merges.

## Final sweep

Before handing over: `scripts/check_endpoint_census.sh`, `scripts/check_csimp_census.sh`,
`scripts/check_no_umbrella_imports.sh`, `typos`, `lake build Zcash` — then one pass over the
full diff with the census, native, noncomputable, and claims questions above, reporting per
file what was fixed, what is compliant, and what needs author judgment.
