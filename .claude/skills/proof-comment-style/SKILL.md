---
name: proof-comment-style
description: Writing, tightening, and auditing Lean doc comments in the ironwood soundness stack (issue #35 conventions). Use when writing, editing, or reviewing doc comments in Zcash/**, when asked to "tighten"/"clean up" proof comments, when asked to audit/check/verify docstring consistency or adherence, or when a docs-only pass must review as a pure prose diff.
---

# Proof comment style (issue #35)

The docstrings are the durable record of the proof structure: the argument must stay
reproducible from the comments alone. Tightening is **restructuring, not weakening** — never
drop an honest caveat or soften a claim's scope; move it to where it belongs and say it once.

**House exemplar**: `Zcash/Security/BindingSignature/Balance.lean` (PR #4) — its idiom at small
scale, carried by the structural conventions below at large scale. PR #4's narrative style alone
does not survive a 5,000-line composition (pre-#35 `Soundness/Main.lean` was written in it and
degraded into walls of text); the ledgers, route maps, and one-home-per-story below are what let
it scale.

## The convention

1. **Lead with the plain claim, self-contained.** The first sentence says *what* the lemma
   establishes, in words, before the how, the caveats, or the history — and restates the fact in
   symbols or plain words (PR #4 style: "the value coefficient satisfies `A • V = (bsk − B) • R`")
   so the docstring reads without chasing references. Good leads from the codebase:
   - `The deployed Orchard verifier is sound, opening derived: …`
   - `Assumption: if the proof is accepted, there exist …` (assumed defs say so up front)
2. **Define jargon on first use** (per module), or point at the book's proof-map glossary. Coined
   terms that always need this: *fingerprint, capstone, rung, peel, fixed-slot, pinned,
   adjusted commitment, bad set, forking vs. rewind, deployed vs. conditional, decoded columns*.
3. **One caveat, not a paragraph.** A nuance needing three sentences becomes its own note — a
   `/-! ## … -/` section comment or a `--` note above the declaration — and the docstring points
   at it in one clause.
4. **Concrete over abstract** where a name or number will do (`P' = P − [v]g₀ + [ξ]S`, `≤ deg/p`,
   `assemble.eval = 0` — not "the adjusted commitment equation", "a small set", "the check").
5. **Bold role labels on milestones, and only there.** Load-bearing theorems open with a bolded
   role — `**Balance reduction (field level).**`, `**Orchard integer balance reduction
   (§4.14).**`, `**Deployed soundness, opening derived.**` — so a file skims by its milestones.
   Defs and supporting lemmas stay plain (`NontrivialRelation`, `valueCommit`,
   `DeployedAccepts`). Don't bold mechanically: a label on everything is a label on nothing.
6. **Italicised *either*/*or*** when a docstring states a reduction dichotomy — "*either* the
   bundle balances *or* an explicit nontrivial relation is computed" — the contrapositive
   reading of a breaks-as-computed-data reduction (`NontrivialRelation.ofBundleModImbalance`).
7. **Statement-shape rationale, once.** When a statement's *form* would surprise a reader — a
   reduction where an assumption was expected, a free `Prop` where a concrete relation was
   expected — write the why as a named module-docstring section and point at it. Exemplars:
   `Balance.lean` "How binding is expressed (and why not as 'no relation exists')";
   `Soundness/Main.lean` "The reduction form". Cite external results for nontrivial side-claims
   the way `Balance.lean` cites Jaeger–Tessaro (https://eprint.iacr.org/2020/1213).
8. **`§` is for named or public sections only** — an in-file section by its title
   (`` `§ Binding reduction` below ``) or the protocol spec (`§4.13`/`§4.14`). Never bare
   private plan numbers (§1/§2, "Step 4"): spell out what they name.
9. **Record proof-engineering rationale where it's used, the day it's written.** Non-obvious
   proof-term and modeling moves get a sentence at the declaration — this is exactly the
   knowledge that evaporates between sessions. Existing exemplars: why the multiopen grouping
   keys on slot identity rather than curve values (`CommitmentId`: halo2 keys by `std::ptr::eq`;
   a value-equality key would wrongly merge equal-valued slots), why an induction is set up the
   way it is (`Lookup.run_structure`: indices are `Fin (n + 1)` with `Fin.induction` so the
   `succ` case's hypothesis is exactly the predecessor row), why a statement quantifies over ℤ
   rather than ℕ (`value_zpow`: Mathlib's `SameCycle` uses ℤ). The test: if a future session
   would have to re-derive the trick before it could safely modify the proof, it is not written
   down enough. Proof sketches have exactly one home: as `--` step comments in the body
   (preferred — they sit next to the tactics they explain), or in the docstring only when the
   body has none. If the body already steps through the proof, the docstring says "stepped
   through in the body" in one clause and does not retell it.
10. **Short by default, in the PR #4 register.** The norm is one to three plain sentences: the
    fact, at most one short formula, at most one sentence of role — "No-overflow: an integer
    reducing to `0` mod `r` whose magnitude is `< r` is `0`. This turns balance mod `r` into
    integer balance." No clause-stacking, no symbol runs, no parenthetical doing a sentence's
    job. But keep the load-bearing Lean anchors: the predicates and lemmas the statement is about
    (`IpaRelation`, `circuitSat`) stay named — the budget is on symbol *density*, not presence.
    Supporting lemmas: 1–4 lines. Milestones: ≤ ~7 lines, overflow going to
    the module docstring or a section note. Specialisation wrappers do not retell the abstract
    theorem's story — "`foo` specialised to `SWPoint Vesta.curve`; same hypotheses, plus the
    Hasse bound" is enough. Drop role commentary the module docstring already carries, and drop
    a "Named assumptions:" ledger when the text already names every hypothesis binder once —
    ledgers are for hypothesis-heavy capstones (the `∨`-shaped stack endpoints), not
    three-hypothesis theorems.
11. **Introduce before use, in reading order.** No symbol or coined term appears in a formula
    before a plain-words sentence has said what it is. Module docstrings run: the claim → the
    objects/setting → what the verifier's check gives → what this file proves → what it relies
    on / what is missing. Red flags that prose is *structured but not intuitive* — being
    well-organised does not exempt it:
    - coined terms chained into a compound ("the grand-product → multiset-of-pairs kernel");
    - one parenthetical carrying a file, a lemma, and a formula at once;
    - an apposition equating three noun phrases ("name distinctness — δ-coset disjointness in
      the keygen — is exactly the injectivity of `label`").
    Unpack these: one idea per sentence, and every formula only after its symbols are named.
12. **Motivate, don't paraphrase.** For transcription definitions the code *is* the formula: the
    docstring gives the role, the intuition (what the step does, what it feeds or telescopes
    into, who consumes it), and the halo2 anchor. Keep at most one or two anchoring formulas —
    the ones that make the intuition concrete (the factor `value + β·name + γ`; the reassembly
    `Σᵢ hᵢ · (xⁿ)ⁱ`) — and leave the rest to the code: never a clause-by-clause prose rendering
    of the folds below ("`left` folds …, starting from …, multiplied by … each column").
    Obligations read as plain words ("the running product must start at `1` and end at `0` or
    `1`"); mechanisms in absorb/shed terms ("`z` multiplies in each column's factor under its own
    name and divides out the same factor under the name `σ` assigns it"). A closed-form
    theorem's docstring names the terms by role and lets the displayed statement carry the exact
    list. Exemplar: `Verifier/Expressions.lean`'s `permChunkExpression`.
13. **Complexity compounds with length.** The longer a doc comment, the simpler each sentence
    must be — verbosity, jargon, and equations are each tolerable alone but overwhelm together.
    Per docstring or module-docstring section: at most one displayed identity, jargon countable
    on one hand, and prefer a plain-words description over symbols ("the `(value, name)` pairs
    are unchanged when every cell is renamed to the next one in its cycle" — not the displayed
    multiset equation; the statements below carry the symbols). A module docstring longer than
    ~10 lines needs `##` sections, each obeying the same budget; if a section still wants more,
    the detail belongs on a declaration or in the book.

## Learnings from applying it

- **One home per recurring story.** Explanations that recur across theorems (the reduction-form
  vacuousness story, what the Fiat–Shamir bridge bundles, the bad-set pricing) get exactly one
  canonical home — module docstring or the owning declaration — and every other docstring
  references it in one sentence ("reduction form (see the module docstring)"). Duplicated
  recaps drift; pointers don't.
- **No private shorthand; issue numbers only for open tracked gaps.** Spell out repo-internal
  section numbers ("§1" → "the transcription layer (`assembleFinalMsm`/`ipaFold`, checked by the
  fingerprint fixtures)"). A doc comment cites an issue number only for a gap that is still open
  and tracked there, and states the fact first so that the sentence stands without the tracker
  ("`Describes` is not consumed by any theorem (#232)"). It never cites a closed issue, an issue
  that the PR itself closes, or an issue in place of the fact. The `pr-preflight` skill audits
  this: removing an open-issue reference for a tracked gap is blocking, and a reference is
  removed when its issue closes.
- **Module docstrings are maps, not walls.** Convert narrative paragraphs into: the families/
  endpoints as bullets, the proof route as a numbered chain (each step marked *proven* /
  *residual* / *proven up to X* with its Lean anchor), then an assumptions section.
- **Keep the honesty formula**: claim → mechanism (with anchors) → one caveat → hypotheses named.
  On hypothesis-heavy capstones, close with a "Named assumptions: …" ledger mapping prose to the
  binders (`hFS`, `hquot`, `hgood`, `hencodes`); on smaller theorems, naming each binder once in
  the text is enough (short by default).
- **The last-notch polish — every pass ends with it.** After the rules are satisfied and before
  the verification gates, one dedicated sweep re-reads every touched docstring with a single
  goal: simpler prose — shorter sentences, fewer clauses, plainer words. Applying it inline
  while restructuring does not count; the sweep is its own final step. It removes what the rules
  don't name: scaffolding openers ("This is the structural fact that…", "Note that…"), tails
  that restate the lead, double statements of one fact ("injective — vectors with equal
  commitments are equal, i.e. linearly independent" → pick one), formula parentheticals that
  restate the displayed Lean statement, and arrow glyphs between prose nouns ("the grand-product
  ⟹ multiset step" → words). Provenance survives as a trailing clause, not its own sentence;
  fully-qualified `Zcash.Snark.…` paths shorten to the unambiguous tail in declaration
  docstrings (module docstrings may keep full paths as cross-module links).
- **Don't churn clean docstrings.** If it already leads with the claim and is concise, leave it
  (e.g. the Vesta order lemmas). The diff should only touch what the convention improves.
- **Reference Lean code, not Lean mechanism.** Name the defs and lemmas a claim is about, but not
  the tactic or kernel machinery that discharges it (`native_decide`, `decide`, `simp`,
  `Classical.choice`): the reader wants the established fact and its scope, not how Lean checked
  it — surface a mechanism only when it *is* the claim's content. Verbose mechanism-laden caveats
  then collapse to one reader-facing clause — the fingerprint glossary entry reads "checked equal
  to the Rust verifier's captured MSM, for the specific circuit under analysis", not "a
  `native_decide` match on one selected fixture, an empirical anchor rather than a universal
  equivalence, with the fixture's group bases opaque tags".
- Match repo prose style: ~100-char wrap, en dashes, `Fiat–Shamir`, backticked Lean anchors.

## Docs-only discipline and the adherence audit

Every pass is comments/prose only — zero proof-term changes. The last-notch polish sweep (above)
is the pass's final editing step; only then verify before handing over:

1. **Prose-only diff** — strip comments (`--` lines and nested `/- … -/` blocks) from `HEAD` and
   working versions; the code must be byte-identical. An unbalanced docstring terminator swallows
   code and fails the check, so this also catches splice errors.

   ```sh
   strip() { python3 -c '
   import sys
   s = sys.stdin.read(); out = []; i = 0; d = 0
   while i < len(s):
       if d == 0 and s.startswith("--", i): j = s.find("\n", i); i = len(s) if j < 0 else j
       elif s.startswith("/-", i): d += 1; i += 2
       elif d > 0 and s.startswith("-/", i): d -= 1; i += 2
       elif d > 0: i += 1
       else: out.append(s[i]); i += 1
   print("\n".join(l.rstrip() for l in "".join(out).split("\n") if l.strip()))'; }
   git diff --name-only -- '*.lean' | while IFS= read -r f; do
     diff <(git show "HEAD:$f" | strip) <(strip < "$f") > /dev/null || echo "FAIL: $f"
   done
   ```
2. `typos <files>` — the repo runs the typos checker (`_typos.toml`).
3. `lake build Zcash` — docstrings are syntax; the build is the parse gate.

To audit the whole tree for adherence (after a pass, before a docs PR, when new proof files
land), sweep every `.lean` file under `Zcash/`, skipping auto-generated files (header says "Do
not edit by hand"):

- **No blanket passes.** The verdict for an unmodified file is a per-docstring justification
  ("all ≤ 4 lines, formula-led, anchors present"), never "looks fine". Well-organised prose is
  not exempt from the rule to introduce before use.
- **Verdicts expire when rules change.** A docstring that passed under an earlier rule set has
  not passed now: every rule added or recalibrated re-opens all previous "compliant" and "keep"
  verdicts, and the next sweep re-judges them against the current rules — an early keep is the
  easiest place for a violation to hide through later sweeps.
- **Close the loop on planned fixes.** A drafted fix is not an applied fix: after each batch,
  re-grep the targets and confirm every planned edit actually landed. Batches get interrupted
  and edits fail on stale text; an unapplied fix silently inherits its old verdict.
- **No author exemption.** Exemplar files and other contributors' prose get the same
  per-docstring judgment as everything else — "written by the style's author" is not a verdict,
  and deference is a named bias, not a reason to skip.
- **Module narrative vs declaration docstrings.** Check each module docstring against the
  declarations below it: the module narrates the shape; the declarations own the detail. A
  module sentence that retells a declaration's docstring — its caveat, its citation, its
  mechanism — becomes a pointer.
- **Mechanical red-flag greps** — fix every hit or record why it stands:
  - private numbering: `grep -rn '§[0-9]\|Step [0-9]'` (allowed: `§` + a section title, and
    public spec sections like §4.13);
  - stale process-prose: `grep -rn 'will follow\|next phase\|the next step\|is the remaining\|filled in incrementally'`
    — for each hit, check whether the "pending" thing now exists in the tree;
  - dash style: `grep -rn -- '[a-zA-Z\`]—[a-zA-Z\`]'` (an em-dash with no space on either side)
    and `grep -rn 'Fiat-Shamir'` (hyphen; house style is the en dash, `Fiat–Shamir`). The spaced
    style for en dashes (`word — word`) is accepted; for asides, either the spaced or enclosing
    style (`word —aside— word`) may be used, and the tree mixes them by author;
  - coined-term chains in prose: `grep -rn ' → .*kernel\| → .*bridge'`.
- **Per-docstring checklist**, reading each file top to bottom: the rules above, with staleness
  checked against the current tree rather than the docstring's own claims.
- **Fix or flag.** Violations with an obvious fix are fixed; anything needing author judgment is
  flagged, not guessed.
- **Report** per file: `fixed (what)` / `compliant (why, per docstring group)` /
  `flagged (needs author input)`.