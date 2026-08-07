import Zcash.Meta.AxiomCheck

/-!
# Regression tests for the compiled-body-override checks

`@[implemented_by]` and `@[extern]` swap the body the compiler runs while the kernel keeps
reducing the original, and Lean checks no relation between the two. A declaration carrying either
is still a `.safe` `.defnInfo`, is not `noncomputable`, and introduces no axiom, so every other
check in `Zcash.Meta.AxiomCheck` passes it — which is what makes this the one census bypass that
reaches a *value*: the faithfulness fingerprints are `native_decide` proofs, so a doctored capture
makes the certificate report a match against data the kernel refutes.

The declarations here are deliberately doctored, so they live in this test-only library, out of the
production `Zcash` import graph, alongside the forged axioms of `Zcash.Meta.Tests.AxiomCheck` —
and in a module of their own, because `checkCompiledBodyDisclosure` is a property of the whole
import closure: once an override exists here, every later census entry in this module fails, which
is exactly the third case below but would swamp the unrelated entries of the sibling file.

The order of this file is therefore load-bearing: the clean entries come first, while the module
still has nothing to report.
-/

namespace Zcash.Meta.Tests.CompiledOverride

/-! ## Clean module

Both commands pass while nothing in the closure substitutes a compiled body — so the rejections
below are not passing vacuously, and the disclosure check is not simply always-on. -/

def cleanReduction (n : Nat) : Nat := n + 1

assert_computable Zcash.Meta.Tests.CompiledOverride.cleanReduction

theorem cleanTheorem : (2 : Nat) + 2 = 4 := rfl

assert_axioms Zcash.Meta.Tests.CompiledOverride.cleanTheorem

/-! ## An ambient-package target

The disclosure sweep exempts the toolchain's own overrides — `Nat.add` is `@[extern]`, as are most
of the arithmetic and container primitives whose compiled code every `native_decide` runs
regardless. Censusing one *directly* is a different claim, though: there the substitution is the
entry's own subject rather than background compiler trust, and `assert_computable`'s "genuinely
computed" would be asserted of a body that never runs. The per-declaration check therefore applies
to any target. -/

/-- error: Nat.add carries '@[extern]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable Nat.add

/-! ## The bypass

`capturedData` stands in for a fixture capture: `assert_computable` sees a plain safe `def` whose
axioms are empty, `native_decide` evaluates the *compiled* body and certifies the match, and the
kernel disagrees — `refutesAtKernel` proves the negation of what `fingerprintMatch` proves, both
about the same constant. Every check that predates this file accepts the pair. -/

def honestCaptured : List Nat := [1, 2, 3]

unsafe def doctoredImpl : List Nat := [9, 9, 9]

@[implemented_by doctoredImpl] def capturedData : List Nat := honestCaptured

def target : List Nat := [9, 9, 9]

theorem fingerprintMatch : capturedData = target := by native_decide

theorem refutesAtKernel : capturedData ≠ target := by decide

/-- error: Zcash.Meta.Tests.CompiledOverride.capturedData carries '@[implemented_by]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.CompiledOverride.capturedData

/-! ## The certificate that consumes it

Pinning the doctored data is only half the bypass: the entry that actually launders it is the
`assert_axioms` on the `native_decide` certificate, whose own declaration is clean. What that entry
reaches is a compiled body, which no axiom footprint records — so it is caught by the closure-wide
disclosure check, naming the declaration responsible. -/

/-- error: Zcash.Meta.Tests.CompiledOverride.fingerprintMatch cannot be censused: Zcash.Meta.Tests.CompiledOverride.capturedData (@[implemented_by]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. Use the proven-equality `@[csimp]` instead, or — if the substitution really belongs in the trusted base — disclose it in `Zcash.TrustBoundary` and add it to `Zcash.Meta.allowedCompiledBodyOverrides`. -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.CompiledOverride.fingerprintMatch +native(
  Zcash.Meta.Tests.CompiledOverride.fingerprintMatch)

/-! An entry with no connection at all to the doctored declaration fails too. The census states the
artifact's trusted base, and an unchecked compiled body inside it is undisclosed compiler trust
wherever it sits; scoping the check to each entry's dependency cone would let the same commit that
adds the override keep every unrelated entry green. -/

/-- error: Zcash.Meta.Tests.CompiledOverride.honestCaptured cannot be censused: Zcash.Meta.Tests.CompiledOverride.capturedData (@[implemented_by]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. Use the proven-equality `@[csimp]` instead, or — if the substitution really belongs in the trusted base — disclose it in `Zcash.TrustBoundary` and add it to `Zcash.Meta.allowedCompiledBodyOverrides`. -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.CompiledOverride.honestCaptured

/-! ## `@[extern]`

The same swap without an `unsafe` helper: the compiled body becomes a foreign symbol, about which
nothing at all is known. Both checks report it exactly as they report `@[implemented_by]`. -/

@[extern "zcash_meta_tests_doctored_symbol"] def externData : List Nat := honestCaptured

/-- error: Zcash.Meta.Tests.CompiledOverride.externData carries '@[extern]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.CompiledOverride.externData

/-- error: Zcash.Meta.Tests.CompiledOverride.cleanTheorem cannot be censused: Zcash.Meta.Tests.CompiledOverride.capturedData (@[implemented_by]), Zcash.Meta.Tests.CompiledOverride.externData (@[extern]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. Use the proven-equality `@[csimp]` instead, or — if the substitution really belongs in the trusted base — disclose it in `Zcash.TrustBoundary` and add it to `Zcash.Meta.allowedCompiledBodyOverrides`. -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.CompiledOverride.cleanTheorem

end Zcash.Meta.Tests.CompiledOverride
