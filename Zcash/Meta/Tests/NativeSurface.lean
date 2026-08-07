import Zcash.Meta.AxiomCheck

/-!
# Regression tests for the native-certificate evaluated surface

A `native_decide` auxiliary axiom asserts that the compiler's evaluation of a closed `Bool` term is
the kernel's. `partial def` breaks the premise: the kernel constant is `opaque` with no body, and
what the compiler runs in its place is an `unsafe` implementation with the termination check lifted.
A certificate over such a constant therefore says nothing about anything the kernel could have
checked — and the entry that would launder it is the `assert_axioms` on the certificate, whose own
declaration is clean, so no per-declaration check reaches it.

These declarations live in the test-only library for the same reason as
`Zcash.Meta.Tests.AxiomCheck` and `Zcash.Meta.Tests.CompiledOverride`: the production `Zcash`
import graph must never reach them. This is a module of its own so the closure-wide compiled-body
sweep, which the sibling file deliberately trips, does not mask the checks pinned here.
-/

namespace Zcash.Meta.Tests.NativeSurface

/-! ## The honest shape

A certificate over ordinary `def` data passes, so the rejections below are not vacuous and the
check is not simply refusing every `+native` entry. -/

def honestCaptured : List Nat := [1, 2, 3]

theorem honestMatch : honestCaptured = [1, 2, 3] := by native_decide

assert_axioms Zcash.Meta.Tests.NativeSurface.honestMatch +native(
  Zcash.Meta.Tests.NativeSurface.honestMatch)

/-! ## `partial` data under a certificate

`capturedPartial` needs a parameter only because `partial` requires a function type; the compiled
body still ignores it and returns the attacker's list. The kernel cannot confirm the certificate,
and — unlike the `@[implemented_by]` bypass, where the kernel value refutes the compiled one — it
cannot refute it either, because there is no kernel value at all. -/

partial def capturedPartial (_ : Unit) : List Nat :=
  if 0 = 0 then [9, 9, 9] else capturedPartial ()

def target : List Nat := [9, 9, 9]

theorem partialMatch : capturedPartial () = target := by native_decide

/-- error: Zcash.Meta.Tests.NativeSurface.partialMatch: the native_decide certificate evaluated the `partial` declaration(s) [Zcash.Meta.Tests.NativeSurface.capturedPartial], whose compiled body is an unsafe implementation the kernel never sees and whose kernel constant has no body at all. Nothing relates what ran to what the certificate says. Give the evaluated data an ordinary `def`. -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.NativeSurface.partialMatch +native(
  Zcash.Meta.Tests.NativeSurface.partialMatch)

/-! The data itself was already rejected — a `partial def` is not a `def` — which is what makes the
certificate entry the one that has to catch this. Pinned so the two halves stay distinguishable. -/

/-- error: Zcash.Meta.Tests.NativeSurface.capturedPartial is not a def -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.NativeSurface.capturedPartial

/-! ## A sealed `opaque` is not reported

The reduction-barrier idiom this repository uses (`Zcash.Circuits.Action.TopLevel.actionCircuit`,
`Zcash.Circuits.Integration.ActionGateCoherence.configureHandle`): the opaque's *type* carries the
equation to its source, so the kernel can recover the value, and its compiled body is the declared
one. The certificate below is therefore honest, and the check leaves it alone. -/

def sealedSource : List Nat := [1, 2, 3]

opaque sealed : { xs : List Nat // xs = sealedSource } := ⟨sealedSource, rfl⟩

theorem sealedMatch : sealed.val = [1, 2, 3] := by rw [sealed.property]; native_decide

assert_axioms Zcash.Meta.Tests.NativeSurface.sealedMatch +native(
  Zcash.Meta.Tests.NativeSurface.sealedMatch)

/-! ## `partial` behind a `@[csimp]` replacement

The auxiliary axiom records the term as the *kernel* sees it, and `@[csimp]` replaces a constant
wholesale in compiled code — so the certificate below runs `csimpFast` where its own statement says
`csimpSlow`, and a walk of the statement alone would never reach `hiddenBehindCsimp`. This is not a
hypothetical routing: `Zcash.Arithmetic.FastMsm` redirects the fixtures' MSM hot path exactly this
way, so the replacement target's cone is where a `partial` would sit unnoticed.

The csimp lemma stays at the end of the file: a replacement applies to code compiled after it, and
the honest certificates above must be elaborated without it to keep their own coverage meaningful. -/

partial def hiddenBehindCsimp (_ : Unit) : Nat := hiddenBehindCsimp ()

def csimpSlow (n : Nat) : Nat := n

/-- Equal to `csimpSlow` — the `partial` call sits in an argument the body discards, which is what
lets the replacement be *proved* while still putting `hiddenBehindCsimp` in the compiled cone. -/
def csimpFast (n : Nat) : Nat := (fun _ => n) (hiddenBehindCsimp ())

@[csimp] theorem csimpSlow_eq_csimpFast : @csimpSlow = @csimpFast := by
  funext n; rfl

assert_axioms Zcash.Meta.Tests.NativeSurface.csimpSlow_eq_csimpFast

theorem csimpCert : csimpSlow 7 = 7 := by native_decide

/-- error: Zcash.Meta.Tests.NativeSurface.csimpCert: the native_decide certificate evaluated the `partial` declaration(s) [Zcash.Meta.Tests.NativeSurface.hiddenBehindCsimp], whose compiled body is an unsafe implementation the kernel never sees and whose kernel constant has no body at all. Nothing relates what ran to what the certificate says. Give the evaluated data an ordinary `def`. -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.NativeSurface.csimpCert +native(
  Zcash.Meta.Tests.NativeSurface.csimpCert)

end Zcash.Meta.Tests.NativeSurface
