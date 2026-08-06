import Zcash.Meta.AxiomCheck

/-!
# Regression tests for `Zcash.Meta.AxiomCheck`

Two rejection families. The native-axiom provenance cases deliberately impersonate Lean's
`native_decide` auxiliaries: most declare an axiom named like an auxiliary, and one instead names a
*theorem* so that its own genuine auxiliary imitates the marker path. The `assert_computable` cases
pin the declaration checks that stand behind "the reduction data is genuinely computed". Both live
in this test-only library so the production `Zcash` library never imports them.
-/

namespace Zcash.Meta.Tests.AxiomCheck

namespace Genuine

theorem owner : (123456 : Nat) < 123457 := by native_decide

assert_axioms Zcash.Meta.Tests.AxiomCheck.Genuine.owner +native(
  Zcash.Meta.Tests.AxiomCheck.Genuine.owner)

end Genuine

namespace GenuineAutoParam

/-- The certificate lives in an auto-param, so the axiom is emitted while elaborating the
structure instance below rather than a tactic block of its own. Lean then records the auxiliary's
end position at the start of the *next* token — past the end of the owning declaration — which is
why ownership is decided by the auxiliary's start position. `CompElliptic`'s Tonelli–Shanks data
(`pallasBase`, `vestaBase`) is the census entry with this shape. -/
structure Certified where
  value : Nat
  small : value < 123457 := by native_decide

def owner : Certified where
  value := 123456

assert_axioms Zcash.Meta.Tests.AxiomCheck.GenuineAutoParam.owner +native(
  Zcash.Meta.Tests.AxiomCheck.GenuineAutoParam.owner)

end GenuineAutoParam

namespace NonexistentOwner

axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: Unknown constant `Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.owner` -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.owner)

end NonexistentOwner

namespace UnrelatedOwner

theorem owner : True := True.intro
axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.target: '+native' names 'Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.owner', but that declaration owns no native_decide axiom -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.owner)

end UnrelatedOwner

namespace ForgedDependency

axiom owner._native.native_decide.ax_1_1 : False
theorem owner : False := owner._native.native_decide.ax_1_1

/-- error: 'Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner +native(
  Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner)

end ForgedDependency

namespace MacroForged

/-! The forgery `ForgedDependency` cannot express. A top-level `axiom` command is necessarily its
own command, so its start lands *before* the owner's — which is what makes that case detectable.
Macro expansion removes exactly that tell: every declaration a macro emits inherits the macro
*invocation site* as its declaration range, so the axiom and the theorem using it share one
identical range. A non-strict start comparison accepts that automatically, and the census would
then certify an arbitrary axiom — here `False` — as a `native_decide` compiler-trust certificate.
`rangeStartsInside` therefore requires the auxiliary to start *strictly* after the owner, which no
macro-emitted sibling can do while both genuine shapes (`Genuine`, `GenuineAutoParam`) still can. -/

macro "forge " n:ident " : " t:term : command =>
  `(axiom $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)) : $t
    theorem $n : $t := $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)))

forge owner : False

/-- error: 'Zcash.Meta.Tests.AxiomCheck.MacroForged.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'Zcash.Meta.Tests.AxiomCheck.MacroForged.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.MacroForged.owner +native(
  Zcash.Meta.Tests.AxiomCheck.MacroForged.owner)

end MacroForged

namespace SecondCertificate

/-! Two genuine certificates in one cone. The allowance compares the exact *set* of native axioms
reached against the set the named owners actually own, so an annotation that names only the first
owner goes stale the moment a second certificate enters the cone. Comparing owner sets alone would
not suffice: distinct axioms can share an owner name (see `AliasedOwner`). -/

theorem first : (234567 : Nat) < 234568 := by native_decide

theorem second : (345678 : Nat) < 345679 := by native_decide

theorem target : (234567 : Nat) < 234568 ∧ (345678 : Nat) < 345679 := ⟨first, second⟩

/-- error: Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target: '+native' names [Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first] but the native_decide axiom(s) present are owned by [Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first, Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second]; write '+native(Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first, Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second)' -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target +native(
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first)

assert_axioms Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target +native(
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first,
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second)

end SecondCertificate

namespace AliasedOwner

/-! A certifying declaration whose *own* name contains the marker components. Its auxiliary is
`owner.native_decide.smuggled._native.native_decide.ax_1_1`, so reading ownership off the prefix
before the *first* `_native`/`native_decide` component would credit it to `owner` — collapsing it
onto the legitimate certificate, where a pre-existing `+native(owner)` would cover both and admit
an undisclosed compiler-trust dependency. Ownership is decided by the *last* marker instead, so the
smuggled certificate keeps its own owner and the stale annotation fails the build. -/

theorem owner : (456789 : Nat) < 456790 := by native_decide

namespace owner.native_decide

theorem smuggled : (567890 : Nat) < 567891 := by native_decide

end owner.native_decide

theorem target : (456789 : Nat) < 456790 ∧ (567890 : Nat) < 567891 :=
  ⟨owner, owner.native_decide.smuggled⟩

/-- error: Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target: '+native' names [Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner] but the native_decide axiom(s) present are owned by [Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner, Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled]; write '+native(Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner, Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)' -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner)

/-! The disclosure the census demands: the smuggled certificate is attributed to its own
declaration, not aliased onto `owner`. -/
assert_axioms Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner,
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)

end AliasedOwner

namespace ComputableSafety

/-! The `assert_computable` declaration checks. `unsafe` lifts the termination check, so the
reduction below inhabits `False` by bare self-reference while computing nothing — and it is a
`.defnInfo` that is not `noncomputable`, so the kind and computability checks both pass it. Only
the definition-safety check rejects it. The kernel independently refuses to let a safe declaration
depend on an unsafe one, so what the check has to catch is a reduction no safe proof consumes:
precisely a deliverable endpoint, which the census pins directly for that same reason. -/

unsafe def unsafeReduction : False := unsafeReduction

/-- error: Zcash.Meta.Tests.AxiomCheck.ComputableSafety.unsafeReduction is marked unsafe -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.ComputableSafety.unsafeReduction

/-! `partial def` elaborates to an `opaque` constant carrying an unsafe implementation, so it is
rejected one check earlier — as not a `def` at all. Pinned so a toolchain that instead emits a
`.defnInfo` with `partial` safety is caught by the safety check rather than passing silently. -/

partial def partialReduction (n : Nat) : Nat :=
  if n = 0 then 0 else partialReduction (n - 1)

/-- error: Zcash.Meta.Tests.AxiomCheck.ComputableSafety.partialReduction is not a def -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.ComputableSafety.partialReduction

/-! The positive case, so the rejections above are not passing vacuously. -/

def safeReduction (n : Nat) : Nat := n + 1

assert_computable Zcash.Meta.Tests.AxiomCheck.ComputableSafety.safeReduction

end ComputableSafety

namespace UnneededChoice

/-! An over-broad `+choice` is rejected: the flag on a reduction that never reaches
`Classical.choice` would silently over-state the trusted base, mirroring how a stale
`+native` owner list is rejected. The choice-free reduction is the positive case's shape. -/

def choiceFreeReduction (n : Nat) : Nat := n + 1

/-- error: Zcash.Meta.Tests.AxiomCheck.UnneededChoice.choiceFreeReduction does not depend on Classical.choice; drop the '+choice' flag -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.UnneededChoice.choiceFreeReduction +choice

/-! The genuine-`+choice` positive case: choice entering through an erased `Prop` field. -/

def choiceUsingReduction (n : Nat) : { m : Nat // ∃ k, m = n + k } :=
  ⟨n + 1, Classical.choice ⟨⟨1, rfl⟩⟩⟩

assert_computable Zcash.Meta.Tests.AxiomCheck.UnneededChoice.choiceUsingReduction +choice

end UnneededChoice

namespace CompiledOverrides

/-! `implemented_by`, `extern`, and `csimp` alter native execution without entering the logical
dependency or axiom graph.  Check the whole Ironwood dependency cone, not only the pinned
declaration: the forgeries sit one helper below the otherwise ordinary endpoint. -/

unsafe def dishonestImplementation (n : Nat) : Nat := n + 2

@[implemented_by dishonestImplementation]
def implementedHelper (n : Nat) : Nat := n + 1

def throughImplementedBy (n : Nat) : Nat := implementedHelper n

/-- error: Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughImplementedBy reaches unchecked compiled replacement(s): Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.implementedHelper @[implemented_by Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.dishonestImplementation] -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughImplementedBy

@[extern "ironwood_axiom_check_extern_helper"]
def externHelper (n : Nat) : Nat := n + 1

def throughExtern (n : Nat) : Nat := externHelper n

/-- error: Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughExtern reaches unchecked compiled replacement(s): Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.externHelper @[extern] -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughExtern

/-! A `private` helper's environment name carries the `_private.<module>.0.` prefix, so a scope
test on the raw name would wave its replacement through.  The check must normalize through
`privateToUserName?`. -/

unsafe def dishonestPrivateImplementation (n : Nat) : Nat := n + 4

@[implemented_by dishonestPrivateImplementation]
private def privateImplementedHelper (n : Nat) : Nat := n + 1

def throughPrivateImplementedBy (n : Nat) : Nat := privateImplementedHelper n

/-- error: Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughPrivateImplementedBy reaches unchecked compiled replacement(s): Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.privateImplementedHelper @[implemented_by Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.dishonestPrivateImplementation] -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughPrivateImplementedBy

/-! `@[csimp]` substitutes compiled code on the strength of its equation theorem.  An equation
resting on a bespoke axiom is an unchecked substitution wearing a proof's clothes; one resting on
the standard axioms is the sanctioned mechanism and must keep passing. -/

def csimpVictim (n : Nat) : Nat := n + 1

def csimpDishonest (n : Nat) : Nat := n + 2

axiom forgedCsimpEq : @csimpVictim = @csimpDishonest

@[csimp] theorem csimpVictim_eq_dishonest : @csimpVictim = @csimpDishonest := forgedCsimpEq

def throughForgedCsimp (n : Nat) : Nat := csimpVictim n

/-- error: Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughForgedCsimp reaches the csimp replacement of Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.csimpVictim, whose equation Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.csimpVictim_eq_dishonest depends on unexpected axiom(s): [Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.forgedCsimpEq] -/
#guard_msgs (whitespace := lax) in
assert_computable Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughForgedCsimp

def csimpHonestSlow (n : Nat) : Nat := n + 1

def csimpHonestFast (n : Nat) : Nat := n + 1

@[csimp] theorem csimpHonestSlow_eq_fast : @csimpHonestSlow = @csimpHonestFast := rfl

def throughHonestCsimp (n : Nat) : Nat := csimpHonestSlow n

assert_computable Zcash.Meta.Tests.AxiomCheck.CompiledOverrides.throughHonestCsimp

end CompiledOverrides

end Zcash.Meta.Tests.AxiomCheck
