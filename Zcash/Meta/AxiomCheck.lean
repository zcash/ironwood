import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command
import Lean.DeclarationRange
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Mathlib.Util.AssertNoSorry

/-!
# `assert_axioms` — a concise, build-checked trust-boundary bound

A sibling of Mathlib's `assert_no_sorry` (same `collectAxioms` machinery) that asserts an *upper
bound* on a declaration's trusted base. Unlike a `#guard_msgs`-pinned `#print axioms`, it does not
hard-code the pretty-printed axiom list, so it stays green across toolchain bumps that rename the
`native_decide` axiom — while still failing the build the moment a declaration reaches beyond its
declared tier (a `sorry`, an unexpected axiom, or `native_decide` where none was permitted).

The `#guard_msgs`-pinned form remains the right tool when the *exact* axiom set is the claim.

Scope: these commands catch *inadvertent* drift — an entry silently reaching more than it
claims. They are not a full defense against a deliberately deceptive author. The provenance
check (`rangeStartsInside`) does reject the cheapest deliberate attack, a macro that emits an
auxiliary-named `axiom` alongside the theorem using it; what it cannot reject is code that
manipulates declaration ranges outright (`Lean.addDeclarationRanges` under `run_cmd`), which has
no innocuous reading in a diff. Treat any declaration-emitting metaprogram entering this
repository as census-relevant on review.

Both commands require their argument to be written fully qualified (`checkFullyQualified`):
an unqualified name resolves through the census file's `open`s, so a same-base-name cousin in
an opened namespace can silently capture an entry meant for a declaration that is not in scope
at all — the assertion then reads as covering one theorem while checking another.

CompElliptic has a sibling `CompElliptic/Meta/AxiomCheck.lean`, but the two have diverged: this
version is a strict superset, adding the `+native(D₁, …)` owner list (upstream takes a bare
`+native`, so it cannot state *which* certificate it trusts), the marker parsing and
owner/module/range provenance checks, `checkFullyQualified`, the exact-set staleness check, the
`assert_computable` definition-safety check, and the negative regression suite. Ironwood re-checks
every inherited axiom itself, so the census here
does not depend on the upstream version's strength; porting this file upstream is tracked
separately. Improvements made here should be considered for upstream, not assumed present there.
-/

open Lean Elab Command

namespace Zcash.Meta

/-- The standard axioms of Lean's trusted base — the whole budget for a general theorem. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a declaration belongs to Ironwood rather than the ambient Lean/Mathlib runtime.

The latter deliberately contains trusted `@[extern]` and `@[implemented_by]` primitives.  What
`assert_computable` forbids is adding the same unchecked compiled replacement anywhere in the
Ironwood dependency cone while continuing to advertise the endpoint as computed by its checked
Lean body. -/
def isIronwoodName (n : Name) : Bool :=
  n == `Zcash || n.toString.startsWith "Zcash."

/-- Every unchecked compiled replacement in the transitive Ironwood dependency cone of `root`.

`implemented_by` implementations are not logical dependencies: the compiler silently substitutes
them after elaboration.  Likewise an `extern` declaration's Lean body is what the kernel sees, not
what native execution calls.  Consequently neither replacement can be discovered by
`collectAxioms`; inspect the compiler attribute tables while walking the ordinary dependency cone.
Ambient Lean/Mathlib replacements remain part of the explicitly accepted compiler/runtime TCB. -/
def ironwoodCompiledOverrides (root : Name) : CommandElabM (Array String) := do
  let env ← getEnv
  let mut todo : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut found : Array String := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    let some info := env.find? name | continue
    if isIronwoodName name then
      if let some implementation := Compiler.getImplementedBy? env name then
        found := found.push s!"{name} @[implemented_by {implementation}]"
      if Lean.isExtern env name then
        found := found.push s!"{name} @[extern]"
    for dep in info.getUsedConstantsAsSet do
      if !seen.contains dep then
        todo := todo.push dep
  return found.qsort fun a b => a < b

/-- The declaration an alleged `native_decide` axiom names as its owner. The compiler-generated
name has an `_native.native_decide` marker after the owning declaration; only the tail after that
marker is toolchain-dependent. Taking the last marker also handles an owner whose own name contains
those components. -/
def nativeAxiomOwner? (ax : Name) : Option Name :=
  let rec go (prefixRev rest : List Name) (ownerRev? : Option (List Name)) : Option Name :=
    match rest with
    | a :: b :: tail =>
      let ownerRev? := if a == `_native && b == `native_decide then some prefixRev else ownerRev?
      go (a :: prefixRev) (b :: tail) ownerRev?
    | _ => ownerRev?.map fun ownerRev =>
      ownerRev.reverse.foldl Name.append Name.anonymous
  go [] ax.components none

/-- A syntactically plausible `native_decide` auxiliary axiom. `checkNativeAllowance` additionally
checks its owner, dependency, module, and source range before permitting it. -/
def isNativeDecideAxiom (n : Name) : Bool :=
  (nativeAxiomOwner? n).isSome

/-- Assertion names must be written fully qualified. Resolution through `open`s is
context-dependent: a same-base-name cousin in an opened namespace can silently capture an
entry meant for a declaration that is not even in scope, so the assertion reads as covering
one theorem while checking another. Requiring the written name to equal the resolved
constant's full name (an optional `_root_.` prefix is accepted) makes every entry
independent of the file's `open`s and turns the wrong-cousin case into a loud error. -/
def checkFullyQualified (n : Syntax) (resolved : Name) : CommandElabM Unit := do
  let written := n.getId
  unless written == resolved || written == rootNamespace ++ resolved do
    throwError "{n} is not written fully qualified: it resolves to '{resolved}'. \
      Write the full name so the entry does not depend on this file's `open`s."

/-- Render a list of owners as the text to write inside `+native(...)`. -/
def ownersText (owners : List Name) : String :=
  ", ".intercalate (owners.map toString)

/-- Lexicographic source-position comparison. -/
def positionLE (a b : Position) : Bool :=
  decide (a.line < b.line ∨ (a.line = b.line ∧ a.column ≤ b.column))

/-- Strict lexicographic source-position comparison. -/
def positionLT (a b : Position) : Bool :=
  decide (a.line < b.line ∨ (a.line = b.line ∧ a.column < b.column))

/-- Whether `inner` *starts* strictly inside `outer`. Only the start position is compared against
the owner's end: Lean records an auxiliary's end position at the start of the next token, so it
runs past the end of the declaration that emitted it whenever the emitting syntax is followed by
whitespace or a comment — the shape a `native_decide` auto-param discharged inside a structure
instance always has. The start is still a faithful witness of where the auxiliary was elaborated,
and that is all the check needs: a hand-written `axiom` is a top-level command of its own, and one
the owner depends on must be declared before the owner, so its start never lands inside the owner's
range.

The leading comparison is **strict**, and the strictness is load-bearing. A declaration produced by
macro expansion inherits the macro *invocation site* as its declaration range, so a macro emitting
both an `axiom` named like an auxiliary and a theorem using it gives the two identical ranges —
which satisfies a non-strict test automatically, laundering an arbitrary axiom (up to `False`) past
the census as a compiler-trust certificate. `Zcash.Meta.Tests.AxiomCheck.MacroForged` pins the
rejection. A genuine auxiliary is always emitted by elaborating syntax *within* the owner's
declaration — a tactic in its proof body, or an auto-param inside a structure instance — so in both
shapes its start is strictly after the owner's first token. -/
def rangeStartsInside (outer inner : DeclarationRange) : Bool :=
  positionLT outer.pos inner.pos && positionLE inner.pos outer.endPos

/-- The `native_decide` axioms genuinely owned by `owner`: each must occur in the owner's own
transitive axiom footprint, have the compiler-generated owner prefix, come from the same module,
and start inside the owner's declaration. The range condition distinguishes an auxiliary emitted
while elaborating the owner from an arbitrary axiom merely given the same name. -/
def nativeAxiomsOwnedBy (owner : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let ownerAxioms ← collectAxioms owner
  let alleged := ownerAxioms.filter fun ax => nativeAxiomOwner? ax == some owner
  let mut owned := #[]
  for ax in alleged do
    let sameModule := env.getModuleIdxFor? owner == env.getModuleIdxFor? ax
    let ownerRanges? ← findDeclarationRanges? owner
    let axRanges? ← findDeclarationRanges? ax
    let rangeValid := match ownerRanges?, axRanges? with
      | some ownerRanges, some axRanges => rangeStartsInside ownerRanges.range axRanges.range
      | _, _ => false
    unless sameModule && rangeValid do
      throwError "'{ax}' looks like a native_decide axiom owned by '{owner}', but it was not \
        emitted inside that declaration"
    owned := owned.push ax
  return owned

/-- `+native` must name the owning declaration(s) of exactly the `native_decide` axioms the
entry actually reaches, fully qualified. A bare `+native` would permit a `native_decide`
axiom brought in by *any* declaration entering the dependency cone; naming the owners makes
the census state precisely which native certificates are trusted, and a new native axiom —
or a stale annotation — fails the build with the list to write. -/
def checkNativeAllowance (n : Ident) (axs : Array Name) (allowed : Option (Array Name)) :
    CommandElabM Unit := do
  let nativeAxioms := axs.filter isNativeDecideAxiom
  let owners := (nativeAxioms.filterMap nativeAxiomOwner?).toList.eraseDups
  match allowed with
  | none =>
    unless owners.isEmpty do
      throwError "{n} depends on native_decide axiom(s); name their owning declaration(s): \
        write '+native({ownersText owners})'"
  | some allowedArr =>
    let allowedL := allowedArr.toList.eraseDups
    if owners.isEmpty then
      throwError "{n} reaches no native_decide axiom; drop the '+native(...)' flag"
    let mut permitted := #[]
    for owner in allowedL do
      let owned ← nativeAxiomsOwnedBy owner
      if owned.isEmpty then
        throwError "{n}: '+native' names '{owner}', but that declaration owns no \
          native_decide axiom"
      permitted := permitted.append owned
    let presentL := nativeAxioms.toList.eraseDups
    let permittedL := permitted.toList.eraseDups
    unless presentL.all permittedL.contains && permittedL.all presentL.contains do
      throwError "{n}: '+native' names {allowedL} but the native_decide axiom(s) present \
        are owned by {owners}; write '+native({ownersText owners})'"

/-- The `+native(A, B)` flag: the parenthesized, comma-separated owner list is required. -/
syntax nativeFlag := "+native" "(" ident,+ ")"

/-- Extract the identifiers from an optional `+native(A, B)` flag. -/
def nativeAnnotation (native : Option (TSyntax ``nativeFlag)) : Option (Array Ident) :=
  native.map fun stx => stx.raw[2].getSepArgs.map fun arg => ⟨arg⟩

/-- Resolve and fully qualify every owner named by `+native`. Besides preventing namespace
capture, resolution rejects an annotation that names a nonexistent owner whose text happens
to prefix an arbitrary axiom. -/
def resolveNativeAnnotation (native : Option (TSyntax ``nativeFlag)) :
    CommandElabM (Option (Array Name)) := do
  let some ids := nativeAnnotation native | return none
  let names ← ids.mapM fun id => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    checkFullyQualified id name
    return name
  return some names

/--
`assert_axioms foo` fails the build unless `foo` depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular, no `sorry` and no `native_decide`.

`assert_axioms foo +native(D₁, ...)` additionally permits `native_decide` compiler-trust axioms —
exactly those owned by the named declarations, written fully qualified. The axiom names' tails are
toolchain-dependent, so entries name the owning declarations rather than the axioms themselves.
Any other axiom (including `sorryAx`) is still rejected, as is a stale or incomplete list.
-/
elab "assert_axioms " n:ident native:(nativeFlag)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  checkFullyQualified n name
  let axs ← collectAxioms name
  let allowed ← resolveNativeAnnotation native
  checkNativeAllowance n axs allowed
  let unexpected := axs.filter fun ax =>
    !standardAxioms.contains ax && !(allowed.isSome && isNativeDecideAxiom ax)
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

/--
`assert_computable foo` fails the build unless `foo` is a plain `def` — an actual definition,
marked neither `unsafe`/`partial` nor `noncomputable` — depending on no axioms beyond
`propext` / `Quot.sound`. This is the breaks-as-computed-data check: the data is genuinely
computed, and with `Classical.choice` excluded it cannot have been conjured from mere
propositional existence even in erased positions. Its transitive Ironwood dependency cone must
also contain no `@[extern]` or `@[implemented_by]` declaration: either attribute can make native
execution ignore the kernel-checked Lean body without changing the logical axiom footprint.

`assert_computable foo +choice` additionally permits `Classical.choice`. Together with the
plain-`def` check this asserts choice enters only through erased `Prop` fields: had it touched the
data, the definition could not have compiled as a plain `def`. `+native(D₁, ...)` likewise permits
the named declarations' `native_decide` compiler-trust axioms.

Declaring `+choice` when `foo` does not actually reach `Classical.choice` fails the build (drop the
flag), as an over-broad `+native` does: the census states exactly the trust assumed, nothing more.

The plain-`def` check guards a gap in "computability is compiler-enforced": marking a reduction
`noncomputable` later would still build, silently voiding the convention; this assertion catches
it. The definition-safety check closes the same gap from the other side. An `unsafe` def is a
`.defnInfo` like any other and is not `noncomputable`, so neither the kind check nor
`isNoncomputable` sees it — yet `unsafe` lifts the termination check, so such a definition can
inhabit its result type by bare self-reference (`unsafe def r : Break := r`) while computing
nothing. The kernel does refuse to let a safe declaration depend on an unsafe one, which confines
the forgery to a reduction no safe proof consumes; that is exactly the shape of a deliverable
endpoint reduction, which is why the assertion checks safety itself rather than leaning on the
kernel. `Zcash.Meta.Tests.AxiomCheck.ComputableSafety` pins the rejection.
-/
elab "assert_computable " n:ident choice:("+choice")? native:(nativeFlag)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  checkFullyQualified n name
  let env ← getEnv
  let .defnInfo val ← liftCoreM <| getConstInfo name
    | throwError "{n} is not a def"
  match val.safety with
  | .safe => pure ()
  | .unsafe => throwError "{n} is marked unsafe"
  | .partial => throwError "{n} is marked partial"
  if Lean.isNoncomputable env name then
    throwError "{n} is marked noncomputable"
  let compiledOverrides ← ironwoodCompiledOverrides name
  unless compiledOverrides.isEmpty do
    let details := String.intercalate ", " compiledOverrides.toList
    throwError "{n} reaches unchecked compiled replacement(s): {details}"
  let axs ← collectAxioms name
  let allowChoice := choice.isSome
  if allowChoice && !axs.contains ``Classical.choice then
    throwError "{n} does not depend on Classical.choice; drop the '+choice' flag"
  let allowed ← resolveNativeAnnotation native
  checkNativeAllowance n axs allowed
  let unexpected := axs.filter fun ax =>
    !(ax == ``propext || ax == ``Quot.sound
      || (allowChoice && ax == ``Classical.choice)
      || (allowed.isSome && isNativeDecideAxiom ax))
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

end Zcash.Meta
