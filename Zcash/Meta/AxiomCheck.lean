import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.DeclarationRange
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Mathlib.Util.AssertNoSorry

/-!
# `assert_axioms` — a concise, build-checked trust-boundary bound

A sibling of Mathlib's `assert_no_sorry` (same `collectAxioms` machinery) that asserts an *upper
bound* on a declaration's trusted base. Unlike a `#guard_msgs`-pinned `#print axioms`, it does not
hard-code the pretty-printed axiom list, so it stays green across toolchain bumps that rename the
`native_decide` axiom — while still failing the build the moment a declaration reaches beyond its
declared tier (a `sorry`, an unexpected axiom, or `native_decide` where none was permitted).

The `#guard_msgs`-pinned form remains the right tool when the *exact* axiom set is the claim.

Both commands also police the *compiled* side of the trusted base: an axiom footprint says nothing
about what compiled code runs, and the fixtures' faithfulness certificates are `native_decide`
proofs that run it. Two sections below cover the two ways compiled behaviour comes apart from kernel
meaning — a substituted body (`@[implemented_by]`, `@[extern]`) and a `partial` declaration inside a
certificate's evaluated term.

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

/-! ## Compiled-body overrides

`@[implemented_by f]` and `@[extern "sym"]` instruct the compiler to run a *different body* than the
one the kernel reduces, and Lean checks no relation between the two (`@[csimp]` is the checked
counterpart: it demands a proof that the replacement equals the original). Neither attribute changes
the safety flag, the `noncomputable` flag, or the axiom footprint, so nothing the rest of this file
inspects can see the substitution: a censused `def` can carry `@[implemented_by doctored]` and
`assert_computable` will still call it genuinely computed data while the executed value is the
attacker's. That matters here because the fixtures' faithfulness certificates are `native_decide`
proofs, which *run the compiled bodies* — a doctored capture makes the certificate report a match
that the kernel value refutes.

The check below is deliberately not cone-scoped. `collectAxioms` no longer walks imported bodies
(it reads a per-module precomputed footprint), so a transitive walk over a fixture's cone would be
the expensive traversal Lean stopped doing — and what it would mostly find is the *ambient* surface:
at the pinned toolchain, `Init`/`Std`/`Lean`/`Mathlib` carry on the order of a thousand of these
attributes between them, all of them compiled code every `native_decide` in existence already runs.
So the census splits the two rather than walking terms. On the ambient surface it claims nothing
new. Outside it, it enumerates *every* override in the import closure, reachable or not: the
attribute extensions are indexed by declaring module, so this is a scan of the module list rather
than of any term, and it catches an override before the commit that puts it in a cone. Stating it
over the whole closure is sound because `ParametricAttribute`'s `add` refuses a declaration from an
imported module (`Lean.Attributes`, `throwAttrDeclInImportedModule`) — a commit can only attach
either attribute inside the module that declares the constant, so every override a commit here can
introduce lives in a module this repository owns, and none of them can hide behind an ambient
root. -/

/-- Package roots whose compiled-body overrides are *ambient*: the Lean toolchain and the pinned
mathlib stack, whose compiled code every `native_decide` runs no matter what this repository does,
and which a commit here cannot add an override to (attributes cannot be attached to an imported
declaration). Everything else is censused, so a *new* dependency fails the build until its root is
classified — a new package in the import closure is a trusted-base change, unlike a version bump of
one already listed. This is where the `@[extern]` `Task.spawn` / `Task.get` reached through
`List.parMap` land; the kernel sees their reference bodies, `List.parMap_eq_map` closes by `rfl`,
and `Zcash.TrustBoundary` discloses what the task runtime widens the compiled surface to. -/
def ambientPackageRoots : Array Name :=
  #[`Init, `Lean, `Std, `Lake, `Batteries, `Mathlib, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Cli]

/-- The attribute substituting `decl`'s compiled body, if any. -/
def compiledBodyOverride? (env : Environment) (decl : Name) : Option Name :=
  if (Lean.Compiler.getImplementedBy? env decl).isSome then some `implemented_by
  else if Lean.isExtern env decl then some `extern
  else none

/-- Compiled-body overrides the census has examined and admitted, each of which must be justified by
a disclosure in `Zcash.TrustBoundary` saying why the substituted body is trusted. Empty: the
repository has none, and `Zcash.Arithmetic.FastMsm` records the convention that the proven-equality
`@[csimp]` is used instead. An entry here is a deliberate widening of the trusted base, so it should
be as hard to add unnoticed as any other census line. -/
def allowedCompiledBodyOverrides : Array Name := #[]

/-- Every declaration outside `ambientPackageRoots` that carries a compiled-body override and is not
on the allowlist, paired with the attribute responsible.

Imported declarations are read off the two attribute extensions' per-module entry arrays — the same
arrays `ParametricAttribute.getParam?`, and hence the compiler, reads, so an override the compiler
acts on cannot be invisible here. The entry arrays are fetched first and the module root classified
only for the few modules that have any, so the scan costs a pair of array lookups per imported
module. Declarations of the module currently being elaborated have no module index, so they are read
from stage 2 of the constant map — exactly the current module's constants — through
`compiledBodyOverride?`, which is that same compiler-facing query. -/
def undisclosedCompiledBodyOverrides (env : Environment) : Array (Name × Name) := Id.run do
  let mods := env.header.moduleNames
  let mut found : Array (Name × Name) := #[]
  for i in [0:mods.size] do
    let idx : ModuleIdx := i
    let impls := Lean.Compiler.implementedByAttr.ext.getModuleEntries env idx
    let externs := Lean.externAttr.ext.getModuleEntries env idx
    unless impls.isEmpty && externs.isEmpty do
      unless ambientPackageRoots.contains mods[i]!.getRoot do
        found := impls.foldl (fun acc (d, _) => acc.push (d, `implemented_by)) found
        found := externs.foldl (fun acc (d, _) => acc.push (d, `extern)) found
  found := env.constants.foldStage2 (fun acc d _ =>
    match compiledBodyOverride? env d with
    | some attr => acc.push (d, attr)
    | none => acc) found
  -- Sorted: the current module's constants come out of a hash map, so the report — which is pinned
  -- by `#guard_msgs` in the regression suite — would otherwise have no fixed order. The attribute
  -- breaks ties, since a declaration can in principle carry both and sorting on the name alone
  -- would leave those two rows unordered.
  return (found.filter fun (d, _) => !allowedCompiledBodyOverrides.contains d).qsort
    (fun a b => Name.lt a.1 b.1 || (a.1 == b.1 && Name.lt a.2 b.2))

/-- Render `(declaration, attribute)` pairs as the text of the offending attributes. -/
def overridesText (overrides : Array (Name × Name)) : String :=
  ", ".intercalate (overrides.toList.map fun (d, attr) => s!"{d} (@[{attr}])")

/-- The censused declaration must not have its own compiled body substituted. Checked even for an
ambient-root target, because here the substitution is not background compiler trust but the entry's
own subject: everything the census goes on to verify is about the kernel term, which for such a
declaration is not what runs. -/
def checkNoCompiledBodyOverride (n : Ident) (name : Name) : CommandElabM Unit := do
  if allowedCompiledBodyOverrides.contains name then return
  if let some attr := compiledBodyOverride? (← getEnv) name then
    throwError "{n} carries '@[{attr}]', so its compiled body is not the body the kernel reduces \
      and Lean checks no relation between the two. Nothing this census verifies about the kernel \
      term constrains what compiled code — a `native_decide` over it in particular — computes."

/-- No declaration in the census's own scope may have its compiled body substituted. This is a
property of the whole import closure rather than of `n`, so it fails every entry in the file at
once; that is the intent — an override anywhere is undisclosed compiler trust that the census, as
the artifact's statement of its trusted base, must not certify around. -/
def checkCompiledBodyDisclosure (n : Ident) : CommandElabM Unit := do
  let overrides := undisclosedCompiledBodyOverrides (← getEnv)
  unless overrides.isEmpty do
    throwError "{n} cannot be censused: {overridesText overrides} \
      substitute(s) a compiled body Lean never checks against the kernel body, so the value the \
      compiler runs is unconstrained by anything proved about it. Use the proven-equality \
      `@[csimp]` instead, or — if the substitution really belongs in the trusted base — disclose it \
      in `Zcash.TrustBoundary` and add it to `Zcash.Meta.allowedCompiledBodyOverrides`."

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

/-! ## `partial` inside a native certificate

The other shape of compiled-versus-kernel divergence, and the one the attribute sweep above cannot
see. `partial def f` elaborates to an `opaque` constant plus an `unsafe` `f._unsafe_rec` that the
compiler substitutes for it: the kernel gets a constant it will not unfold and no equation relating
it to anything, while the compiled body is unsafe code with the termination check lifted — the
`unsafe def r : Break := r` shape `assert_computable`'s safety check rejects, re-entering through a
declaration that is neither `unsafe` nor a `def`. A `native_decide` over such a constant is an
assertion about something the kernel could not have evaluated even in principle.

`assert_computable` rejects a `partial` target already (it is not a `def`), but the entry that
launders one is the `assert_axioms` on the certificate *consuming* it, whose own declaration is
clean. So this is checked where it bites: inside what a `native_decide` certificate actually
evaluated. That surface is exact and cheap, because a `native_decide` auxiliary axiom is
`@Eq Bool e Bool.true` with `e` the closed term the compiler ran (`Lean.Meta.nativeEqTrue`) —
walking `e` walks the data, not the proof.

`e` is the term as the *kernel* records it, though, and the compiler does not run it verbatim: a
`@[csimp]` lemma replaces a constant wholesale in compiled code, so where `e` says `evalNat` the
compiled certificate ran `evalNatFast`. The walk therefore follows those replacements. Without that
step a `partial` reachable only through a replacement target would be invisible here, and this
repository redirects the fixtures' hot path exactly that way (`Zcash.Arithmetic.FastMsm`).

Plain `opaque` is deliberately not reported. Its compiled body *is* its declared body, so it cannot
make a certificate disagree with the source; and the sealed-subtype barriers this repository uses
(`opaque h : {x // x = source} := ⟨source, rfl⟩`, as in `Zcash.Circuits.Action.TopLevel` and
`ActionGateCoherence`) keep the value kernel-recoverable through the type. An `opaque` that *is*
body-substituted carries `@[implemented_by]` and is caught by the sweep above. -/

/-- Whether `decl` is the `opaque` constant a `partial def` leaves behind, recognised by the
`_unsafe_rec` implementation the compiler substitutes for it (`Lean.Compiler.mkUnsafeRecName`). -/
def isPartialDecl (env : Environment) (decl : Name) : Bool :=
  env.find? decl matches some (.opaqueInfo _) &&
    env.contains (Lean.Compiler.mkUnsafeRecName decl)

/-- `partial` declarations outside `ambientPackageRoots` that a `native_decide` certificate
evaluated. Walks the auxiliary axioms' types, which are the terms that ran, following the
`@[csimp]` replacements the compiler applies to them. -/
def nativeEvaluatedPartials (env : Environment) (nativeAxioms : Array Name) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let csimp := (Lean.Compiler.CSimp.ext.getState env).map
  let mut seen : Std.HashSet Name := {}
  let mut found : Array Name := #[]
  let mut todo := nativeAxioms
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    unless seen.contains c do
      seen := seen.insert c
      if let some info := env.find? c then
        let ambient := match env.getModuleIdxFor? c with
          | some idx => ambientPackageRoots.contains mods[idx.toNat]!.getRoot
          | none => false
        if !ambient && isPartialDecl env c then
          found := found.push c
        -- An axiom contributes only its type: for a native auxiliary that type *is* the evaluated
        -- term. A theorem contributes only its type too — its proof is erased before compilation,
        -- so a `partial` reachable only through one is never run. Everything else contributes its
        -- value, which is what evaluation unfolds into.
        todo := todo ++ info.type.getUsedConstants
        unless info matches .axiomInfo _ | .thmInfo _ do
          todo := todo ++ (info.value?.map Expr.getUsedConstants).getD #[]
        -- An inductive's constructors, as `Lean.CollectAxioms.collect` does: they carry no value,
        -- but reaching them keeps the traversal's notion of "mentioned" the same as the census's.
        if let .inductInfo v := info then
          todo := todo ++ v.ctors.toArray
        -- `@[csimp]` replaces `c` with `e.toDeclName` in compiled code, so where the kernel term
        -- says `c` the compiler runs the replacement's body. Following it is what makes this a
        -- walk of what actually ran rather than of what the axiom's statement mentions.
        if let some e := csimp.find? c then
          todo := todo.push e.toDeclName
  return found.qsort Name.lt

/-- A `native_decide` certificate must not have evaluated a `partial` declaration: the auxiliary
axiom asserts that the compiler's evaluation is the kernel's, and here the kernel has no body to
have evaluated — for a fixture capture, that turns the fingerprint into a statement about an
abstract constant backed by an unsafe implementation. -/
def checkNativeEvaluatedSurface (n : Ident) (axs : Array Name) : CommandElabM Unit := do
  let nativeAxioms := axs.filter isNativeDecideAxiom
  if nativeAxioms.isEmpty then return
  let partials := nativeEvaluatedPartials (← getEnv) nativeAxioms
  unless partials.isEmpty do
    throwError "{n}: the native_decide certificate evaluated the `partial` declaration(s) \
      {partials.toList}, whose compiled body is an unsafe implementation the kernel never sees and \
      whose kernel constant has no body at all. Nothing relates what ran to what the certificate \
      says. Give the evaluated data an ordinary `def`."

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

Independently of the axiom budget, the entry fails if `foo` or any censused-scope declaration
carries a compiled-body override (`checkCompiledBodyDisclosure`), or if a permitted certificate
evaluated a `partial` declaration (`checkNativeEvaluatedSurface`); `Zcash.Meta.Tests.NativeSurface`
pins the latter.
-/
elab "assert_axioms " n:ident native:(nativeFlag)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  checkFullyQualified n name
  checkNoCompiledBodyOverride n name
  let axs ← collectAxioms name
  let allowed ← resolveNativeAnnotation native
  checkNativeAllowance n axs allowed
  checkNativeEvaluatedSurface n axs
  let unexpected := axs.filter fun ax =>
    !standardAxioms.contains ax && !(allowed.isSome && isNativeDecideAxiom ax)
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"
  checkCompiledBodyDisclosure n

/--
`assert_computable foo` fails the build unless `foo` is a plain `def` — an actual definition,
marked neither `unsafe`/`partial` nor `noncomputable` — depending on no axioms beyond
`propext` / `Quot.sound`. This is the breaks-as-computed-data check: the data is genuinely
computed, and with `Classical.choice` excluded it cannot have been conjured from mere
propositional existence even in erased positions.

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

"Genuinely computed" is a claim about the *compiled* body, which none of the checks above can see,
so the assertion additionally rejects a definition whose compiled body is substituted and any
censused-scope declaration that substitutes one (`checkNoCompiledBodyOverride`,
`checkCompiledBodyDisclosure`); `Zcash.Meta.Tests.CompiledOverride` pins both rejections.
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
  checkNoCompiledBodyOverride n name
  let axs ← collectAxioms name
  let allowChoice := choice.isSome
  if allowChoice && !axs.contains ``Classical.choice then
    throwError "{n} does not depend on Classical.choice; drop the '+choice' flag"
  let allowed ← resolveNativeAnnotation native
  checkNativeAllowance n axs allowed
  checkNativeEvaluatedSurface n axs
  let unexpected := axs.filter fun ax =>
    !(ax == ``propext || ax == ``Quot.sound
      || (allowChoice && ax == ``Classical.choice)
      || (allowed.isSome && isNativeDecideAxiom ax))
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"
  checkCompiledBodyDisclosure n

end Zcash.Meta
