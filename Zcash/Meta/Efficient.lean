import Lean

/-!
# `efficient def` — a cost function derived from a definition (prototype)

A security reduction has to be more than computable. The adversary that it builds against an
assumption must run in time bounded by the adversary that it is given. Otherwise the reduction
transfers nothing. `assert_computable` (`Zcash.Meta.AxiomCheck`) checks the first half, that the
reduction is a plain `def` that does not reach any choice principle. This module is a prototype of
the second half.

A definition `f` gets a cost function `f.cost`, with the same binders and returning `Nat`, derived
from its body in the style of Isabelle's `time_fun` command:

* every call of a function with a cost function costs that function's cost at the actual
  arguments, plus one for the call;
* a recursive call costs `f.cost` at the actual arguments, plus one, so `f.cost` recurses as `f`
  does;
* every `if` and every `match` costs one for the decision, and then the cost of the branch taken;
* constructors, literals, projections and local variables are free beyond the cost of their
  arguments;
* a call of a function without a cost function derives one on demand from that function's
  definition, by the same rules, and so on down to the primitives;
* a primitive, which has no definition to price (an axiom, an opaque or `partial` definition, a
  quotient operation, a recursor) or whose definition is not the right measure of its cost (`Nat`
  arithmetic, which runs on machine words), needs a cost function registered with
  `efficient_cost`, exactly as an unexpected axiom needs an allowance for `assert_computable`.

Isabelle's `time_fun` is defined in HOL-Library's `Time_Commands` theory and applied to the
standard library in its `Time_Functions` theory:
<https://isabelle.in.tum.de/library/HOL/HOL-Data_Structures/HOL-Library.Time_Functions.html>.

Two ways in. `efficient def f (binders) : α := body` defines `f` and derives `f.cost` from the
elaborated body, copying the termination suffix, so that `f.cost` reuses `f`'s termination
argument. `assert_efficient f`, defined beside `assert_computable` in `Zcash.Meta.AxiomCheck`,
derives `f.cost` on demand from `f`'s definition: for a recursive `f`, from the body that Lean
keeps for its equation lemmas, with the recursive calls charged to `f.cost`, and Lean then settles
the cost function's recursion as it settled `f`'s. A structurally recursive `f` goes through by
itself. A well-founded `f` goes through when Lean's default decreasing tactic proves the measure
that it guesses; otherwise the derivation fails and says so, and `f` needs an `efficient def` with
its own termination argument, or a registered cost function, which is the analogue of a loop
variant. The derived function is a definition like any other: `#eval` runs it, `simp [f.cost]`
unfolds it, and a bound `f.cost xs ≤ 3 * xs.length + 1` is an ordinary theorem, usually by
induction. This module itself imports only `Lean`, so the cost machinery can be used on its own.

Prototype restrictions, in the order in which they are likely to be lifted:

* functions are first order: a function-valued expression in a data position (a lambda passed as
  an argument, or a local function applied) is an error, since its cost would have to be given
  symbolically, and so is a partial application of a function with a cost function;
* mutual recursion is not supported;
* the cost is a single `Nat`, with no separate budget for group operations; and
* no bound is synthesized or proved automatically.
-/

open Lean Elab Command Meta Term

namespace Zcash.Meta.Efficient

/-- A registered cost function. `cost` takes the binders of `fn`, then one companion per entry
of `companions`, and returns `Nat`. A companion `(i, path)` is the cost function of the function
reached from the `i`-th binder by the projections in `path`: `(i, [])` for a function-typed
binder itself, `(i, [f])` for a function stored in field `f` of a structure-typed binder. -/
structure CostEntry where
  fn : Name
  cost : Name
  companions : Array (Nat × List Name) := #[]
  deriving Inhabited, Repr

/-- The registry of cost functions: derived by `efficient def` or on demand, or declared by
`efficient_cost`. -/
initialize costExt : SimplePersistentEnvExtension CostEntry (NameMap CostEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.fn e
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl (fun m e => m.insert e.fn e) m) {}
  }

/-- The cost function registered for `fn`, if any. -/
def costFn? (env : Environment) (fn : Name) : Option Name :=
  ((costExt.getState env).find? fn).map (·.cost)

/-- The registry entry of `fn`, if any. -/
def costEntry? (env : Environment) (fn : Name) : Option CostEntry :=
  (costExt.getState env).find? fn

/-- The derivations that failed in this module, by function, with the reason. A failed derivation
can leave the cost declaration behind, and a second attempt should repeat the reason rather than
report that leftover. -/
initialize failedCostsExt : EnvExtension (NameMap String) ← registerEnvExtension (pure {})

/-- Constants whose applications cost nothing beyond their arguments: numerals, casts between
number types, type-level casts along equalities, and the identity. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``HEq.rec, ``Quot.mk]

/-- The function whose cost is being derived; the expression that stands for its cost function,
to which a recursive call is charged (a local variable while an `efficient def` is being
elaborated, the cost function's constant when a cost is derived on demand); the companions of
the function-typed binders in scope (see `companionType`); and the functions whose costs are
being derived further up the chain, to stop a cycle. -/
structure Context where
  fn : Name
  recCall : Option Expr
  /-- The parameters of the definition being priced: the only roots that companions can have. -/
  params : Std.HashSet FVarId := {}
  /-- Whether the cost is being built by `efficient def`, whose cost definition has no
  companions. -/
  viaEfficientDef : Bool := false
  /-- The companions in scope, keyed by a parameter and the projection path from it: `[]` for the
  parameter itself, `[f]` for the function in its field `f`. -/
  companions : Std.HashMap (FVarId × List Name) Expr := {}
  /-- The companions that the recursive calls of `fn` take, as descriptors over its binders. -/
  recCompanions : Array (Nat × List Name) := #[]
  /-- In the collecting pass, the companions reached through structure fields that are not in
  scope yet: their keys and types. A placeholder stands in for each. -/
  collect : Option (IO.Ref (Array (FVarId × List Name × Expr))) := none
  visiting : NameSet := {}

private def natLit (n : Nat) : Expr := mkNatLit n

/-- `e` for an error message, on one line: the pretty-printer would otherwise break an
application such as `pts p` across lines at the message width. -/
private def inline (e : Expr) : MetaM MessageData := do
  return .ofFormat (.text ((← ppExpr e).pretty 100000))

/-- Mark `e` as a value whose cost has been paid elsewhere, so that the walker prices it at
zero: the recursive result that an induction hypothesis stands for. -/
private def markPaid (e : Expr) : Expr := mkMData (KVMap.empty.insert `efficient.paid (.ofBool true)) e

/-- Whether `e` is a value marked by `markPaid`. -/
private def isPaid (e : Expr) : Bool :=
  match e with
  | .mdata d _ => d.contains `efficient.paid
  | _ => false

/-- `a + b` over `Nat`, dropping zero summands. Built without type inference: while a cost
function is being derived, its recursive calls name a constant that does not exist yet. -/
private def add (a b : Expr) : Expr :=
  if a == natLit 0 then b
  else if b == natLit 0 then a
  else
    let nat := Lean.mkConst ``Nat
    mkApp6 (Lean.mkConst ``HAdd.hAdd [.zero, .zero, .zero]) nat nat nat
      (mkApp2 (Lean.mkConst ``instHAdd [.zero]) nat (Lean.mkConst ``instAddNat)) a b

/-- Whether an argument carries data that the cost should account for: not a type or a type
family, a proof, or an instance. -/
private def isDataArg (a : Expr) : MetaM Bool := do
  let t ← inferType a
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- `t` reduced until it is a `∀` or cannot be unfolded further, by at most a few unfoldings:
a full `whnf` can run away on some dependent types, and a function type hides behind at most a
short chain of definitions. -/
private def exposeForall (t : Expr) : MetaM Expr := do
  let mut t ← whnfCore t
  for _ in [:16] do
    if t.isForall then return t
    match ← unfoldDefinition? t with
    | some t' => t ← whnfCore t'
    | none => return t
  return t

/-- Whether a data binder or argument of type `t` is a function: its type reduces to a `∀` whose
codomain is data. Such a binder gets a companion, and such an argument is priced symbolically. -/
private def isFunctionType (t : Expr) : MetaM Bool := do
  let t ← exposeForall t
  unless t.isForall do return false
  forallTelescopeReducing t fun _ cod => return !(← isTypeFormerType cod)

/-- `ys` with each binder's companion, where it has one, right after it. -/
private def interleave (ys : Array Expr) (comps : Array (Option Expr)) : Array Expr := Id.run do
  let mut out := #[]
  for y in ys, c in comps do
    out := out.push y
    if let some c := c then out := out.push c
  return out

mutual

/-- Declare a companion for each function-typed data binder among `ys`, and continue with them,
aligned with `ys` (`none` where a binder has no companion). -/
private partial def withCompanionDecls {α : Type} [Inhabited α] (ys : Array Expr)
    (k : Array (Option Expr) → TermElabM α) : TermElabM α := do
  let mut decls := #[]
  let mut which := #[]
  for y in ys do
    if (← isDataArg y) && (← isFunctionType (← inferType y)) then
      let ty ← companionType (← inferType y)
      decls := decls.push ((← y.fvarId!.getUserName) ++ `cost, BinderInfo.default,
        fun (_ : Array Expr) => pure ty)
      which := which.push true
    else
      which := which.push false
  withLocalDecls decls fun comps => do
    let mut aligned := #[]
    let mut i := 0
    for w in which do
      if w then
        aligned := aligned.push (some comps[i]!)
        i := i + 1
      else
        aligned := aligned.push none
    k aligned

/-- The type of the companion of a function value of type `t`: `t` with its codomain replaced by
`Nat`, and, after each function-typed argument, a companion for that argument. So the companion
of `f : α → β` is `f.cost : α → Nat`, and the companion of `g : (α → β) → γ` is
`g.cost : (h : α → β) → (h.cost : α → Nat) → Nat`. -/
partial def companionType (t : Expr) : TermElabM Expr := do
  forallTelescopeReducing (← exposeForall t) fun ys _ =>
    withCompanionDecls ys fun comps =>
      mkForallFVars (interleave ys comps) (Lean.mkConst ``Nat)

end

/-- For each binder of the function `c`, whether it is a function-typed data binder, which its
cost function follows with a companion. -/
private def functionBinders (c : Name) : MetaM (Array Bool) := do
  forallTelescope (← getConstInfo c).type fun xs _ => xs.mapM fun x => do
    if ← isDataArg x then isFunctionType (← inferType x) else pure false

/-- For each argument, whether it is function-typed data: such an argument is not priced as data
(a closure costs nothing to build), and a callee with a companion for it prices its calls. -/
private def functionArgs (args : Array Expr) : MetaM (Array Bool) :=
  args.mapM fun a => do if ← isDataArg a then isFunctionType (← inferType a) else pure false

/-- `value` with as many leading lambdas as `type` has binders, so that a definition that returns
a function is priced with that function's arguments among its own binders. -/
private def etaExpandToType (value type : Expr) : MetaM Expr :=
  lambdaTelescope value fun xs body => do
    forallTelescopeReducing (← instantiateForall type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN body ys).headBeta

/-- The companion descriptors of a function priced by a registered cost function: one for each
function-typed data binder, in order, and none for structure fields. -/
private def plainDescriptors (c : Name) : MetaM (Array (Nat × List Name)) := do
  let flags ← functionBinders c
  return (flags.zipIdx.filterMap fun (isFn, i) => if isFn then some (i, []) else none)

/-- The parameter and projection path that a structure-field access `e` reaches: `A` gives
`(A, [])`, `A.f` gives `(A, [f])`, `A.f.g` gives `(A, [f, g])`, through either form of projection.
`none` for anything else, such as a field of a value computed on the spot. -/
private partial def structPath? (e : Expr) : MetaM (Option (FVarId × List Name)) := do
  match e with
  | .mdata _ e => structPath? e
  | .fvar id => return some (id, [])
  | .proj s i x =>
    let some (root, path) ← structPath? x | return none
    let fields := getStructureFields (← getEnv) s
    return fields[i]?.map fun f => (root, path ++ [f])
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let .const c _ := f | return none
    let some info := (← getEnv).getProjectionFnInfo? c | return none
    if info.fromClass || args.size != info.numParams + 1 then return none
    let some (root, path) ← structPath? args.back! | return none
    return some (root, path ++ [Name.mkSimple c.getString!])
  | _ => return none

/-- The structure that a field access `e` projects from: `A.f.g` gives `A.f`. -/
private def structBase (e : Expr) : MetaM Expr := do
  match e.consumeMData with
  | .proj _ _ x => return x
  | e => return e.getAppArgs.back!

/-- The field that `e` accesses, if `e` is a field access of a plain structure in either form. -/
private def fieldOf? (e : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  match e.consumeMData with
  | .proj s i _ => return (getStructureFields env s)[i]?
  | e =>
    let .const c _ := e.getAppFn | return none
    let some info := env.getProjectionFnInfo? c | return none
    if info.fromClass || e.getAppNumArgs != info.numParams + 1 then return none
    return some (Name.mkSimple c.getString!)

/-- The layout of a `casesOn` or `rec` application of a non-recursive inductive type: the
recursor's value, and whether `c` is the `casesOn` form. -/
private def casesLayout? (c : Name) : MetaM (Option (RecursorVal × Bool)) := do
  let env ← getEnv
  if isCasesOnRecursor env c then
    let some (.recInfo r) := env.find? (c.getPrefix ++ `rec) | return none
    return some (r, true)
  match env.find? c with
  | some (.recInfo r) => return some (r, false)
  | _ => return none

/-- The body from which `c`'s cost is derived, with its universe parameters and type: for a
recursive definition, the body that Lean keeps for the equation lemmas, in which the recursive
calls are applications of the constant `c`; otherwise the definition's value. -/
def bodyToPrice (c : Name) : TermElabM (List Name × Expr × Expr) := do
  let env ← getEnv
  let mutualErr := m!"efficient: '{c}' is defined by mutual recursion, which is not supported \
    yet; register a cost function for it with `efficient_cost`"
  if let some info := Structural.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then throwError mutualErr
    return (info.levelParams, info.value, info.type)
  if let some info := WF.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then throwError mutualErr
    return (info.levelParams, info.value, info.type)
  let register := m!"register a cost function for it with `efficient_cost {c} := <cost function>`"
  match env.find? c with
  | some (.defnInfo info) => return (info.levelParams, info.value, info.type)
  | some (.opaqueInfo info) =>
    -- A `partial def` is an opaque constant whose value is a default element, with the real
    -- implementation behind `implemented_by`: there is nothing to price. An honest `opaque`
    -- with a value is a reduction barrier for proofs; the value is what runs, so it is priced.
    if info.isUnsafe || (Compiler.getImplementedBy? env c).isSome
        || env.contains (c ++ `_unsafe_rec) then
      throwError "efficient: '{c}' is a `partial` definition (an opaque constant implemented by \
        unsafe code), so it has no body to price; {register}"
    return (info.levelParams, info.value, info.type)
  | some (.axiomInfo _) => throwError "efficient: '{c}' is an axiom, so it cannot be priced"
  | some (.thmInfo _) => throwError "efficient: '{c}' is a theorem, not data"
  | some (.quotInfo _) =>
    throwError "efficient: '{c}' is a quotient primitive, which takes a function; higher-order \
      costs are not supported yet, so {register}"
  | some (.recInfo _) =>
    throwError "efficient: '{c}' is a recursor, which takes functions; higher-order costs are \
      not supported yet, so {register}"
  | some (.inductInfo _) | some (.ctorInfo _) => throwError "efficient: '{c}' is not a function"
  | none => throwError "efficient: unknown constant '{c}'"

mutual

/-- The derived cost of `e`, an expression of `Nat`. -/
partial def costOf (ctx : Context) (e : Expr) : TermElabM Expr := do
  if isPaid e then return natLit 0
  match e with
  | .mdata _ b => costOf ctx b
  | .proj _ _ s => if ← isDataArg s then costOf ctx s else return natLit 0
  | .letE n t v b _ =>
    -- A `let` may bind a proof, a type, or an instance; only data is priced. A `let`-bound
    -- function is inlined, so that its calls are priced at the function it stands for.
    if (← isDataArg v) && (← isFunctionType t) then
      return ← costOf ctx (b.instantiate1 v)
    let cv ← if ← isDataArg v then costOf ctx v else pure (natLit 0)
    let cb ← withLetDecl n t v fun x => do
      mkLetFVars #[x] (← costOf ctx (b.instantiate1 x))
    return add cv cb
  | .app .. =>
    -- Reducing a lambda at the head may leave something other than an application, such as a
    -- bare local, which is a value rather than a call.
    let e := e.headBeta
    unless e.isApp do return ← costOf ctx e
    match e.getAppFn with
    | .letE n t v b nd =>
      -- `(let x := v; b) args`, which a `have` in a `do` block elaborates to: the arguments
      -- go into the body, under the binding.
      costOf ctx (.letE n t v (mkAppN b (e.getAppArgs.map (·.liftLooseBVars 0 1))) nd)
    | .mdata _ f => costOf ctx (mkAppN f e.getAppArgs)
    | _ => costApp ctx e
  | .const .. => costApp ctx e
  | .lam .. =>
    throwError "efficient: a function-valued expression outside an argument position is not \
      supported yet (a `let`-bound function, say)"
  | _ => return natLit 0

/-- The summed cost of the arguments of a call: data arguments are priced here; function-typed
ones are priced through their companions, by the caller. -/
partial def argsCost (ctx : Context) (args : Array Expr) (isFn : Array Bool) : TermElabM Expr := do
  let mut acc := natLit 0
  for a in args, fn in isFn do
    if !fn && (← isDataArg a) then
      acc := add acc (← costOf ctx a)
  return acc

/-- The companion in scope for the function reached from a parameter by `path`, whose type is
given by `mkType`. In the collecting pass a missing one is recorded, with its type, and a
placeholder of that type stands in for it. -/
partial def companionFor (ctx : Context) (key : FVarId × List Name) (mkType : TermElabM Expr)
    (use? : Option Expr := none) : TermElabM Expr := do
  if let some c := ctx.companions[key]? then return c
  let raw ← key.1.getUserName
  let where_ := m!"{raw.eraseMacroScopes}{key.2.foldl (fun s f => s ++ "." ++ f.toString) ""}"
  if ctx.viaEfficientDef then
    throwError "efficient def: `{where_}` is a function, and `efficient def` cannot price a call \
      of a function parameter: the cost function it builds has no companion for the parameter's \
      cost. Define `{ctx.fn}` with `def` and pin it with `assert_efficient`, which derives a cost \
      function that takes a companion `{where_}.cost`."
  unless ctx.params.contains key.1 do
    -- A local introduced by the elaborator has a synthesized name, which the user cannot act
    -- on; show it as the pretty-printer does, with the expression that uses it.
    let fv := mkFVar key.1
    let nameless := raw.hasMacroScopes || raw.isAnonymous
    let name ← if nameless then inline fv else pure m!"{where_}"
    -- `use?` is the call headed by the local, or the local itself when it is passed on.
    let (verb, site) ← match use? with
      | some u => do
        if u.consumeMData == fv then pure ("is passed on", m!"")
        else if nameless then pure ("is called", m!" in `{← inline u}`")
        else pure ("is called", m!"")
      | none => pure ("is called", m!"")
    let local_ := if nameless then "a local with no name of its own, bound by" else "a local bound by"
    throwError "efficient: in the body of `{ctx.fn}`, the function `{name}` of type \
      `{← inline (← inferType fv)}` {verb}{site}, but its cost is unknown there. It is \
      {local_} a lambda, a `let`, or a `match` pattern. The derivation has cost companions only \
      for the parameters of `{ctx.fn}`, and for functions stored in fields of those parameters."
  let some ref := ctx.collect
    | throwError "efficient: no cost companion for `{where_}` in `{ctx.fn}` (internal: it \
        should have been collected in the first pass)"
  let ty ← mkType
  ref.modify (·.push (key.1, key.2, ty))
  mkSorry ty true

/-- Why the class instance `inst` has no priced methods, for the report: it is a local that is
not a parameter, a field of such a local, a global that does not reduce to its constructor, or
something else. (An instance that is a parameter, or a field of one, has companions instead.) -/
partial def describeInstance (ctx : Context) (inst : Expr) : TermElabM MessageData := do
  let inst := inst.consumeMData
  let local_ := "a local bound by a lambda, a `let`, or a `match` pattern, not a parameter of"
  match ← structPath? inst with
  | some (_, []) => return m!"the instance `{← inline inst}` is {local_} `{ctx.fn}`"
  | some (root, _) =>
    return m!"the instance `{← inline inst}` is a field of `{← inline (mkFVar root)}`, which \
      is {local_} `{ctx.fn}`"
  | none =>
    let .const n _ := inst.getAppFn
      | return m!"the instance `{← inline inst}` is neither a parameter of `{ctx.fn}`, a field \
          of one, nor an expression that reduces to its constructor"
    let kind ← match (← getEnv).find? n with
      | some (.opaqueInfo _) => pure "an `opaque` constant"
      | some (.axiomInfo _) => pure "an axiom"
      | some (.defnInfo _) =>
        if (← getReducibilityStatus n) == .irreducible then pure "an irreducible definition"
        else pure "a definition that does not reduce to its constructor here"
      | _ => pure "not a definition"
    return m!"the instance `{← inline inst}` is headed by `{n}`, {kind}"

/-- `e` reduced until its head is a constructor or it cannot be unfolded further, by at most a
few unfoldings: a structure computed on the spot, such as `Equiv.symm e` or a global constant,
often reduces to its constructor, which exposes the field's value. -/
partial def exposeCtor (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let mut e ← whnfCore e
  for _ in [:16] do
    if let .const c _ := e.getAppFn then
      if env.isConstructor c then return e
    match ← unfoldDefinition? e with
    | some e' => e ← whnfCore e'
    | none => return e
  return e

/-- The value of field `field` of the structure `s`, when `s` reduces to a constructor
application. -/
partial def fieldValue? (s : Expr) (field : Name) : MetaM (Option Expr) := do
  let s ← exposeCtor s
  let .const ctor _ := s.getAppFn | return none
  let env ← getEnv
  let some (.ctorInfo c) := env.find? ctor | return none
  let fields := getStructureFields env c.induct
  let some i := fields.idxOf? field | return none
  let args := s.getAppArgs
  unless args.size == c.numParams + fields.size do return none
  return some args[c.numParams + i]!

/-- The companion of a function argument: the function's cost at its arguments. A parameter, or
a function in a field of one, has its companion in scope; a lambda's companion prices its body;
a global function, possibly partially applied, is eta-expanded and priced as a call. Anything
else, such as a function computed on the spot and stored in a structure, is not supported. -/
partial def companionOf (ctx : Context) (arg : Expr) : TermElabM Expr := do
  if let some key ← structPath? arg then
    if ctx.params.contains key.1 || key.2.isEmpty then
      return ← companionFor ctx key (companionType (← inferType arg)) arg
  -- A field of a structure that is not a parameter (a global constant, or one built on the
  -- spot): through the field's value, if the structure reduces to its constructor.
  if let some field ← fieldOf? arg then
    if let some v ← fieldValue? (← structBase arg) field then
      return ← companionOf ctx v
    throwError "efficient: the function in field `{field}` of `{← inline (← structBase arg)}` is applied or \
      passed on, but the structure is not a parameter of `{ctx.fn}` and does not reduce to its \
      constructor, so its cost cannot be given"
  match arg with
  | .mdata _ a => companionOf ctx a
  | .lam .. => functionCost ctx arg
  | _ =>
    unless arg.getAppFn.isConst do
      throwError "efficient: the function argument `{← inline arg}` is neither a parameter, a function in \
        a field of one, a lambda, nor a global function, so its cost cannot be given yet"
    functionCost ctx arg

/-- The companion of a function value `fn` given as a lambda or as an application: a function of
`fn`'s arguments, with a companion for each function-typed one in scope, returning the cost of
`fn`'s body at them (`companionType`). -/
partial def functionCost (ctx : Context) (fn : Expr) : TermElabM Expr := do
  forallTelescopeReducing (← exposeForall (← inferType fn)) fun ys _ =>
    withCompanionDecls ys fun comps => do
      let mut companions := ctx.companions
      for y in ys, c in comps do
        if let some c := c then companions := companions.insert (y.fvarId!, []) c
      let cost ← costOf { ctx with companions } (mkAppN fn ys).headBeta
      mkLambdaFVars (interleave ys comps) cost

/-- `comp args`, where `comp` is a companion: a function-typed argument is followed by its own
companion, as `companionType` lays the binders out. -/
partial def applyCompanion (ctx : Context) (comp : Expr) (args : Array Expr) : TermElabM Expr := do
  let mut e := comp
  for a in args do
    e := mkApp e a
    if (← isDataArg a) && (← isFunctionType (← inferType a)) then
      e := mkApp e (← companionOf ctx a)
  return e

/-- The cost of a `casesOn` or `rec` application `c args`: the cost of the major premise, and a
`casesOn`/`rec` of the same shape whose motive is the companion type of the original motive
(`Nat` for a value, a function to `Nat` for a result that is a function) and whose minor premises
return the costs of the original branches, each with one for its decision. In a `rec`, an
induction hypothesis stands for the recursive result; in the cost minor its binder is that
result's companion: for a value, its cost, added once; for a function, charged at each
application in the branch. Where the branch uses the hypothesis as a value, the recursive value
itself, the original `rec` on the field, takes its place, already paid for. -/
partial def costCases (ctx : Context) (c : Name) (levels : List Level) (args : Array Expr)
    (r : RecursorVal) (isCasesOn : Bool) : TermElabM Expr := do
  let nParams := r.numParams
  let nIndices := r.numIndices
  let nMinors := r.numMinors
  let arity := nParams + 1 + nIndices + 1 + nMinors
  if args.size < arity then
    throwError "efficient: '{c}' is applied to {args.size} argument(s), but it takes {arity}"
  -- A result that is a function, applied further: the cost `rec` returns a function too.
  let extra := args[arity:].toArray
  let args := args[:arity].toArray
  -- Layouts: `casesOn`: params, motive, indices, major, minors; `rec`: params, motive,
  -- minors, indices, major.
  let params := args[:nParams].toArray
  let motive := args[nParams]!
  let (indices, major, minors) :=
    if isCasesOn then
      (args[nParams + 1 : nParams + 1 + nIndices].toArray, args[nParams + 1 + nIndices]!,
       args[nParams + 2 + nIndices :].toArray)
    else
      (args[nParams + 1 + nMinors : nParams + 1 + nMinors + nIndices].toArray, args[arity - 1]!,
       args[nParams + 1 : nParams + 1 + nMinors].toArray)
  let (motive', level) ← forallTelescopeReducing (← inferType motive) fun xs _ => do
    let ct ← companionType (mkAppN motive xs).headBeta
    return (← mkLambdaFVars xs ct, ← getLevel ct)
  -- How many binders each minor premise has in the recursor's own type: the constructor's
  -- fields, then one induction hypothesis per recursive field. (A `casesOn` minor has the
  -- fields only.) A minor premise may bind more when the motive is a function type: the rest
  -- are the result's arguments.
  let minorArities ← forallTelescope r.type fun xs _ =>
    xs[nParams + 1 : nParams + 1 + nMinors].toArray.mapM fun m => do
      forallTelescope (← inferType m) fun ys _ => pure ys.size
  let minors' ← minors.zipIdx.mapM fun (m, j) => do
    -- The minor premise eta-expanded to all of its arguments, so that the result's arguments
    -- are bound here whether or not the original bound them.
    let m ← forallTelescopeReducing (← inferType m) fun ys _ =>
      mkLambdaFVars ys (mkAppN m ys).headBeta
    lambdaTelescope m fun vars body => do
      let nfields := r.rules[j]!.nfields
      let nihs := if isCasesOn then 0 else minorArities[j]! - nfields
      let fields := vars[:nfields].toArray
      let ihs := vars[nfields : nfields + nihs].toArray
      let rest := vars[nfields + nihs:].toArray
      let ihDecls ← ihs.mapM fun ih => do
        let ty ← companionType (← inferType ih)
        return ((← ih.fvarId!.getUserName) ++ `cost, BinderInfo.default,
          fun (_ : Array Expr) => pure ty)
      withLocalDecls ihDecls fun ihcs => do
        let mut companions := ctx.companions
        for ih in ihs, ihc in ihcs do
          companions := companions.insert (ih.fvarId!, []) ihc
        let ctx := { ctx with companions }
        -- The branch's cost, as a value or as a function of the result's arguments, with a
        -- companion after each function-typed one; the decision costs one; a value result pays
        -- its hypotheses' costs once.
        let cost ← withCompanionDecls rest fun comps => do
          let mut cs := ctx.companions
          for y in rest, co in comps do
            if let some co := co then cs := cs.insert (y.fvarId!, []) co
          let cb ← costOf { ctx with companions := cs } body
          let cb := if rest.isEmpty then ihcs.foldl add cb else cb
          mkLambdaFVars (interleave rest comps) (add (natLit 1) cb)
        -- A hypothesis used as a value stands for the recursive result, already paid for.
        let mut cost := cost
        if !isCasesOn then
          let induct := r.getMajorInduct
          let recFields ← fields.filterM fun x => do
            return (← whnf (← inferType x)).getAppFn.constName? == some induct
          if recFields.size == ihs.size then
            for ih in ihs, field in recFields do
              let value := mkAppN (Lean.mkConst c levels) (params ++ #[motive] ++ minors ++ #[field])
              cost := cost.replaceFVar ih (markPaid value)
          else if ihs.any fun ih => cost.containsFVar ih.fvarId! then
            throwError "efficient: a branch of '{c}' uses an induction hypothesis as a value, \
              and the hypothesis belongs to a field that is not plainly of the type being \
              recursed over (a function into it, say), which is not supported yet"
        mkLambdaFVars (fields ++ ihcs) cost
  let majorCost ← if ← isDataArg major then costOf ctx major else pure (natLit 0)
  let extraCost ← argsCost ctx extra (← functionArgs extra)
  let levels' := match levels with
    | _ :: rest => level :: rest
    | [] => []
  let rebuilt := if isCasesOn then
      mkAppN (Lean.mkConst c levels') (params ++ #[motive'] ++ indices ++ #[major] ++ minors')
    else
      mkAppN (Lean.mkConst c levels') (params ++ #[motive'] ++ minors' ++ indices ++ #[major])
  return add (add majorCost extraCost) (← applyCompanion ctx rebuilt extra)

/-- The companion that a callee expects for the function reached from its argument `arg` by the
projections `path`: `arg`'s own companion when the path is empty; otherwise the companion of the
field reached from a parameter, or, when `arg` is a structure built on the spot, the companion
of the field's value. -/
partial def companionAt (ctx : Context) (arg : Expr) (path : List Name) : TermElabM Expr := do
  match path with
  | [] => companionOf ctx arg
  | field :: rest =>
    if let some (root, p) ← structPath? arg then
      if ctx.params.contains root then
        let chain ← path.foldlM (fun e f => mkProjection e f) arg
        return ← companionFor ctx (root, p ++ path) (companionType (← inferType chain))
    if let some v ← fieldValue? arg field then
      return ← companionAt ctx v rest
    throwError "efficient: the function in field `{field}` of `{← inline arg}` is needed by a callee, but the \
      structure is neither a parameter nor reducible to its constructor, so its cost cannot be \
      given yet"

/-- The companions that a callee with the given descriptors expects for a call with `args`. -/
partial def companionsFor (ctx : Context) (descriptors : Array (Nat × List Name))
    (args : Array Expr) : TermElabM (Array Expr) :=
  descriptors.mapM fun (i, path) => do
    let some a := args[i]? | throwError "efficient: a cost companion refers to a missing argument"
    companionAt ctx a path

partial def costApp (ctx : Context) (e : Expr) : TermElabM Expr := do
  if let some m ← matchMatcherApp? e then
    -- A `match` that returns a function, applied further: the extra arguments go into every
    -- alternative, which is where they are applied.
    let discrs ← argsCost ctx m.discrs (m.discrs.map fun _ => false)
    let termCtx ← read
    try
      let m' ← m.transform
        (onMotive := fun _ _ => pure (mkConst ``Nat))
        (onAlt := fun _ _ _ alt => (costOf ctx (mkAppN alt m.remaining).headBeta).run' termCtx)
      let m' := { m' with remaining := #[] }
      return add (add (natLit 1) discrs) m'.toExpr
    catch ex =>
      -- An alternative may rebind a discriminant that has a companion as a pattern variable
      -- (`| some a, f => f a`), which the walker then cannot price. The matcher's own
      -- definition applies the alternative to the discriminants, so unfolding it restores the
      -- original term, companion included. The `casesOn` underneath is priced as usual.
      -- (`unfoldDefinition?` declines a matcher; `delta?` unfolds it by its value.)
      if let some e' ← delta? e then
        return ← costOf ctx e'.headBeta
      throw ex
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const c _ =>
    if c == ``ite && args.size == 5 then
      let ct ← costOf ctx args[3]!
      let ce ← costOf ctx args[4]!
      return add (natLit 1)
        (mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce)
    if c == ``dite && args.size == 5 then
      let branch (b : Expr) : TermElabM Expr := lambdaTelescope b fun xs body => do
        mkLambdaFVars xs (← costOf ctx body)
      let ct ← branch args[3]!
      let ce ← branch args[4]!
      return add (natLit 1)
        (mkApp5 (mkConst ``dite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce)
    let env ← getEnv
    -- A projection of a plain structure is free, unless the field is a function that is then
    -- applied. A class method is a projection too, but it stands for an operation: it is priced
    -- by its registered cost function, or else by unfolding it through a concrete instance to
    -- the implementation; on an abstract instance there is nothing to unfold.
    if let some info := env.getProjectionFnInfo? c then
      if !info.fromClass then
        if args.size > info.numParams + 1 then
          -- A function stored in a structure, applied: priced through the field's companion.
          let access := mkAppN f args[:info.numParams + 1]
          let rest := args[info.numParams + 1:].toArray
          -- Its companion: from a parameter, or from the field's value when the structure
          -- reduces to its constructor (a global constant, or one built on the spot).
          let comp ← companionOf ctx access
          let inner ← argsCost ctx rest (← functionArgs rest)
          return add (add (natLit 1) inner) (← applyCompanion ctx comp rest)
        return ← argsCost ctx args (← functionArgs args)
      -- A class method on an instance that is a parameter of the definition being priced, or a
      -- field of one, is a function stored in a field of a parameter, with the instance as the
      -- structure: its companion is keyed by the parameter, the path, and the method.
      let inst := args[info.numParams]!
      if (costFn? env c).isNone then
        if let some (id, path) ← structPath? inst then
          if ctx.params.contains id then
            let access := mkAppN f args[:info.numParams + 1]
            let rest := args[info.numParams + 1:].toArray
            let comp ← companionFor ctx (id, path ++ [Name.mkSimple c.getString!])
              (companionType (← inferType access))
            let inner ← argsCost ctx rest (← functionArgs rest)
            return add (add (natLit 1) inner) (← applyCompanion ctx comp rest)
      -- Unregistered, or registered but applied beyond its arity (an operation on functions,
      -- such as a pointwise subtraction, then applied): unfold through the instance.
      let registeredArity ← if (costFn? env c).isSome then pure (some (← functionBinders c).size)
        else pure none
      if registeredArity.isNone || registeredArity != some args.size then
        if let some e' ← unfoldProjInst? e then
          return ← costOf ctx e'
        if registeredArity.isNone then
          throwError "efficient: the class method '{c}' is used on an instance whose methods \
            cannot be priced: {← describeInstance ctx inst}. Register a cost function for the \
            method with `efficient_cost {c} := <cost function>`"
    if env.isConstructor c || freeConstants.contains c then
      return ← argsCost ctx args (← functionArgs args)
    -- `casesOn` and `rec`: one for the decision, then the branch. The auxiliary recursors of
    -- `Nat` unfold to `Nat.rec`.
    if c == ``Nat.recAux || c == ``Nat.casesAuxOn then
      if let some e' ← unfoldDefinition? e then
        return ← costOf ctx e'.headBeta
    if let some (r, isCasesOn) ← casesLayout? c then
      return ← costCases ctx c f.constLevels! args r isCasesOn
    let isFn ← functionBinders c
    unless args.size == isFn.size do
      throwError "efficient: '{c}' is applied to {args.size} argument(s) here, but its cost \
        function takes exactly its own {isFn.size} binder(s); a partial application, or a call \
        that goes on to apply the result, is not supported yet"
    let inner ← argsCost ctx args isFn
    if c == ctx.fn then
      let some recCall := ctx.recCall
        | throwError "efficient: '{c}' calls itself, but no cost function is being defined for it"
      -- In the collecting pass the companion list is not final; the result is discarded.
      let comps ← if ctx.collect.isSome then pure #[] else companionsFor ctx ctx.recCompanions args
      return add (add (natLit 1) inner) (mkAppN recCall (args ++ comps))
    let costName ← ensureCost ctx.visiting c
    let descriptors := ((costEntry? (← getEnv) c).map (·.companions)).getD #[]
    let comps ← companionsFor ctx descriptors args
    let call ← try mkAppOptM costName ((args ++ comps).map some)
      catch ex => throwError "efficient: the cost function of '{c}' does not apply to this \
        call: {ex.toMessageData}"
    return add (add (natLit 1) inner) call
  | .fvar id =>
    let comp ← companionFor ctx (id, []) (companionType (← inferType f)) e
    let inner ← argsCost ctx args (← functionArgs args)
    return add (add (natLit 1) inner) (← applyCompanion ctx comp args)
  | .proj .. =>
    -- A function stored in a structure, applied, in the other form of projection.
    let comp ← companionOf ctx f
    let inner ← argsCost ctx args (← functionArgs args)
    return add (add (natLit 1) inner) (← applyCompanion ctx comp args)
  | _ => throwError "efficient: unsupported application head {f}"

/-- The cost function of `c`: the registered one, or else one derived now from `c`'s definition
and registered. `visiting` holds the functions whose costs are being derived further up. -/
partial def ensureCost (visiting : NameSet) (c : Name) : TermElabM Name := do
  if let some cost := costFn? (← getEnv) c then return cost
  -- The reasons nest: a derivation that fails on a callee's failure indents the callee's
  -- report under its own line, so `efficient:` appears once, at the top.
  let chain (why : String) : MessageData :=
    m!"efficient: while deriving the cost of '{c}':" ++ .nest 2 (m!"\n" ++ .ofFormat (.text why))
  -- A callee that many pins need fails once in full; a later pin that needs it refers to that
  -- report instead of repeating the chain.
  if (failedCostsExt.getState (← getEnv)).contains c then
    throwError "efficient: the cost of '{c}' could not be derived; see the report above"
  try deriveCost visiting c
  catch ex =>
    let why ← (← addMessageContextFull ex.toMessageData).toString
    let why := if why.startsWith "efficient: " then (why.drop "efficient: ".length).toString else why
    modifyEnv (failedCostsExt.modifyState · (·.insert c why))
    throwError (chain why)

/-- Derive and register the cost function of `c`; `ensureCost` memoizes its failures. -/
partial def deriveCost (visiting : NameSet) (c : Name) : TermElabM Name := do
  if visiting.contains c then
    throwError "efficient: '{c}' is reached again while its own cost is being derived; mutual \
      recursion is not supported yet, so register a cost function for it with `efficient_cost`"
  -- A function of the current module gets `f.cost`, a name to state theorems about. A cost derived
  -- for an imported function is private to the deriving module: two modules may each derive it,
  -- and public copies would clash when both are imported. The registry carries whichever name.
  -- The imported function's full name, private prefix included, is kept as one component, since
  -- appending to a private name drops its module and two private `rowsData`s would collide.
  let env ← getEnv
  let costName := if (env.getModuleIdxFor? c).isSome then
      mkPrivateName env (Name.mkSimple (c.toString ++ ".cost"))
    else c ++ `cost
  if env.contains costName then
    throwError "efficient: '{costName}' already exists, so no cost function can be derived for \
      '{c}'; register one with `efficient_cost {c} := <cost function>`"
  let (levelParams, value, type) ← bodyToPrice c
  let value ← etaExpandToType value type
  let recCall := Lean.mkConst costName (levelParams.map mkLevelParam)
  -- The cost function's binders are `c`'s, followed by a companion for each function-typed data
  -- binder, holding that function's cost, and then one for each function stored in a field of
  -- a structure-typed binder that the body (or a callee) applies. The latter are found by a
  -- first, collecting pass over the body, with placeholders standing in, and declared for the
  -- second pass. The type comes from the binders, not from the value, whose recursive calls name
  -- the constant that is about to be defined.
  let (costValue, costType, descriptors) ← lambdaTelescope value fun xs body => do
    let mut plain := #[]   -- (binder index, fvar)
    for x in xs, i in [:xs.size] do
      if (← isDataArg x) && (← isFunctionType (← inferType x)) then
        plain := plain.push (i, x)
    let plainDecls ← plain.mapM fun (_, x) => do
      let ty ← companionType (← inferType x)
      return ((← x.fvarId!.getUserName) ++ `cost, BinderInfo.default,
        fun (_ : Array Expr) => pure ty)
    let plainMap (comps : Array Expr) : Std.HashMap (FVarId × List Name) Expr :=
      (plain.zip comps).foldl (init := {}) fun m ((_, x), comp) => m.insert (x.fvarId!, []) comp
    -- Pass 1: collect the field companions that the body reaches.
    let ref ← IO.mkRef (#[] : Array (FVarId × List Name × Expr))
    let params : Std.HashSet FVarId := xs.foldl (fun s x => s.insert x.fvarId!) {}
    withLocalDecls plainDecls fun comps => do
      let ctx : Context := { fn := c, recCall := some recCall, params,
                             companions := plainMap comps, collect := some ref,
                             visiting := visiting.insert c }
      discard <| costOf ctx body
    let mut seen : Std.HashSet (FVarId × List Name) := {}
    let mut fields : Array (FVarId × List Name × Expr) := #[]
    for (root, path, ty) in ← ref.get do
      unless seen.contains (root, path) do
        seen := seen.insert (root, path)
        fields := fields.push (root, path, ty)
    let index (root : FVarId) : Nat := (xs.findIdx? (·.fvarId! == root)).getD xs.size
    let sorted := fields.qsort fun (r₁, p₁, _) (r₂, p₂, _) =>
      index r₁ < index r₂ || (index r₁ == index r₂ && p₁.toString < p₂.toString)
    let fieldDecls ← sorted.mapM fun (root, path, ty) => do
      let name := (path.foldl (fun n f => n ++ f) (← root.getUserName)) ++ `cost
      return (name, BinderInfo.default, fun (_ : Array Expr) => pure ty)
    let descriptors : Array (Nat × List Name) :=
      plain.map (fun (i, _) => (i, [])) ++ sorted.map fun (root, path, _) => (index root, path)
    -- Pass 2: price with every companion in scope.
    withLocalDecls (plainDecls ++ fieldDecls) fun comps => do
      let plainComps := comps[:plain.size].toArray
      let fieldComps := comps[plain.size:].toArray
      let companions := (sorted.zip fieldComps).foldl (init := plainMap plainComps)
        fun m ((root, path, _), comp) => m.insert (root, path) comp
      let ctx : Context := { fn := c, recCall := some recCall, params, companions,
                             recCompanions := descriptors, visiting := visiting.insert c }
      let cb ← costOf ctx body
      return (← mkLambdaFVars (xs ++ comps) cb, ← mkForallFVars (xs ++ comps) (Lean.mkConst ``Nat),
              descriptors)
  -- Lean settles the recursion of the cost function as it settled `c`'s, with its default
  -- decreasing tactic for a well-founded one. A failure is logged rather than thrown by some of
  -- its paths, and some leave a `sorry` behind, so check both.
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let outcome ← try
      addPreDefinitions ({}, {}) #[{
        ref := .missing, kind := .def, levelParams, modifiers := {}, declName := costName,
        binders := .missing, type := costType, value := costValue, termination := .none }]
      pure (Except.ok ())
    catch ex => pure (Except.error ex)
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := saved }
  let failure ← match outcome with
    | .error ex => pure (some ex.toMessageData)
    | .ok () =>
      if msgs.hasErrors then
        let errors : List MessageData := msgs.toList.filterMap fun (m : Message) =>
          if m.severity == MessageSeverity.error then some m.data else none
        pure (some (MessageData.joinSep errors "\n"))
      else
        let env ← getEnv
        match env.find? costName with
        | some info =>
          if (info.value?.map Expr.hasSorry).getD false then
            pure (some m!"the definition contains `sorry`")
          else pure none
        | none => pure (some m!"the definition was not added")
  if let some why := failure then
    throwError "efficient: the cost function of '{c}' could not be defined from its \
      definition: {why}\nGive '{c}' a cost function with `efficient def` and an explicit \
      termination argument, or register one with `efficient_cost {c} := <cost function>`."
  modifyEnv (costExt.addEntry · { fn := c, cost := costName, companions := descriptors })
  return costName

end

/-- `efficient_cost% f body` elaborates `body` and produces its derived cost, with recursive calls
of `f` charged to the cost function being defined. -/
syntax (name := efficientCostTerm) "efficient_cost% " ident ppSpace term : term

@[term_elab efficientCostTerm] def elabEfficientCost : TermElab := fun stx _ => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let body ← elabTerm stx[2] none
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  let costName := fn ++ `cost
  let lctx ← getLCtx
  let recCall := lctx.decls.toList.findSome? fun d? => do
    let d ← d?
    guard d.isAuxDecl
    guard (lctx.auxDeclToFullName.get? d.fvarId == some costName)
    return d.toExpr
  -- Report a rejected call at the body, not at the synthesized cost definition.
  withRef stx[2][1] <| costOf { fn, recCall, viaEfficientDef := true,
                                visiting := ({} : NameSet).insert fn } body
/-- `efficient_cost f := c` registers `c` as the cost function of `f`. `c` must take exactly the
binders of `f`, then a companion for each function-typed data binder of `f` in order (that
function's type with codomain `Nat`), and return `Nat`; it is checked against `f`'s type at every
call that it prices. -/
syntax (name := efficientCostCmd) "efficient_cost " ident " := " ident : command

@[command_elab efficientCostCmd] def elabEfficientCostCmd : CommandElab := fun stx => do
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let cost ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let companions ← liftTermElabM <| plainDescriptors fn
  modifyEnv (costExt.addEntry · { fn, cost, companions })

/-- `efficient def f (binders) : α := body` defines `f` and derives `f.cost`. The termination
suffix, if any, is copied to the cost function, which recurses exactly as `f` does. Modifiers
(a doc comment, attributes, `private`) go before `efficient`, as on a plain `def`. -/
syntax (name := efficientDef)
  declModifiers "efficient " Lean.Parser.Command.definition : command

@[command_elab efficientDef] def elabEfficientDef : CommandElab := fun stx => do
  let inner := stx[2]
  let decl : Syntax := (mkNode ``Lean.Parser.Command.declaration #[stx[0], inner]).raw
  -- `definition := "def " declId optDeclSig declVal (deriving)?`
  let declId := inner[1]
  let sig := inner[2]
  let declVal := inner[3]
  unless declVal.getKind == ``Lean.Parser.Command.declValSimple do
    throwErrorAt declVal "efficient def: write the body as `:= term`, with explicit binders, \
      rather than as pattern-matching equations (or define it plainly and use \
      `assert_efficient`, which derives the cost from the definition)"
  if sig[1].getNumArgs == 0 then
    throwErrorAt sig "efficient def: give the definition's return type"
  elabCommand decl
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declId[0]
  -- The cost definition: the same binders, returning `Nat`, with the body replaced by its cost.
  let costId := mkIdentFrom declId[0] (declId[0].getId ++ `cost)
  let ty := sig[1][0][1]
  let body := declVal[1]
  let fullId := mkIdentFrom declId[0] (rootNamespace ++ fn)
  let costBody ← `(efficient_cost% $fullId ($(⟨body⟩) : $(⟨ty⟩)))
  let natTy ← `(Nat)
  let newSig := sig.setArg 1 (sig[1].setArg 0 (sig[1][0].setArg 1 natTy))
  let newDeclVal := declVal.setArg 1 costBody
  let newInner := (inner.setArg 1 (declId.setArg 0 costId)).setArg 2 newSig |>.setArg 3 newDeclVal
  -- `declModifiers` is six optional pieces: doc comment, attributes, visibility, `noncomputable`,
  -- `unsafe`, and `partial`/`nonrec`; the cost function takes none of the original's.
  let emptyMods := mkNode ``Lean.Parser.Command.declModifiers
    #[mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode]
  let newDecl := (decl.setArg 1 newInner).setArg 0 emptyMods
  -- Elaborate the cost function under its own message log. Term elaboration recovers from an error
  -- in the cost body with `sorry`, so the definition exists either way. Only the log shows whether
  -- it is real. On an error, `f` stays defined but unregistered, so `assert_efficient f` fails.
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand newDecl
  let msgs := (← get).messages
  modify fun s => { s with messages := saved ++ msgs }
  let costName := fn ++ `cost
  if !msgs.hasErrors && (← getEnv).contains costName then
    modifyEnv (costExt.addEntry · { fn, cost := costName })

end Zcash.Meta.Efficient
