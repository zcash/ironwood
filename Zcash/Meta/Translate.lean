import Zcash.Meta.Instrument

/-!
# The instrumented translation: terms

A definition `f : (x₁ : T₁) → ⋯ → (xₙ : Tₙ) → R` gets an instrumented version
`f.inst : ⟦T₁⟧ → ⋯ → ⟦Tₙ⟧ → Nat × ⟦R⟧`, where `⟦T⟧` is the costed form of `T` (`Costed.WithCosts`,
written as `T` itself when `T` is first order). It takes the costed forms of the arguments, and
returns the cost of the call together with the costed form of the result. The body is translated
term by term into the writer monad over `Nat`:

* a call of a constant `g` costs one plus what `g.inst` reports, and yields the costed form that
  `g.inst` returns; `g.inst` is derived on demand from `g`'s definition, or registered by hand
  for a primitive;
* a call of a local function, which is a value of a function type and so comes as the function
  with its instrumented version, costs one plus what the instrumented version reports;
* a lambda costs nothing, and its costed form is the pair of itself and its translation;
* a constructor application builds the mirror's constructor from the fields' costed forms; a
  projection projects the mirror;
* a `let` binds the costed form of the value; `if` costs one plus the branch taken;
* the original value of a binder, where a type, a proposition, or an argument that is not data
  needs it, is the erasure of its costed form.

A type parameter of `f` becomes a type parameter of `f.inst` followed by a `Costed` instance
for it, which is what lets the shape of the costed forms follow the instantiation at each call
site: that is the failure of the earlier companion design that the translation fixes.
-/

open Lean Elab Command Meta Term
open Zcash.Meta.CostedRegistry Zcash.Meta.Instrument

namespace Zcash.Meta.Translate

private def natLit (n : Nat) : Expr := mkNatLit n

/-- `a + b` on `Nat`, built syntactically because the constant being defined may occur in the
operands. -/
private def add (a b : Expr) : Expr :=
  if a == natLit 0 then b else if b == natLit 0 then a
  else mkApp2 (mkConst ``Nat.add) a b

/-- The pair `(cost, value)` of a translated term, in `Nat × T` where `T` is the value's type. -/
private def mkCostPair (cost value : Expr) : MetaM Expr := do
  let t ← inferType value
  let u ← getLevel t
  return mkApp4 (mkConst ``Prod.mk [Level.zero, u.dec.get!]) (mkConst ``Nat) t cost value

/-- The two projections of a pair `p : Nat × T`. -/
private def pairCost (p : Expr) : Expr := Expr.proj ``Prod 0 p
private def pairValue (p : Expr) : Expr := Expr.proj ``Prod 1 p

/-- The context of a translation: the definition being translated and the constant that stands for
its instrumented version, the original locals in scope with their costed forms and their erasures,
and the definitions whose instrumented versions are being derived further up the chain. -/
structure TCtx where
  fn : Name
  recInst : Expr
  /-- An original local's costed form: a costed binder for data, the local itself for a type, a
  proposition, or an instance. -/
  costed : Std.HashMap FVarId Expr := {}
  /-- The original locals, in order, and what replaces each in a type, a proposition, or an
  argument that is not data: the erasure of its costed form. -/
  olds : Array Expr := #[]
  news : Array Expr := #[]
  visiting : NameSet := {}

/-- `e` with every original local replaced by its erasure: for a type, a proposition, an instance
argument, and the data half of a lambda's costed form. -/
def TCtx.erase (ctx : TCtx) (e : Expr) : Expr := e.replaceFVars ctx.olds ctx.news

/-- Fail on a shape that the translation does not handle, or a state it should not reach, with what
a report needs: the definition being translated, the term, its type where it has one, and the
original locals in scope. -/
def TCtx.internalError {α} (ctx : TCtx) (what : MessageData) (e : Expr) : TermElabM α := do
  let type ← try pure m!"{indentExpr (← inferType e)}" catch _ => pure m!" (no type)"
  let locals := ctx.olds.map fun x => m!"{x}"
  throwError "efficient: {what}, while translating `{ctx.fn}`. This is a limitation or a \
    defect of the translation; please report it with this term:{indentExpr e}\nof type{type}\n\
    with the original locals in scope: {MessageData.joinSep locals.toList ", "}"

/-- The costed form of the type `t`, reduced through the instances: `t` itself when it is first
order, the mirror or the pair otherwise. The reduction uses `reduceCosted` with no hypothetical
instance to stop at. -/
def costedFormOf (t : Expr) : TermElabM Expr := do
  let (inst, _) ← ensureCosted t
  let some v := (← getLevel t).dec
    | throwError "efficient: `{t}` is not a type in some `Type u`, so it has no costed form"
  let fv ← mkFreshFVarId
  reduceCosted fv (mkApp2 (mkConst ``Costed.WithCosts [v]) t inst)

/-- The erasure of `c`, a value of the costed form of `t`: `c` itself when `t` is first order,
`Costed.forget` reduced through the instances otherwise. -/
def erasureOf (t c : Expr) : TermElabM Expr := do
  if ← isFirstOrder t then return c
  let (inst, _) ← ensureCosted t
  let some v := (← getLevel t).dec
    | throwError "efficient: `{t}` is not a type in some `Type u`, so it has no costed form"
  let fv ← mkFreshFVarId
  reduceCosted fv (mkApp3 (mkConst ``Costed.forget [v]) t inst c)

/-- Whether the local `x` is a type: its type is a sort, or a function into one. -/
private def isTypeLocal (x : Expr) : MetaM Bool := do isTypeFormerType (← inferType x)

/-- Bind the costed forms of the original locals `xs`, one after another, and continue with the
context extended and the new binders:

* a type local stays itself, followed by a `Costed` instance binder for it;
* a proposition or an instance local is re-bound at its erased type;
* a data local is bound at its costed form, and its erasure is recorded for the later types.

The continuation gets the new binders, which include the originals that stayed. -/
def withCostedLocals {α} (ctx : TCtx) (xs : Array Expr)
    (k : TCtx → Array Expr → TermElabM α) : TermElabM α :=
  go ctx 0 #[]
where
  /-- Bind the locals from `xs[i]` on, with `acc` the binders made for the earlier ones. -/
  go (ctx : TCtx) (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < xs.size then
      let x := xs[i]
      let τ := ctx.erase (← inferType x)
      let name ← x.fvarId!.getUserName
      let bi ← x.fvarId!.getBinderInfo
      if ← isTypeLocal x then
        -- The original type local is kept, so the types that mention it need no change, and
        -- the instance binder follows it.
        let some v := (← getLevel x).dec
          | throwError "efficient: the type parameter `{x}` of `{ctx.fn}` is not in `Type u`"
        withLocalDecl (name.appendAfter "Costed") .instImplicit (mkApp (mkConst ``Costed [v]) x)
          fun inst => do
            let ctx := { ctx with costed := ctx.costed.insert x.fvarId! x,
                                  olds := ctx.olds.push x, news := ctx.news.push x }
            go ctx (i + 1) (acc ++ #[x, inst])
      else if ← isDataLocal x then
        let τc ← costedFormOf τ
        withLocalDecl name bi τc fun xc => do
          let er ← erasureOf τ xc
          let ctx := { ctx with costed := ctx.costed.insert x.fvarId! xc,
                                olds := ctx.olds.push x, news := ctx.news.push er }
          go ctx (i + 1) (acc.push xc)
      else
        withLocalDecl name bi τ fun x' => do
          let ctx := { ctx with costed := ctx.costed.insert x.fvarId! x',
                                olds := ctx.olds.push x, news := ctx.news.push x' }
          go ctx (i + 1) (acc.push x')
    else k ctx acc
  termination_by xs.size - i

/-- The definition to translate: its universe parameters, the body with the recursive calls as
applications of the constant itself, and the type. For a recursive definition the body is the
one that Lean keeps for the equation lemmas. -/
def bodyOf (c : Name) : TermElabM (List Name × Expr × Expr) := do
  let env ← getEnv
  let mutualErr := m!"efficient: `{c}` is defined by mutual recursion, which is not supported \
    yet; register an instrumented version for it with `efficient_inst`"
  if let some info := Structural.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then throwError mutualErr
    return (info.levelParams, info.value, info.type)
  if let some info := WF.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then throwError mutualErr
    return (info.levelParams, info.value, info.type)
  let register := m!"register an instrumented version for it with `efficient_inst {c} := \
    <instrumented function>`"
  match env.find? c with
  | some (.defnInfo info) => return (info.levelParams, info.value, info.type)
  | some (.opaqueInfo info) =>
    if info.isUnsafe || (Compiler.getImplementedBy? env c).isSome
        || env.contains (c ++ `_unsafe_rec) then
      throwError "efficient: `{c}` is a `partial` definition (an opaque constant implemented \
        by unsafe code), so it has no body to translate; {register}"
    return (info.levelParams, info.value, info.type)
  | some (.axiomInfo _) => throwError "efficient: `{c}` is an axiom, so it cannot be priced"
  | some (.thmInfo _) => throwError "efficient: `{c}` is a theorem, not data"
  | some (.quotInfo _) => throwError "efficient: `{c}` is a quotient primitive; {register}"
  | some (.recInfo _) => throwError "efficient: `{c}` is a recursor; {register}"
  | some (.inductInfo _) | some (.ctorInfo _) => throwError "efficient: `{c}` is not a function"
  | none => throwError "efficient: unknown constant `{c}`"

/-- Constants whose applications cost nothing beyond their arguments, and whose costed form is
the same constant at the costed forms of its arguments: numerals, casts, the identity. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``HEq.rec]

/-- `value` with as many leading lambdas as `type` has binders, so that a definition that returns a
function is translated with that function's arguments among its own binders. -/
private def etaExpandToType (value type : Expr) : MetaM Expr :=
  lambdaTelescope value fun xs body => do
    forallTelescopeReducing (← instantiateForall type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN body ys).headBeta

/-- Whether the expression `e` is data: not a type, a proposition, or an instance. -/
private def isDataExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- Whether the expression `e` is a type. -/
private def isTypeExpr (e : Expr) : MetaM Bool := do isTypeFormerType (← inferType e)

/-- The leading `let`s of `e`, outermost first, and its body under them; the bound variables are
loose in the later binders and in the body, to be instantiated once the binders are re-entered. -/
private def peelLets : Expr → Array (Name × Expr × Expr × Bool) × Expr
  | .letE n t v b nd =>
    let (lets, body) := peelLets b
    (#[(n, t, v, nd)] ++ lets, body)
  | e => (#[], e)

/-- Re-enter the `let`s that `peelLets` collected, in order, each binder's type and value
instantiated with the locals of the earlier ones, and continue with all the locals. -/
private def withLets {α} (lets : Array (Name × Expr × Expr × Bool))
    (k : Array Expr → TermElabM α) : TermElabM α :=
  go 0 #[]
where
  go (i : Nat) (xs : Array Expr) : TermElabM α := do
    if h : i < lets.size then
      let (n, t, v, nd) := lets[i]
      withLetDecl n (t.instantiateRev xs) (v.instantiateRev xs) (nondep := nd) fun x =>
        go (i + 1) (xs.push x)
    else k xs
  termination_by lets.size - i

/-- Continue with the cost and the value of the translated term `p : Nat × T`: taken apart when
`p` is a literal pair, and otherwise bound to a local, so that the term is not duplicated, with
the continuation's result under that `let`. -/
private def bindPair (p : Expr) (k : Expr → Expr → TermElabM Expr)
    (type? : Option Expr := none) : TermElabM Expr := do
  -- The continuation goes under the leading `let`s, where the pair they bind is usually literal,
  -- and a projection of a literal pair, as applying a split field's pair form leaves, reduces to
  -- one; a literal pair is taken apart rather than bound, which also keeps a recursive argument
  -- such as `kr a` visible to structural recursion.
  let (lets, body) := peelLets p
  withLets lets fun xs => do
    let p ← reduceProjs (body.instantiateRev xs)
    let result ← if p.isAppOfArity ``Prod.mk 4 then
        let args := p.getAppArgs
        k args[2]! args[3]!
      else
        -- The type is given where `p` is a recursive call, whose constant does not exist yet.
        let t ← match type? with
          | some t => pure t
          | none => inferType p
        withLetDecl `p t p fun x => do
          mkLetFVars #[x] (← k (pairCost x) (pairValue x))
    mkLetFVars xs result

/-- The inductive type of the costed form of a value of type `t`, and the costed form's arguments:
the mirror with the parameters and instances, or the type itself at the costed forms of its
parameters. -/
private def costedInductive (t : Expr) : TermElabM (Name × List Level × Array Expr) := do
  let wc ← costedFormOf t
  let .const n ls := wc.getAppFn
    | throwError "efficient: the costed form of `{t}` is not an inductive type, so it has no \
        constructors or fields to translate; the costed form is{indentExpr wc}"
  return (n, ls, wc.getAppArgs)

/-- The layout of the constructor `ctor` of the inductive type `n` that a costed form has: how
many fields of `n` represent each original field, from the registry for a generated mirror,
and one each for a type that is its own mirror. -/
private def layoutOf (n ctor : Name) : MetaM (Array Nat) := do
  let ctorInfo ← getConstInfoCtor ctor
  match mirrorInfo? (← getEnv) n with
  | some info => return info.layout[ctorInfo.cidx]!
  | none => return (Array.range ctorInfo.numFields).map fun _ => 1

/-- The mirror's field index at which the original field `i` starts, under `layout`. -/
private def mirrorIndex (layout : Array Nat) (i : Nat) : Nat :=
  (layout[:i].toArray.foldl (· + ·) 0)

/-- The pair form of a function's costed form from a split field's three parts: the function
`f`, the cost `kc`, and the result `kr` of a call. -/
private def joinSplit (f kc kr : Expr) : MetaM Expr := do
  let .forallE _ dom _ _ ← whnf (← inferType kr)
    | throwError "efficient: a split field's result part is not a function. This is a defect \
        of the translation; please report it with the three parts.\n\
        The function:{indentExpr f}\n\
        of type:{indentExpr (← inferType f)}\n\
        The cost part:{indentExpr kc}\n\
        of type:{indentExpr (← inferType kc)}\n\
        The result part:{indentExpr kr}\n\
        of type:{indentExpr (← inferType kr)}"
  let instrumented ← withLocalDecl `a .default dom fun a => do
    mkLambdaFVars #[a] (← mkCostPairOf (mkApp kc a) (mkApp kr a))
  let tf ← inferType f
  let ti ← inferType instrumented
  return mkApp4 (mkConst ``Prod.mk [(← getLevel tf).dec.get!, (← getLevel ti).dec.get!])
    tf ti f instrumented
where
  mkCostPairOf (cost value : Expr) : MetaM Expr := do
    let t ← inferType value
    return mkApp4 (mkConst ``Prod.mk [Level.zero, (← getLevel t).dec.get!]) (mkConst ``Nat) t
      cost value

/-- The three parts of a split field from the pair form `v` of a function's costed form: the
function, and the cost and the result of a call, as functions of the argument. A literal pair
is taken apart; any other `v` is projected. -/
private def splitPair (v : Expr) : MetaM (Expr × Expr × Expr) := do
  let (f, fi) := if v.isAppOfArity ``Prod.mk 4 then (v.getAppArgs[2]!, v.getAppArgs[3]!)
    else (pairCost v, pairValue v)
  let .forallE _ dom _ _ ← whnf (← inferType fi)
    | throwError "efficient: a function's costed form has no instrumented half. This is a \
        defect of the translation; please report it with the costed form:{indentExpr v}\nof \
        type{indentExpr (← inferType v)}"
  let kc ← withLocalDecl `a .default dom fun a => mkLambdaFVars #[a] (pairCost (mkApp fi a))
  let kr ← withLocalDecl `a .default dom fun a => mkLambdaFVars #[a] (pairValue (mkApp fi a))
  return (f, kc, kr)

/-- The costed form of the field `i` of the costed-form value `vs` of inductive type `n`: the
mirror's field, or the pair form rebuilt from a split field's three. -/
private def projectField (n : Name) (layout : Array Nat) (i : Nat) (vs : Expr) : MetaM Expr := do
  let j := mirrorIndex layout i
  if layout[i]! == 3 then
    joinSplit (Expr.proj n j vs) (Expr.proj n (j + 1) vs) (Expr.proj n (j + 2) vs)
  else return Expr.proj n j vs

/-- Whether `c` is the `casesOn` of an inductive type without indices, with its layout. -/
private def isCasesOn (c : Name) : MetaM (Option (InductiveVal × RecursorVal)) := do
  let env ← getEnv
  unless c.isStr && c.getString! == "casesOn" do return none
  let some (.inductInfo info) := env.find? c.getPrefix | return none
  let some (.recInfo r) := env.find? (c.getPrefix ++ `rec) | return none
  if info.numIndices != 0 then return none
  return some (info, r)

/-- The result type of `I.casesOn` from its motive, which must not depend on the value matched,
since the minor premises are translated at one costed form of the result. -/
private def casesResultType (ctx : TCtx) (motive major : Expr) : TermElabM Expr :=
  lambdaTelescope motive fun xs body => do
    -- A matcher unfolded to its `casesOn` leaves the motive as a redex applied to the value.
    let body ← Core.betaReduce body
    if xs.any (fun x => body.containsFVar x.fvarId!) then
      throwError "efficient: in `{ctx.fn}`, a `match` on a value of type `{← inferType major}` \
        has a result type that depends on the value matched, which is not supported yet: the \
        motive is{indentExpr motive}"
    pure body

mutual

/-- The instrumented version of the constant `c`: the registered one, or one derived now from `c`'s
definition and registered. A failure is remembered, and a later request for the same constant refers
to the first report instead of repeating the chain. -/
partial def ensureInst (visiting : NameSet) (c : Name) : TermElabM Name := do
  if let some e := instEntry? (← getEnv) c then return e.inst
  let chain (why : String) : MessageData :=
    m!"efficient: while deriving the instrumented version of `{c}`:" ++
      .nest 2 (m!"\n" ++ .ofFormat (.text why))
  if (failedInstExt.getState (← getEnv)).contains c then
    throwError "efficient: the instrumented version of `{c}` could not be derived; see the \
      report above"
  try deriveInst visiting c
  catch ex =>
    let why ← (← addMessageContextFull ex.toMessageData).toString
    let why := if why.startsWith "efficient: " then (why.drop "efficient: ".length).toString
      else why
    modifyEnv (failedInstExt.modifyState · (·.insert c why))
    throwError (chain why)

/-- Derive and register the instrumented version of `c`: its binders' costed forms, then the
body translated, with the recursive calls charged to the constant being defined. -/
partial def deriveInst (visiting : NameSet) (c : Name) : TermElabM Name := do
  if visiting.contains c then
    throwError "efficient: `{c}` is reached again while its own instrumented version is being \
      derived; mutual recursion is not supported yet, so register one for it with \
      `efficient_inst`"
  let env ← getEnv
  let instName := generatedName env c "inst"
  if env.contains instName then
    throwError "efficient: `{instName}` already exists, so no instrumented version can be \
      derived for `{c}`; register one with `efficient_inst {c} := <instrumented function>`"
  let (levelParams, value, type) ← bodyOf c
  let value ← etaExpandToType value type
  let recInst := Lean.mkConst instName (levelParams.map mkLevelParam)
  let (instValue, instType) ← lambdaTelescope value fun xs body => do
    let ctx : TCtx := { fn := c, recInst, visiting := visiting.insert c }
    withCostedLocals ctx xs fun ctx cs => do
      -- The projections of literal pairs left by the translation are reduced, so that the
      -- definition reads as written and structural recursion sees its arguments.
      let p ← reduceProjs (← translate ctx body)
      return (← mkLambdaFVars cs p, ← mkForallFVars cs (← inferType p))
  addDefinition instName levelParams instType instValue
  modifyEnv (instExt.addEntry · { fn := c, inst := instName, registered := false })
  return instName

/-- The translation of the data term `e`: a term of type `Nat × ⟦T⟧`, the cost of evaluating
`e` and the costed form of its value, where `T` is `e`'s type. -/
partial def translate (ctx : TCtx) (e : Expr) : TermElabM Expr := do
  match e with
  | .mdata _ b => translate ctx b
  | .fvar id =>
    let some c := ctx.costed[id]?
      | ctx.internalError m!"the local `{e}` has no costed form in scope" e
    mkCostPair (natLit 0) c
  | .lit _ => mkCostPair (natLit 0) e
  | .lam .. => translateLambda ctx e
  | .letE n t v b _ =>
    -- The original local is bound too, since the body's types may mention it.
    withLetDecl n t v fun x => do
      let body := b.instantiate1 x
      if ← isDataExpr v then
        let pv ← translate ctx v
        bindPair pv fun cv vv => do
          withLetDecl n (← inferType vv) vv fun xc => do
            let er ← erasureOf (ctx.erase t) xc
            let ctx := { ctx with costed := ctx.costed.insert x.fvarId! xc,
                                  olds := ctx.olds.push x, news := ctx.news.push er }
            let pb ← translate ctx body
            mkLetFVars #[xc] (← bindPair pb fun cb vb => mkCostPair (add cv cb) vb)
      else
        -- A type, a proposition, or an instance: bound at its erased form.
        withLetDecl n (ctx.erase t) (ctx.erase v) fun x' => do
          let ctx := { ctx with costed := ctx.costed.insert x.fvarId! x',
                                olds := ctx.olds.push x, news := ctx.news.push x' }
          mkLetFVars #[x'] (← translate ctx body)
  | .proj _ i s =>
    let ps ← translate ctx s
    bindPair ps fun cs vs => do
      let (n, _, _) ← costedInductive (ctx.erase (← inferType s))
      let ctor := (← getConstInfoInduct n).ctors[0]!
      mkCostPair cs (← projectField n (← layoutOf n ctor) i vs)
  | .const c _ =>
    if freeConstants.contains c then mkCostPair (natLit 0) e
    else translateCall ctx e
  | .app .. =>
    let e := e.headBeta
    match e.getAppFn with
    | .const .. => translateConstApp ctx e
    | .fvar id =>
      let some g := ctx.costed[id]?
        | ctx.internalError m!"the local function `{e.getAppFn}` has no costed form in scope" e
      translateApply ctx (← mkCostPair (natLit 0) g) e.getAppArgs
    | .proj .. =>
      translateApply ctx (← translate ctx e.getAppFn) e.getAppArgs
    | .mdata _ f => translate ctx (mkAppN f e.getAppArgs)
    | f => ctx.internalError m!"an application headed by `{f}` is not supported yet" e
  | _ => ctx.internalError m!"this is not a data term that the translation handles" e

/-- A lambda in a data position: its costed form is the pair of the lambda, with its free locals
erased, and its instrumented version, which binds the costed form of the argument and returns the
body's translation. Creating the closure costs nothing. -/
partial def translateLambda (ctx : TCtx) (e : Expr) : TermElabM Expr := do
  let data := ctx.erase e
  let instrumented ← lambdaTelescope e fun xs body => do
    -- One binder at a time: the costed form of a function of several arguments is nested pairs, one
    -- per argument.
    let x := xs[0]!
    let inner ← mkLambdaFVars xs[1:] body
    withCostedLocals ctx #[x] fun ctx cs => do
      mkLambdaFVars cs (← translate ctx inner)
  let tData ← inferType data
  let tInst ← inferType instrumented
  let pair := mkApp4 (mkConst ``Prod.mk [(← getLevel tData).dec.get!, (← getLevel tInst).dec.get!])
    tData tInst data instrumented
  mkCostPair (natLit 0) pair

/-- Apply the costed form `pf` (a translated term whose value is a function's costed form) to the
arguments `args`, one after another: each data argument is translated and passed to the instrumented
version, which costs one plus what it reports; a type, a proposition, or an instance argument is
passed erased and costs nothing. -/
partial def translateApply (ctx : TCtx) (pf : Expr) (args : Array Expr) : TermElabM Expr := do
  if args.isEmpty then return pf
  bindPair pf fun cf vf => do
    let a := args[0]!
    let rest := args[1:]
    if ← isDataExpr a then
      let pa ← translate ctx a
      bindPair pa fun ca va => do
        let pr := mkApp (pairValue vf) va
        bindPair pr fun cr vr => do
          let p ← mkCostPair (add (add cf (add (natLit 1) ca)) cr) vr
          translateApply ctx p rest
    else
      let pr := mkApp (pairValue vf) (ctx.erase a)
      bindPair pr fun cr vr => do
        translateApply ctx (← mkCostPair (add cf cr) vr) rest

/-- An application headed by a constant: a matcher is unfolded to its `casesOn`; `casesOn`, `ite`,
and `dite` are translated branch by branch; a constructor or a free constant is applied at the
costed forms of its arguments; a projection function projects the costed form; any other constant is
a call of its instrumented version. -/
partial def translateConstApp (ctx : TCtx) (e : Expr) : TermElabM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const c _ := f | unreachable!
  let env ← getEnv
  if let some _ ← matchMatcherApp? e then
    let some e' ← delta? e
      | throwError "efficient: the matcher `{c}` could not be unfolded"
    return ← translate ctx e'.headBeta
  if c == ``ite && args.size ≥ 5 then return ← translateIte ctx e false
  if c == ``dite && args.size ≥ 5 then return ← translateIte ctx e true
  if let some r ← isCasesOn c then return ← translateCases ctx e r
  if env.isConstructor c || freeConstants.contains c then
    return ← translateSame ctx e
  if let some info := env.getProjectionFnInfo? c then
    if !info.fromClass then
      -- A projection function, applied to the structure and maybe further: the field of the
      -- costed form, which for a function field is its costed form, then applied.
      let s := args[info.numParams]!
      let ps ← translate ctx s
      let p ← bindPair ps fun cs vs => do
        let (n, _, _) ← costedInductive (ctx.erase (← inferType s))
        let ctor := (← getConstInfoInduct n).ctors[0]!
        mkCostPair cs (← projectField n (← layoutOf n ctor) info.i vs)
      return ← translateApply ctx p args[info.numParams + 1:]
    -- A class method on a concrete instance is unfolded to the implementation, unless it has a
    -- registered instrumented version; on an abstract instance it needs one. The unfolding looks
    -- only at the instance argument, so the original application, over the original locals, is what
    -- is unfolded and then translated.
    if (instEntry? env c).isNone then
      if let some e' ← unfoldProjInst? e then
        return ← translate ctx e'
      throwError "efficient: the class method `{c}` is used on an instance that does not \
        unfold here, and has no instrumented version; register one with `efficient_inst {c} \
        := <instrumented function>`"
  translateCall ctx e

/-- `ite` and `dite`: one for the decision, then the branch taken, each branch translated; the
condition and its decidability instance are erased, and `dite`'s branches bind the proof. -/
partial def translateIte (ctx : TCtx) (e : Expr) (dependent : Bool) : TermElabM Expr := do
  let args := e.getAppArgs
  let c := ctx.erase args[1]!
  let inst := ctx.erase args[2]!
  let branch (b : Expr) : TermElabM Expr :=
    if dependent then
      lambdaTelescope b fun hs body =>
        withCostedLocals ctx hs fun ctx hs' => do mkLambdaFVars hs' (← translate ctx body)
    else translate ctx b
  let pt ← branch args[3]!
  let pe ← branch args[4]!
  let resultType ← if dependent then
      lambdaTelescope pt fun _ body => inferType body
    else inferType pt
  let u ← getLevel resultType
  let ite := mkApp5 (mkConst (if dependent then ``dite else ``ite) [u]) resultType c inst pt pe
  let p ← bindPair ite fun ci vi => mkCostPair (add (natLit 1) ci) vi
  translateApply ctx p args[5:]

/-- A constructor or a free constant: the same constant, or the mirror's constructor, at the
costed forms of its type arguments and of its data arguments, with the other arguments erased;
the costs of the data arguments add up, and the constant itself is free. -/
partial def translateSame (ctx : TCtx) (e : Expr) : TermElabM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const c levels := f | unreachable!
  let env ← getEnv
  let mut cost := natLit 0
  let mut head := f
  let mut newArgs : Array Expr := #[]
  if let some (.ctorInfo ctorInfo) := env.find? c then
    -- The constructor of the costed form's inductive type, at the costed form's parameters,
    -- with each field's costed form, or the three parts of a split field.
    let t ← inferType e
    let (n, ls, cparams) ← costedInductive (ctx.erase t)
    let ctor := c.updatePrefix n
    let layout ← layoutOf n ctor
    let fields := args[ctorInfo.numParams:].toArray
    let rec build (i : Nat) (acc : Array Expr) (cost : Expr) : TermElabM Expr := do
      if h : i < fields.size then
        let a := fields[i]
        if ← isDataExpr a then
          let pa ← translate ctx a
          bindPair pa fun ca va => do
            if layout[i]! == 3 then
              let (f, kc, kr) ← splitPair va
              build (i + 1) (acc ++ #[f, kc, kr]) (add cost ca)
            else build (i + 1) (acc.push va) (add cost ca)
        else build (i + 1) (acc.push (ctx.erase a)) cost
      else mkCostPair cost (mkAppN (mkConst ctor ls) (cparams ++ acc))
    return ← build 0 #[] (natLit 0)
  for a in args do
    if ← isTypeExpr a then newArgs := newArgs.push (← costedFormOf (ctx.erase a))
    else if ← isDataExpr a then
      let pa ← translate ctx a
      cost := add cost (pairCost pa)
      newArgs := newArgs.push (pairValue pa)
    else newArgs := newArgs.push (ctx.erase a)
  mkCostPair cost (mkAppN (mkConst c levels) newArgs)

/-- A call of a constant with an instrumented version, derived on demand: one plus what the
instrumented version reports, at the erased type arguments each followed by its `Costed` instance,
the data arguments' costed forms, and the other arguments erased. A partial application is
eta-expanded and translated as a lambda; a result that is a function is applied to the remaining
arguments as a local function. -/
partial def translateCall (ctx : TCtx) (e : Expr) : TermElabM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const c levels := f | unreachable!
  let instName ← if c == ctx.fn then pure ctx.recInst.constName! else ensureInst ctx.visiting c
  -- The binders of `c`, to classify the arguments.
  let cType ← inferType f
  let arity ← forallTelescope cType fun xs _ => pure xs.size
  if args.size < arity then
    -- A partial application: translated as the lambda it stands for.
    let expanded ← forallTelescope (← instantiateForall cType args) fun ys _ =>
      mkLambdaFVars ys (mkAppN e ys)
    return ← translateLambda ctx expanded
  let kinds ← forallTelescope cType fun xs _ => xs.mapM fun x => do
    if ← isTypeLocal x then pure 0 else if ← isDataLocal x then pure 1 else pure 2
  -- The call's type, from the original application: `Nat × ⟦R⟧` for its result type `R`.
  let resultType := ctx.erase (← inferType (mkAppN f args[:arity]))
  let cResult ← costedFormOf resultType
  let pairType := mkApp2 (mkConst ``Prod [Level.zero, (← getLevel cResult).dec.get!])
    (mkConst ``Nat) cResult
  -- The arguments one after another, each data argument's translation bound before the next,
  -- so that no translated argument is duplicated for its cost and its value.
  let rec build (i : Nat) (acc : Array Expr) (cost : Expr) : TermElabM Expr := do
    if i < arity then
      let a := args[i]!
      match kinds[i]! with
      | 0 =>
        let a' := ctx.erase a
        let (inst, _) ← ensureCosted a'
        build (i + 1) (acc.push a' |>.push inst) cost
      | 1 =>
        let pa ← translate ctx a
        bindPair pa fun ca va => build (i + 1) (acc.push va) (add cost ca)
      | _ => build (i + 1) (acc.push (ctx.erase a)) cost
    else
      let call := mkAppN (mkConst instName levels) acc
      bindPair call (type? := some pairType) fun cc vc =>
        mkCostPair (add (add (natLit 1) cost) cc) vc
  let p ← build 0 #[] (natLit 0)
  translateApply ctx p args[arity:]

/-- `I.casesOn params motive major minors extra`: one for the decision, then the branch taken.
The major premise is translated, and the cases run on its costed form with the costed form's
`casesOn`, each minor premise over the costed forms of its fields; the motive is the costed
form of the result, which may not depend on the major premise yet. -/
partial def translateCases (ctx : TCtx) (e : Expr) (r : InductiveVal × RecursorVal) :
    TermElabM Expr := do
  let (info, _) := r
  let args := e.getAppArgs
  let .const c _ := e.getAppFn | unreachable!
  let nParams := info.numParams
  let nMinors := info.numCtors
  let arity := nParams + 1 + 1 + nMinors
  if args.size < arity then
    ctx.internalError m!"`{c}` is applied to fewer arguments than its parameters, motive, \
      major premise, and minor premises" e
  let motive := args[nParams]!
  let major := args[nParams + 1]!
  let minors := args[nParams + 2 : arity].toArray
  let extra := args[arity:].toArray
  let cResult ← costedFormOf (ctx.erase (← casesResultType ctx motive major))
  let pairType := mkApp2 (mkConst ``Prod [Level.zero, (← getLevel cResult).dec.get!])
    (mkConst ``Nat) cResult
  let pm ← translate ctx major
  bindPair pm fun cm vm => do
    let majorType := ctx.erase (← inferType major)
    let (n, ls, cparams) ← costedInductive majorType
    let motive' ← withLocalDecl `x .default (mkAppN (mkConst n ls) cparams) fun x =>
      mkLambdaFVars #[x] pairType
    let mut minors' := #[]
    for minor in minors, ctor in info.ctors do
      minors' := minors'.push (← translateMinor ctx minor ctor n ls cparams)
    let casesOn := mkAppN (mkConst (n ++ `casesOn) ((← getLevel pairType) :: ls))
      (cparams ++ #[motive', vm] ++ minors')
    let p ← bindPair casesOn fun cc vc => mkCostPair (add (add cm (natLit 1)) cc) vc
    translateApply ctx p extra

/-- The minor premise `minor` of `casesOn` for the constructor `ctor`, translated into a minor
premise of the costed form's `casesOn`: a lambda over the fields of the mirror constructor, with
each original field's costed form and erasure in scope for the body. The mirror constructor's
type is taken at the costed form's universes `ls` and parameters `cparams`. -/
partial def translateMinor (ctx : TCtx) (minor : Expr) (ctor n : Name) (ls : List Level)
    (cparams : Array Expr) : TermElabM Expr := do
  let ctorInfo ← getConstInfoCtor ctor
  -- The minor eta-expanded to all of the constructor's fields.
  let minor ← forallTelescopeReducing (← inferType minor) fun ys _ =>
    mkLambdaFVars ys (mkAppN minor ys).headBeta
  let mirrorCtor := ctor.updatePrefix n
  let layout ← layoutOf n mirrorCtor
  lambdaTelescope minor fun allFields body => do
    let fields := allFields[:ctorInfo.numFields].toArray
    let body ← mkLambdaFVars allFields[ctorInfo.numFields:].toArray body
    let mirrorCtorInfo ← getConstInfoCtor mirrorCtor
    let mirrorCtorType := mirrorCtorInfo.instantiateTypeLevelParams ls
    forallTelescope (← instantiateForall mirrorCtorType cparams) fun mfields _ => do
      let mut ctx := ctx
      let mut j := 0
      for x in fields, count in layout do
        let τ := ctx.erase (← inferType x)
        let (costed, erased) ← if count == 3 then
            pure (← joinSplit mfields[j]! mfields[j + 1]! mfields[j + 2]!, mfields[j]!)
          else if ← isDataLocal x then
            pure (mfields[j]!, ← erasureOf τ mfields[j]!)
          else pure (mfields[j]!, mfields[j]!)
        ctx := { ctx with costed := ctx.costed.insert x.fvarId! costed,
                          olds := ctx.olds.push x, news := ctx.news.push erased }
        j := j + count
      mkLambdaFVars mfields (← translate ctx body)

end

/-- `efficient_inst c := e` registers `e` as the instrumented version of the constant `c`, a
trusted assumption about cost: `e` must take the costed forms of `c`'s binders and return the
cost of a call with the costed form of its result. -/
syntax (name := efficientInst) "efficient_inst " ident " := " term : command

@[command_elab efficientInst] def elabEfficientInst : CommandElab
  | `(efficient_inst $fn:ident := $body:term) => do
    let c ← liftCoreM (realizeGlobalConstNoOverloadWithInfo fn)
    if let some e := instEntry? (← getEnv) c then
      throwError "efficient_inst: `{c}` already has the instrumented version `{e.inst}`"
    let instName := generatedName (← getEnv) c "inst"
    liftTermElabM do
      let value ← elabTerm body none
      synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      let type ← inferType value
      let levelParams := (collectLevelParams {} value).params.toList
      addAndCompile (.defnDecl { name := instName, levelParams, type, value,
                                 hints := .regular 0, safety := .safe })
    modifyEnv (instExt.addEntry · { fn := c, inst := instName, registered := true })
  | _ => throwUnsupportedSyntax

/-- `instrument c` derives the instrumented version of `c`, for tests. -/
syntax (name := instrumentCmd) "instrument " ident : command

@[command_elab instrumentCmd] def elabInstrument : CommandElab
  | `(instrument $fn:ident) => do
    let c ← liftCoreM (realizeGlobalConstNoOverloadWithInfo fn)
    liftTermElabM do discard <| ensureInst {} c
  | _ => throwUnsupportedSyntax

end Zcash.Meta.Translate
