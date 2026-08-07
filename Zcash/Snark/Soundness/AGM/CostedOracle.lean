import Zcash.Snark.Soundness.AGM.AdaptiveOnline

/-!
# Costed adaptive oracle computations

`LabeledOracleComp` deliberately records only random-oracle interaction.  This module adds a
small, erasable accounting language for the other finite resource used by the concrete AGM
endpoints: Vesta group work.  A group node is an explicit audit event; erasure removes those
events and leaves exactly the original labeled oracle tree.

The cost rules count additions, negations, scalar multiplications, and MSM terms.  This matches the
convention used by `AssembleGroupCost`: a primitive MSM costs one modeled group-work unit per term,
and its fixed-generator sweep and accumulated terms are charged explicitly.  Equality tests,
field operations, and list traversal are kept outside the DLOG group-operation budget.  In
particular, an adversary-sized scan must not be disguised as a shape-only group-work charge.

The costed program is the source of the modeled computation: erasure forgets its audit events and
produces the ordinary `LabeledOracleComp` used by the probability game.  In particular, this module
does **not** provide a zero-cost promotion from an arbitrary existing `LabeledOracleComp`; such a
promotion would make every finite-work certificate vacuous.  Construction of values passed to
`pure` is outside the staged program and therefore must be group-free.  Group-valued computation
inside the staged program goes through the reified constructors below.  This is a staging
contract, not extraction of the runtime cost of an arbitrary Lean term; connecting a concrete
implementation to the staged program remains an explicit modeling boundary.
-/

namespace Zcash.Snark

/-- Concrete Vesta group-law operations admitted by the staged adversary language.  The MSM node
carries its terms, so its price cannot be chosen independently of the computation. -/
inductive VestaGroupOperation where
  | add (left right : VestaG)
  | neg (point : VestaG)
  | scalarMul (scalar : Fp) (point : VestaG)
  | msm (terms : List (Fp × VestaG))
deriving DecidableEq

namespace VestaGroupOperation

/-- Concrete cost of one reified Vesta operation. -/
def cost : VestaGroupOperation → Nat
  | .add _ _ | .neg _ | .scalarMul _ _ => 1
  | .msm terms => terms.length

@[simp] theorem cost_add (left right : VestaG) : cost (.add left right) = 1 := rfl
@[simp] theorem cost_neg (point : VestaG) : cost (.neg point) = 1 := rfl
@[simp] theorem cost_scalarMul (scalar : Fp) (point : VestaG) :
    cost (.scalarMul scalar point) = 1 := rfl
@[simp] theorem cost_msm (terms : List (Fp × VestaG)) :
    cost (.msm terms) = terms.length := rfl

end VestaGroupOperation

/-- Internal syntax of a labeled adaptive oracle computation interleaved with explicit Vesta-work
events.  The syntax constructor is private; callers build programs through the smart API below,
so a group event and its computed result cannot be detached. -/
private inductive CostedLabeledOracleCompCore
    (T F : Type*) (Label : T → Type*) (α : Type*) where
  | mkPure (a : α)
  | mkQuery (t : T) (label : Label t)
      (k : F → CostedLabeledOracleCompCore T F Label α)
  | mkGroup (op : VestaGroupOperation) (next : CostedLabeledOracleCompCore T F Label α)

/-- Public abstract type of staged adaptive oracle programs. -/
structure CostedLabeledOracleComp (T F : Type*) (Label : T → Type*) (α : Type*) where
  private mk ::
  private core : CostedLabeledOracleCompCore T F Label α

namespace CostedLabeledOracleComp

variable {T F α β : Type*} {Label : T → Type*}

/-- Embed group-free data in a staged computation. -/
def pure (a : α) : CostedLabeledOracleComp T F Label α :=
  ⟨CostedLabeledOracleCompCore.mkPure a⟩

/-- Make one labeled random-oracle query. -/
def query (t : T) (label : Label t) (k : F → CostedLabeledOracleComp T F Label α) :
    CostedLabeledOracleComp T F Label α :=
  ⟨CostedLabeledOracleCompCore.mkQuery t label (fun answer => (k answer).core)⟩

private def eraseCore : CostedLabeledOracleCompCore T F Label α →
    LabeledOracleComp T F Label α
  | .mkPure a => .pure a
  | .mkQuery t label k => .query t label (fun answer => eraseCore (k answer))
  | .mkGroup _ next => eraseCore next

/-- Forget group-accounting nodes, preserving the exact labeled random-oracle computation. -/
def erase (A : CostedLabeledOracleComp T F Label α) : LabeledOracleComp T F Label α :=
  eraseCore A.core

/-- Run the erased computation against an ordinary oracle table. -/
def run (A : CostedLabeledOracleComp T F Label α) (O : T → F) : α :=
  A.erase.run O

private def groupWorkCore : CostedLabeledOracleCompCore T F Label α → (T → F) → Nat
  | .mkPure _, _ => 0
  | .mkQuery t _ k, O => groupWorkCore (k (O t)) O
  | .mkGroup op next, O => op.cost + groupWorkCore next O

/-- Group work on the adaptive path selected by one oracle table. -/
def groupWork (A : CostedLabeledOracleComp T F Label α) (O : T → F) : Nat :=
  groupWorkCore A.core O

/-- A structural worst-case group-work certificate. -/
def GroupWorkBound (A : CostedLabeledOracleComp T F Label α) (bound : Nat) : Prop :=
  ∀ O, A.groupWork O ≤ bound

/-- External staging judgment for the shallow cost language.  It means that construction of
`pure` payloads, query arguments, and host-language continuations performs no Vesta group-law
work except through the reified nodes of `A`.  Lean has no operational cost semantics for an
arbitrary host term, so this judgment is intentionally abstract: a concrete implementation or a
deeper embedded program must discharge it.  Keeping it in the certificate prevents a zero-cost
`pure` tree from being silently presented as an end-to-end mechanical work proof. -/
opaque StagedGroupWorkFaithful (A : CostedLabeledOracleComp T F Label α) : Prop

private def bindCore : CostedLabeledOracleCompCore T F Label α →
    (α → CostedLabeledOracleComp T F Label β) →
      CostedLabeledOracleCompCore T F Label β
  | .mkPure a, f => f a
      |>.core
  | .mkQuery t label k, f =>
      .mkQuery t label (fun answer => bindCore (k answer) f)
  | .mkGroup op next, f => .mkGroup op (bindCore next f)

/-- Sequence two costed computations. -/
def bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) :
    CostedLabeledOracleComp T F Label β :=
  ⟨bindCore A.core f⟩

/-- Apply a pure function without changing either oracle or group accounting. -/
def map (f : α → β) (A : CostedLabeledOracleComp T F Label α) :
    CostedLabeledOracleComp T F Label β :=
  A.bind (fun a => .pure (f a))

/-- Reified Vesta addition. -/
def vestaAdd (left right : VestaG) : CostedLabeledOracleComp T F Label VestaG :=
  ⟨.mkGroup (.add left right) (.mkPure (left + right))⟩

/-- Reified Vesta negation. -/
def vestaNeg (point : VestaG) : CostedLabeledOracleComp T F Label VestaG :=
  ⟨.mkGroup (.neg point) (.mkPure (-point))⟩

/-- Reified Vesta scalar multiplication. -/
def vestaScalarMul (scalar : Fp) (point : VestaG) :
    CostedLabeledOracleComp T F Label VestaG :=
  ⟨.mkGroup (.scalarMul scalar point) (.mkPure (scalar • point))⟩

/-- Vesta equality is a data comparison, not a group-law operation in the DLOG work model. -/
def vestaEq (left right : VestaG) : CostedLabeledOracleComp T F Label Bool :=
  .pure (decide (left = right))

/-- Modeled cost of the primitive MSM below: one work unit per input term, matching
`AssembleGroupCost`. -/
def vestaMsmCost (terms : List (Fp × VestaG)) : Nat :=
  terms.length

/-- Reified Vesta MSM.  Its cost is derived from the term list rather than accepted as a
caller-selected tag. -/
def vestaMsm (terms : List (Fp × VestaG)) :
    CostedLabeledOracleComp T F Label VestaG :=
  ⟨.mkGroup (.msm terms)
    (.mkPure ((terms.map fun term => term.1 • term.2).sum))⟩

/-- Reified Vesta MSM whose result retains its defining equation.  The dependent result lets a
later staged branch construct proof-carrying verifier output without trusting an unconnected host
value. -/
def vestaMsmCertified (terms : List (Fp × VestaG)) :
    CostedLabeledOracleComp T F Label
      {value : VestaG // value = (terms.map fun term => term.1 • term.2).sum} :=
  ⟨.mkGroup (.msm terms)
    (.mkPure ⟨(terms.map fun term => term.1 • term.2).sum, rfl⟩)⟩

@[simp] theorem erase_pure (a : α) :
    (pure a : CostedLabeledOracleComp T F Label α).erase = .pure a := rfl

@[simp] theorem erase_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) :
    (query t label k).erase = .query t label (fun answer => (k answer).erase) := rfl

private theorem eraseCore_bindCore (core : CostedLabeledOracleCompCore T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) :
    eraseCore (bindCore core f) =
      (eraseCore core).bind (fun a => (f a).erase) := by
  induction core with
  | mkPure => rfl
  | mkQuery t label k ih =>
      simp only [bindCore, eraseCore, LabeledOracleComp.bind]
      congr
      funext answer
      exact ih answer
  | mkGroup op next ih =>
      simpa only [bindCore, eraseCore] using ih

@[simp] theorem erase_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) :
    (A.bind f).erase = A.erase.bind (fun a => (f a).erase) := by
  rcases A with ⟨core⟩
  exact eraseCore_bindCore core f

@[simp] theorem run_pure (a : α) (O : T → F) :
    (pure a : CostedLabeledOracleComp T F Label α).run O = a := rfl

@[simp] theorem run_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).run O = (k (O t)).run O := rfl

@[simp] theorem run_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).run O = (f (A.run O)).run O := by
  simp only [run, erase_bind, LabeledOracleComp.run_bind]

@[simp] theorem run_vestaAdd (left right : VestaG) (O : T → F) :
    (vestaAdd (T := T) (F := F) (Label := Label) left right).run O = left + right := rfl

@[simp] theorem run_vestaNeg (point : VestaG) (O : T → F) :
    (vestaNeg (T := T) (F := F) (Label := Label) point).run O = -point := rfl

@[simp] theorem run_vestaScalarMul (scalar : Fp) (point : VestaG) (O : T → F) :
    (vestaScalarMul (T := T) (F := F) (Label := Label) scalar point).run O =
      scalar • point := rfl

@[simp] theorem run_vestaEq (left right : VestaG) (O : T → F) :
    (vestaEq (T := T) (F := F) (Label := Label) left right).run O =
      decide (left = right) := rfl

@[simp] theorem run_vestaMsm (terms : List (Fp × VestaG)) (O : T → F) :
    (vestaMsm (T := T) (F := F) (Label := Label) terms).run O =
      (terms.map fun term => term.1 • term.2).sum := rfl

@[simp] theorem run_vestaMsmCertified (terms : List (Fp × VestaG)) (O : T → F) :
    (vestaMsmCertified (T := T) (F := F) (Label := Label) terms).run O =
      ⟨(terms.map fun term => term.1 • term.2).sum, rfl⟩ := rfl

@[simp] theorem groupWork_pure (a : α) (O : T → F) :
    (pure a : CostedLabeledOracleComp T F Label α).groupWork O = 0 := rfl

@[simp] theorem groupWork_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).groupWork O = (k (O t)).groupWork O := rfl

private theorem groupWorkCore_bindCore
    (core : CostedLabeledOracleCompCore T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) (O : T → F) :
    groupWorkCore (bindCore core f) O =
      groupWorkCore core O + (f ((eraseCore core).run O)).groupWork O := by
  induction core with
  | mkPure a => simp [bindCore, groupWork, groupWorkCore, eraseCore, LabeledOracleComp.run]
  | mkQuery t label k ih =>
      simpa only [bindCore, groupWorkCore, eraseCore, LabeledOracleComp.run] using ih (O t)
  | mkGroup op next ih =>
      simp only [bindCore, groupWorkCore, eraseCore, LabeledOracleComp.run, ih, Nat.add_assoc]

@[simp] theorem groupWork_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).groupWork O = A.groupWork O + (f (A.run O)).groupWork O := by
  rcases A with ⟨core⟩
  exact groupWorkCore_bindCore core f O

@[simp] theorem groupWork_vestaAdd (left right : VestaG) (O : T → F) :
    (vestaAdd (T := T) (F := F) (Label := Label) left right).groupWork O = 1 := by
  simp [vestaAdd, groupWork, groupWorkCore]

@[simp] theorem groupWork_vestaNeg (point : VestaG) (O : T → F) :
    (vestaNeg (T := T) (F := F) (Label := Label) point).groupWork O = 1 := by
  simp [vestaNeg, groupWork, groupWorkCore]

@[simp] theorem groupWork_vestaScalarMul (scalar : Fp) (point : VestaG) (O : T → F) :
    (vestaScalarMul (T := T) (F := F) (Label := Label) scalar point).groupWork O = 1 := by
  simp [vestaScalarMul, groupWork, groupWorkCore]

@[simp] theorem groupWork_vestaEq (left right : VestaG) (O : T → F) :
    (vestaEq (T := T) (F := F) (Label := Label) left right).groupWork O = 0 := by
  simp [vestaEq]

@[simp] theorem groupWork_vestaMsm (terms : List (Fp × VestaG)) (O : T → F) :
    (vestaMsm (T := T) (F := F) (Label := Label) terms).groupWork O =
      vestaMsmCost terms := by
  simp [vestaMsm, vestaMsmCost, groupWork, groupWorkCore]

@[simp] theorem groupWork_vestaMsmCertified (terms : List (Fp × VestaG)) (O : T → F) :
    (vestaMsmCertified (T := T) (F := F) (Label := Label) terms).groupWork O =
      vestaMsmCost terms := by
  simp [vestaMsmCertified, vestaMsmCost, groupWork, groupWorkCore]

theorem groupWork_vestaMsm_pos (terms : List (Fp × VestaG)) (hterms : terms ≠ [])
    (O : T → F) :
    0 < (vestaMsm (T := T) (F := F) (Label := Label) terms).groupWork O := by
  cases terms with
  | nil => exact False.elim (hterms rfl)
  | cons head tail => simp [vestaMsmCost]

private def erasePreimage : LabeledOracleComp T F Label α →
    CostedLabeledOracleComp T F Label α
  | .pure a => pure a
  | .query t label k => query t label fun answer => erasePreimage (k answer)

private theorem erase_erasePreimage (A : LabeledOracleComp T F Label α) :
    (erasePreimage A).erase = A := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simp only [erasePreimage, erase_query]
      congr
      funext answer
      exact ih answer

/-- Erasure is expressive enough for every labeled adaptive oracle computation.  The witness is
intentionally opaque outside this module: this theorem supplies neither a group-work bound nor the
staging-fidelity judgment required by a cost certificate, so it cannot serve as a zero-cost
promotion API. -/
theorem erase_surjective (A : LabeledOracleComp T F Label α) :
    ∃ costed : CostedLabeledOracleComp T F Label α, costed.erase = A :=
  ⟨erasePreimage A, erase_erasePreimage A⟩

/-! ## Closing one selected oracle path

The complete reduction runs at a fixed oracle table.  The operation below specializes an
adaptive costed program to that table while retaining both the selected group nodes and the
query annotations accumulated on that same traversal.  It is deliberately implemented over the
private syntax: rebuilding only the returned value would lose the adversary's group-work trace.
-/

private def mapCore (f : α → β) : CostedLabeledOracleCompCore T F Label α →
    CostedLabeledOracleCompCore T F Label β
  | .mkPure a => .mkPure (f a)
  | .mkQuery t label k => .mkQuery t label (fun answer => mapCore f (k answer))
  | .mkGroup op next => .mkGroup op (mapCore f next)

private theorem groupWorkCore_mapCore (f : α → β)
    (core : CostedLabeledOracleCompCore T F Label α) (O : T → F) :
    groupWorkCore (mapCore f core) O = groupWorkCore core O := by
  induction core with
  | mkPure => rfl
  | mkQuery t label k ih => simpa only [mapCore, groupWorkCore] using ih (O t)
  | mkGroup op next ih => simp only [mapCore, groupWorkCore, ih]

private def materializeWithAnnotationsCertifiedCore (O : T → F) :
    (core : CostedLabeledOracleCompCore T F Label α) →
      CostedLabeledOracleCompCore Unit Unit (fun _ => Unit)
        {result : α × List (LabeledOracleComp.QueryAnnotation T Label) //
          result = (eraseCore core).runWithAnnotations O}
  | .mkPure a => .mkPure ⟨(a, []), rfl⟩
  | .mkQuery t label k =>
      mapCore (fun rest =>
        ⟨(rest.1.1, ⟨t, label⟩ :: rest.1.2), by rw [rest.2]; rfl⟩)
        (materializeWithAnnotationsCertifiedCore O (k (O t)))
  | .mkGroup op next => .mkGroup op (materializeWithAnnotationsCertifiedCore O next)

/-- Proof-carrying specialization of one oracle path.  The dependent result makes it possible for
a later costed continuation to consume the exact output/log pair without appealing to a parallel
host recomputation. -/
def materializeWithAnnotationsCertified
    (A : CostedLabeledOracleComp T F Label α) (O : T → F) :
    CostedLabeledOracleComp Unit Unit (fun _ => Unit)
      {result : α × List (LabeledOracleComp.QueryAnnotation T Label) //
        result = A.erase.runWithAnnotations O} :=
  ⟨materializeWithAnnotationsCertifiedCore O A.core⟩

private theorem materializeWithAnnotationsCertifiedCore_groupWork
    (core : CostedLabeledOracleCompCore T F Label α) (O : T → F) :
    groupWorkCore (materializeWithAnnotationsCertifiedCore O core) (fun _ => ()) =
      groupWorkCore core O := by
  induction core with
  | mkPure => rfl
  | mkQuery t label k ih =>
      simp only [materializeWithAnnotationsCertifiedCore, groupWorkCore_mapCore]
      exact ih (O t)
  | mkGroup op next ih =>
      simp only [materializeWithAnnotationsCertifiedCore, groupWorkCore]
      exact congrArg (op.cost + ·) ih

@[simp] theorem groupWork_materializeWithAnnotationsCertified
    (A : CostedLabeledOracleComp T F Label α) (O : T → F) :
    (materializeWithAnnotationsCertified A O).groupWork (fun _ => ()) = A.groupWork O := by
  rcases A with ⟨core⟩
  exact materializeWithAnnotationsCertifiedCore_groupWork core O

end CostedLabeledOracleComp

/-! ## Closed costed Vesta computations

Reduction postprocessing does not make oracle queries after its inputs have been materialized.  The
specialization below lets those computations use the same private costed syntax without inventing
a dummy trace record.  `run` and `groupWork` are both projections of the one syntax tree.
-/

/-- A closed costed computation whose only effects are reified Vesta group operations. -/
abbrev CostedVestaComp (α : Type*) :=
  CostedLabeledOracleComp Unit Unit (fun _ => Unit) α

namespace CostedVestaComp

variable {α β : Type*}

/-- Execute a closed costed Vesta computation. -/
def run (A : CostedVestaComp α) : α :=
  CostedLabeledOracleComp.run A (fun _ => ())

/-- Group work executed by the same closed program. -/
def groupWork (A : CostedVestaComp α) : Nat :=
  CostedLabeledOracleComp.groupWork A (fun _ => ())

/-- Embed group-free data. -/
def pure (a : α) : CostedVestaComp α :=
  CostedLabeledOracleComp.pure a

/-- Sequence two closed costed computations. -/
def bind (A : CostedVestaComp α) (f : α → CostedVestaComp β) : CostedVestaComp β :=
  CostedLabeledOracleComp.bind A f

/-- Apply a group-free function to a costed result. -/
def map (f : α → β) (A : CostedVestaComp α) : CostedVestaComp β :=
  bind A (fun a => pure (f a))

/-- Reified closed Vesta addition. -/
def vestaAdd (left right : VestaG) : CostedVestaComp VestaG :=
  CostedLabeledOracleComp.vestaAdd left right

/-- Reified closed Vesta negation. -/
def vestaNeg (point : VestaG) : CostedVestaComp VestaG :=
  CostedLabeledOracleComp.vestaNeg point

/-- Reified closed Vesta scalar multiplication. -/
def vestaScalarMul (scalar : Fp) (point : VestaG) : CostedVestaComp VestaG :=
  CostedLabeledOracleComp.vestaScalarMul scalar point

/-- Group-free equality over two already-computed Vesta points. -/
def vestaEq (left right : VestaG) : CostedVestaComp Bool :=
  CostedLabeledOracleComp.vestaEq left right

/-- Reified closed Vesta MSM. -/
def vestaMsm (terms : List (Fp × VestaG)) : CostedVestaComp VestaG :=
  CostedLabeledOracleComp.vestaMsm terms

/-- Reified closed MSM with its defining equation. -/
def vestaMsmCertified (terms : List (Fp × VestaG)) :
    CostedVestaComp
      {value : VestaG // value = (terms.map fun term => term.1 • term.2).sum} :=
  CostedLabeledOracleComp.vestaMsmCertified terms

/-- Execute a list of concrete MSMs in order and retain their values. -/
def evalMsms : List (List (Fp × VestaG)) → CostedVestaComp (List VestaG)
  | [] => pure []
  | terms :: rest =>
      bind (vestaMsm terms) fun value =>
        map (List.cons value) (evalMsms rest)

/-- Execute a list of MSMs while retaining a proof that every returned point is the evaluation of
its corresponding term list.  This dependent result is the value-coupling interface used by
reduction code that must feed the computed points into later verifier stages. -/
def evalMsmsCertified (termSets : List (List (Fp × VestaG))) :
    CostedVestaComp
      {values : List VestaG //
        values = termSets.map fun terms => (terms.map fun term => term.1 • term.2).sum} :=
  match termSets with
  | [] => pure ⟨[], rfl⟩
  | terms :: rest =>
      bind (vestaMsmCertified terms) fun value =>
        bind (evalMsmsCertified rest) fun values =>
          pure ⟨value.1 :: values.1, by rw [value.2, values.2]; rfl⟩

/-- Execute a matrix of MSMs, retaining both its row shape and the equation for every result. -/
def evalMsmMatrixCertified (matrix : List (List (List (Fp × VestaG)))) :
    CostedVestaComp
      {values : List (List VestaG) //
        values = matrix.map fun row =>
          row.map fun terms => (terms.map fun term => term.1 • term.2).sum} :=
  match matrix with
  | [] => pure ⟨[], rfl⟩
  | row :: rest =>
      bind (evalMsmsCertified row) fun values =>
        bind (evalMsmMatrixCertified rest) fun rows =>
          pure ⟨values.1 :: rows.1, by rw [values.2, rows.2]; rfl⟩

@[simp] theorem run_pure (a : α) : run (pure a) = a := rfl

@[simp] theorem run_bind (A : CostedVestaComp α) (f : α → CostedVestaComp β) :
    run (bind A f) = run (f (run A)) := by
  simp [run, bind]

@[simp] theorem run_map (f : α → β) (A : CostedVestaComp α) :
    run (map f A) = f (run A) := by
  rw [map, run_bind, run_pure]

@[simp] theorem run_vestaAdd (left right : VestaG) :
    run (vestaAdd left right) = left + right := rfl

@[simp] theorem run_vestaNeg (point : VestaG) : run (vestaNeg point) = -point := rfl

@[simp] theorem run_vestaScalarMul (scalar : Fp) (point : VestaG) :
    run (vestaScalarMul scalar point) = scalar • point := rfl

@[simp] theorem run_vestaEq (left right : VestaG) :
    run (vestaEq left right) = decide (left = right) := rfl

@[simp] theorem run_vestaMsm (terms : List (Fp × VestaG)) :
    run (vestaMsm terms) = (terms.map fun term => term.1 • term.2).sum := rfl

@[simp] theorem run_vestaMsmCertified (terms : List (Fp × VestaG)) :
    run (vestaMsmCertified terms) =
      ⟨(terms.map fun term => term.1 • term.2).sum, rfl⟩ := rfl

@[simp] theorem run_evalMsms (termSets : List (List (Fp × VestaG))) :
    run (evalMsms termSets) =
      termSets.map fun terms => (terms.map fun term => term.1 • term.2).sum := by
  induction termSets with
  | nil => rfl
  | cons terms rest ih => simp [evalMsms, ih]

@[simp] theorem run_evalMsmsCertified (termSets : List (List (Fp × VestaG))) :
    (run (evalMsmsCertified termSets)).1 =
      termSets.map fun terms => (terms.map fun term => term.1 • term.2).sum :=
  (run (evalMsmsCertified termSets)).2

@[simp] theorem run_evalMsmMatrixCertified
    (matrix : List (List (List (Fp × VestaG)))) :
    (run (evalMsmMatrixCertified matrix)).1 =
      matrix.map fun row =>
        row.map fun terms => (terms.map fun term => term.1 • term.2).sum :=
  (run (evalMsmMatrixCertified matrix)).2

@[simp] theorem groupWork_pure (a : α) : groupWork (pure a) = 0 := rfl

@[simp] theorem groupWork_bind (A : CostedVestaComp α) (f : α → CostedVestaComp β) :
    groupWork (bind A f) = groupWork A + groupWork (f (run A)) := by
  simp [groupWork, run, bind]

@[simp] theorem groupWork_map (f : α → β) (A : CostedVestaComp α) :
    groupWork (map f A) = groupWork A := by
  rw [map, groupWork_bind, groupWork_pure, Nat.add_zero]

@[simp] theorem groupWork_vestaAdd (left right : VestaG) :
    groupWork (vestaAdd left right) = 1 := by
  simp [groupWork, vestaAdd]

@[simp] theorem groupWork_vestaNeg (point : VestaG) : groupWork (vestaNeg point) = 1 := by
  simp [groupWork, vestaNeg]

@[simp] theorem groupWork_vestaScalarMul (scalar : Fp) (point : VestaG) :
    groupWork (vestaScalarMul scalar point) = 1 := by
  simp [groupWork, vestaScalarMul]

@[simp] theorem groupWork_vestaEq (left right : VestaG) :
    groupWork (vestaEq left right) = 0 := by
  simp [groupWork, vestaEq]

@[simp] theorem groupWork_vestaMsm (terms : List (Fp × VestaG)) :
    groupWork (vestaMsm terms) = terms.length := by
  simp [groupWork, vestaMsm, CostedLabeledOracleComp.vestaMsmCost]

@[simp] theorem groupWork_vestaMsmCertified (terms : List (Fp × VestaG)) :
    groupWork (vestaMsmCertified terms) = terms.length := by
  simp [groupWork, vestaMsmCertified, CostedLabeledOracleComp.vestaMsmCost]

@[simp] theorem groupWork_evalMsms (termSets : List (List (Fp × VestaG))) :
    groupWork (evalMsms termSets) = (termSets.map List.length).sum := by
  induction termSets with
  | nil => rfl
  | cons terms rest ih => simp [evalMsms, ih]

@[simp] theorem groupWork_evalMsmsCertified (termSets : List (List (Fp × VestaG))) :
    groupWork (evalMsmsCertified termSets) = (termSets.map List.length).sum := by
  induction termSets with
  | nil => rfl
  | cons terms rest ih => simp [evalMsmsCertified, ih]

@[simp] theorem groupWork_evalMsmMatrixCertified
    (matrix : List (List (List (Fp × VestaG)))) :
    groupWork (evalMsmMatrixCertified matrix) =
      (matrix.map fun row => (row.map List.length).sum).sum := by
  induction matrix with
  | nil => rfl
  | cons row rest ih => simp [evalMsmMatrixCertified, ih]

end CostedVestaComp
end Zcash.Snark
