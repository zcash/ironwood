import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Model

/-!
# Effects: outputs, spends, and the shielded pool balance

The effects of a valid ledger are read off its witnesses (Zcon3 "Understanding the
Security of Zcash" slides 20-21). An output is the `(rcm, note)` opening carried by an
action's output side, positioned by its leaf index; a spend is the opening carried by
an action's spend side, positioned by its witnessed path position. Zero-valued spends
are excluded — the statement's Merkle condition is vacuous for them, so they are
dummies by construction and do not need to correspond to any output.

`Opening` is exactly the pair that `noteCommitBreakOfNe` pins: once Balance-subset pins
a spend's commitment to an output's leaf, the two openings agree or a note-commitment
break is exhibited. The shielded pool balance is the output value total minus the
nonzero-spend value total.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}

/-- A note-commitment opening: the randomness and the note. This is the tuple a
commitment pins (up to `NoteCommitBreak`), and the unit of account for effects. -/
structure Opening (F G RHO PSI : Type*) where
  rcm : F
  note : Note G RHO PSI
  deriving DecidableEq

/-- An opening at a tree position: the leaf index for outputs, the witnessed path
position for spends. -/
structure PositionedOpening (F G RHO PSI : Type*) where
  pos : ℕ
  opening : Opening F G RHO PSI
  deriving DecidableEq

/-- All actions of a ledger, in order. Outputs, spends, and leaves are all per-action,
so their index correspondences reduce to `List.map` facts over this list. -/
def outputActions (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    List (Action KW F G RHO PSI MHASH MENC SIG d) :=
  ledger.flatMap fun tx => tx.actions

/-- The output-side opening of an action. -/
def outputOpening (a : Action KW F G RHO PSI MHASH MENC SIG d) : Opening F G RHO PSI :=
  ⟨a.w.rcm_new, a.w.note_new⟩

/-- The spend-side opening of an action, at its witnessed path position. -/
def spendRecord (a : Action KW F G RHO PSI MHASH MENC SIG d) :
    PositionedOpening F G RHO PSI :=
  ⟨posVal a.w.side, ⟨a.w.rcm_old, a.w.note_old⟩⟩

/-- The output openings of a ledger, in leaf order. -/
def outputOpenings (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    List (Opening F G RHO PSI) :=
  (outputActions ledger).map outputOpening

/-- The leaf list is the per-action map of the commitment over the flattened actions. -/
theorem leafList_eq_map (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    leafList ledger = (outputActions ledger).map fun a => a.inst.cmx_new := by
  rw [leafList, outputActions, List.map_flatMap]

/-- Outputs and leaves correspond one to one. -/
theorem outputOpenings_length (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    (outputOpenings ledger).length = (leafList ledger).length := by
  rw [outputOpenings, leafList_eq_map, List.length_map, List.length_map]

/-- The positioned outputs of the first `i` transactions: each output opening at its
leaf index. -/
def positionedOutputs (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    List (PositionedOpening F G RHO PSI) :=
  (outputOpenings (ledger.take i)).zipIdx.map fun p => ⟨p.2, p.1⟩

/-- The nonzero-valued spend actions of the first `i` transactions. -/
def spendActions (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    List (Action KW F G RHO PSI MHASH MENC SIG d) :=
  (ledger.take i).flatMap fun tx => tx.actions.filter fun a => a.w.note_old.v ≠ 0

/-- The nonzero-valued spends of the first `i` transactions, as a multiset of positioned
openings: the spend-side opening at the witnessed path position. A multiset because a
double spend must be countable; Balance-subset proves it is in fact a set. -/
def nonZeroSpends (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    Multiset (PositionedOpening F G RHO PSI) :=
  ↑((spendActions ledger i).map spendRecord)

/-- The shielded pool balance after the first `i` transactions: output value total minus
nonzero-spend value total, both read off the witnesses. -/
def shieldedPoolBalance (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) : ℤ :=
  (((positionedOutputs ledger i).map fun p => (p.opening.note.v : ℤ)).sum : ℤ)
    - ((nonZeroSpends ledger i).map fun p => (p.opening.note.v : ℤ)).sum

/-- The empty prefix holds an empty shielded pool. -/
@[simp] theorem shieldedPoolBalance_zero
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    shieldedPoolBalance ledger 0 = 0 := by
  simp [shieldedPoolBalance, positionedOutputs, nonZeroSpends, spendActions,
    outputOpenings, outputActions]

end Zcash.Security.Ledger.Model
