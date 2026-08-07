import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Balance
import Zcash.Security.BindingSignature.Balance

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# The transaction-balance premiss discharge at the Pedersen shape

The transaction-balance premiss —the witnessed net value matches the declared
`vBalance`, or a break of the abstract type `VB` is exhibited— is discharged here
against the binding-signature layer, with `VB` concretely the nontrivial `(Vbase, Rbase)`
discrete-log relation.

`ValueShape` is the Pedersen shape of the value commitment over the scalar field
`ZMod r`: `ValueCommit_rcv(v) = v • Vbase + rcv • Rbase` for fixed independent bases `Vbase` and
`Rbase` (𝒱^Orchard and ℛ^Orchard at the intended instantiation). The shape is that of the
deployed construction, but the bases stay abstract — the concrete Pallas
instantiation (Sinsemilla-derived bases, RedDSA on Pallas) is deferred, per the
abstract-route plan. On a statement-satisfying transaction the model's
binding verification key `Tx.bvk` — the sum of the actions' `cv_net`s minus a
zero-randomness commitment to `vBalance` — is then the binding-signature layer's
`bindingVK` of the witnessed bundle (`bvk_eq`, via `cv_net_eq`).

The premiss discharge itself lives in `Zcash.Security.Ledger.ExtractionArm`:
`ValueShape.premissOrBreakFallible` decides the net-value equation and, on failure,
computes the relation with `NontrivialRelation.ofBundleIntImbalance`, with the
extractor's failures exhibited as data. Its no-overflow bound comes from the
statement's value ranges, validity's action count and `vBalance` range, and one
numeric hypothesis `(maxActions + 1) * valueBound ≤ r` (deployed:
`(maxActions + 1) · 2^64 ≪ r ≈ 2^254`). A *total* extraction hypothesis — every
verifying `bvk` comes with its scalar — would carry no computational content: in a
cyclic group every `bvk` is some multiple of `Rbase`, so the total form holds for a
choose-the-witness extractor that no one can run. That is why the extractor is a
bare function and its failures are events with a named probability `κ`, discharged in
`RedDSA/KnowledgeError` (#107 tracks the surrounding glue).
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}
variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}

/-- The Pedersen shape of the value commitment, over the scalar field `ZMod r`:
`ValueCommit_rcv(v) = v • Vbase + rcv • Rbase` for fixed independent bases `Vbase` and `Rbase`
(𝒱^Orchard and ℛ^Orchard at the intended instantiation). -/
structure ValueShape (P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG) where
  Vbase : G
  Rbase : G
  commit_eq : ∀ (v : ℤ) (rcv : ZMod r),
    P.valueCommit v rcv = (v : ZMod r) • Vbase + rcv • Rbase

/-- A transaction's witnessed integer bundle: per action, the net value it releases
and its commitment randomness. -/
def txBundle (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG d) : List (ℤ × ZMod r) :=
  tx.actions.map fun a => ((a.w.note_old.v : ℤ) - a.w.note_new.v, a.w.rcv)

/-- The bundle's value sum is the transaction's witnessed net value. -/
theorem txBundle_fst_sum (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG d) :
    ((txBundle tx).map Prod.fst).sum = txNetValue tx := by
  simp [txBundle, txNetValue, List.map_map, Function.comp_def]

/-- On a statement-satisfying transaction, the model's binding verification key is the
binding-signature layer's `bindingVK` of the witnessed bundle. -/
theorem bvk_eq (S : ValueShape P)
    {tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (hsat : ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w) :
    tx.bvk P
      = bindingVK S.Vbase S.Rbase (castBundle (txBundle tx)) [] (tx.vBalance : ZMod r) := by
  have hsum : (tx.actions.map fun a => a.inst.cv_net).sum
      = ((castBundle (txBundle tx)).map fun p => valueCommit S.Vbase S.Rbase p.1 p.2).sum := by
    simp only [castBundle, txBundle, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
    rw [Function.comp_apply, Function.comp_apply, (hsat a ha).cv_net_eq, S.commit_eq]
    rfl
  have hvb : P.valueCommit tx.vBalance 0 = (tx.vBalance : ZMod r) • S.Vbase := by
    rw [S.commit_eq]
    simp
  rw [Tx.bvk, bindingVK, hsum, hvb]
  simp

/-- The witnessed net value of a satisfied transaction is bounded by the action count
times the value bound. -/
theorem txNetValue_natAbs_le
    {tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (hsat : ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w) :
    (txNetValue tx).natAbs ≤ tx.actions.length * P.valueBound := by
  suffices h : ∀ L : List (Action KW (ZMod r) G RHO PSI MHASH MENC SIG P.depth),
      (∀ a ∈ L, ActionSatisfied P kv a.inst a.w) →
      ((L.map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs
        ≤ L.length * P.valueBound by
    exact h tx.actions hsat
  intro L hL
  induction L with
  | nil => simp
  | cons a t ih =>
      have h1 : ((a.w.note_old.v : ℤ) - a.w.note_new.v).natAbs ≤ P.valueBound := by
        have hv1 := (hL a (by simp)).v_old_lt
        have hv2 := (hL a (by simp)).v_new_lt
        omega
      have h2 := ih fun x hx => hL x (by simp [hx])
      calc (((a :: t).map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs
          ≤ ((a.w.note_old.v : ℤ) - a.w.note_new.v).natAbs
            + ((t.map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs := by
            simp only [List.map_cons, List.sum_cons]
            exact Int.natAbs_add_le _ _
        _ ≤ P.valueBound + t.length * P.valueBound := Nat.add_le_add h1 h2
        _ = (a :: t).length * P.valueBound := by
            simp only [List.length_cons]
            ring

end Zcash.Security.Ledger.Model
