import Zcash.Security.Ledger.ActionBundleBridge
import Zcash.Snark.Soundness.Action.AdaptiveCountReduction

/-!
# Adaptive-count Action-to-ledger bridge

Lift the existing bundle bridge over the count selected by one shared adaptive
Action execution.  The witness and every ledger datum are computed from that
selected output; no fixed-count family is rerun on a separate oracle table.
-/

namespace Zcash.Security.Ledger.AdaptiveActionBundleBridge

open Zcash.Circuits
open Zcash.Common
open Zcash.Security.Concrete
open Zcash.Security.Ledger.ActionBundleBridge
open Zcash.Security.Ledger.Bridge
open Zcash.Snark

variable {MSG SIG : Type*}

/-- Refine the witness extracted at the adaptively selected count into all of
that bundle's ledger data, or return the first Sinsemilla escape. -/
def selectedLedgerOutcome {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    let selected := (family.cachedExecution basis O).1
    Option ((∀ i, MemberLedgerData spendAuthVerify bindingVerify
      (selected.output.inputs i)) ⊕' ActionDLBreak) :=
  (family.selectedKnowledgeExtractor basis O).map fun witness ↦
    bundleLedgerData spendAuthVerify bindingVerify witness

/-- The ledger data extracted from the selected Action bundle. -/
def selectedLedgerExtractor {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    let selected := (family.cachedExecution basis O).1
    Option (∀ i, MemberLedgerData spendAuthVerify bindingVerify
      (selected.output.inputs i)) :=
  match selectedLedgerOutcome family spendAuthVerify bindingVerify basis O with
  | some (PSum.inl members) => some members
  | _ => none

/-- The first ledger-bridge escape exposed by the selected Action bundle. -/
def selectedLedgerEscapeFinder {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) : Option ActionDLBreak :=
  match selectedLedgerOutcome family spendAuthVerify bindingVerify basis O with
  | some (PSum.inr relation) => some relation
  | _ => none

/-- Selected ledger extraction fails exactly on an Action knowledge failure or
on a computed Sinsemilla escape from the extracted witness. -/
theorem selectedLedgerExtractor_eq_none_iff {maxActions : ℕ}
    (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    selectedLedgerExtractor family spendAuthVerify bindingVerify basis O = none ↔
      family.selectedKnowledgeExtractor basis O = none ∨
        (selectedLedgerEscapeFinder family spendAuthVerify bindingVerify basis O).isSome := by
  unfold selectedLedgerExtractor selectedLedgerEscapeFinder selectedLedgerOutcome
  cases houtcome : family.selectedKnowledgeExtractor basis O with
  | none => simp
  | some witness =>
      cases hbridge : bundleLedgerData spendAuthVerify bindingVerify witness with
      | inl members => simp only [Option.map_some]; rw [hbridge]; simp
      | inr relation => simp only [Option.map_some]; rw [hbridge]; simp

end Zcash.Security.Ledger.AdaptiveActionBundleBridge
