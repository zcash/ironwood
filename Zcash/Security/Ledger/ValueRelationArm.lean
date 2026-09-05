import Mathlib.Tactic.Ring
import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ExtractionKnowledgeError
import Zcash.Security.BindingSignature.DiscreteLog
import Zcash.Common.RelationProbabilityCoins

/-!
# The conservation relation arm in the oracle model

The capstone layer bounds the conservation reduction's relation arm by the named `ε_dlr`. This
module places that arm in the challenge-oracle model, at the reduction's own events: the
computable finder `valueRelFinder` replays the adversary and rebuilds the arm's nontrivial
`(𝒱, ℛ)` relation, and on every relation-arm sample it returns one
(`valueRelation_finder_isSomeAt`). The conservation experiment's combined finder consumes
both, taking the probability once for the two arms together. The arm contributes no
bad-challenge accounting: its witness is oracle-free data, the easier sibling of the
extraction-failure arm in `Ledger/ExtractionKnowledgeError.lean`, over the same experiment.

The reduction's relation branch fires at the prefix's first imbalanced transaction when the
extractor pins its binding key (`ValueRelationSelection`, computed from the reduction
hypothesis as in the extraction-failure arm). The finder (`valueRelFinder`) replays the
adversary at the presented basis, selects that transaction (`failTxOfAnn`), recomputes the
extractor's value from the run's own data, and rebuilds the relation behind decidable guards:
the integer imbalance, the no-overflow bound, and the binding-key equation are all decidable,
so the finder needs no validity proof. On an event sample the guards pass — validity supplies
the same facts the reduction derived — so the sample lands in the finder's relation-finding
event, and the tight Jaeger–Tessaro accounting applies. The relation lands in the generic AGM
witness type at the two value-commitment slots (`toAlgebraicRelationWitnessAt`), which is
where the distinctness hypothesis `v_idx ≠ r_idx` is consumed.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable (m : ℕ)

section Identification

variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}
variable {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The relation arm's selection, identified with the searched list's first imbalanced
transaction: `find?` selects `tx`, and the extractor pins its binding key. Computed data, in
the breaks-as-computed-data style. -/
structure ValueRelationSelection {shape : ValueShape P} (binding : BindingSigShape P shape)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth)) where
  tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth
  find : L.find? (fun tx => decide (txNetValue tx ≠ tx.vBalance)) = some tx
  extract_eq :
    tx.bvk P = extractor (tx.bvk P) tx.sighash (binding.toSig tx.bindingSig) • shape.Rbase

/-- The premiss fold's relation arm breaks at the first transaction of the list failing the
net-value equation, with the extractor pinning its key; the selection is computed from the
fold hypothesis. -/
def allConservedOrBreak_valueRelation
    (hval : ValidLedger P kv issuance maxActions ledger)
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth))
    (hL : ∀ tx ∈ L, tx ∈ ledger)
    {w : BindingSignature.NontrivialRelation (F := ZMod r) shape.Vbase shape.Rbase}
    (h : allConservedOrBreak
        (fun tx htx => shape.premissOrBreakFallible binding hval hr extractor tx htx) L hL
        = .inr (.inl w)) :
    ValueRelationSelection binding extractor L := by
  induction L with
  | nil => simp [allConservedOrBreak] at h
  | cons tx t ih =>
      rw [allConservedOrBreak] at h
      by_cases heq : txNetValue tx = tx.vBalance
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_pos heq] at h
        simp only at h
        split at h
        next brk hb =>
          simp only [PSum.inr.injEq] at h
          subst h
          obtain ⟨tx', hfind, hex⟩ := ih _ hb
          refine ⟨tx', ?_, hex⟩
          rw [List.find?_cons_of_neg (by simp [heq]), hfind]
        next hall => exact absurd h (by simp)
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_neg heq] at h
        by_cases hex : tx.bvk P
            = extractor (tx.bvk P) tx.sighash (binding.toSig tx.bindingSig) • shape.Rbase
        · exact ⟨tx, List.find?_cons_of_pos (by simp [heq]), hex⟩
        · rw [dif_neg hex] at h
          exact absurd h (by simp)

/-- The conservation reduction's relation arm at prefix `i` breaks at the prefix's first
imbalanced transaction, with the extractor pinning its key; the selection is computed from
the reduction hypothesis. -/
def balanceConservationOrBreak_valueRelation
    (hval : ValidLedger P kv issuance maxActions ledger)
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {w : BindingSignature.NontrivialRelation (F := ZMod r) shape.Vbase shape.Rbase}
    (h : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => shape.premissOrBreakFallible binding hval hr extractor tx htx) i
      = .inr (.inl w)) :
    ValueRelationSelection binding extractor (ledger.take i) := by
  rw [balanceConservationOrBreak] at h
  split at h
  next brk hb =>
    simp only [PSum.inr.injEq] at h
    subst h
    exact allConservedOrBreak_valueRelation hval shape binding hr extractor _ _ hb
  next hall => exact absurd h (by simp)

end Identification

section ArmBound

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The relation finder for the conservation relation arm: replay the labeled adversary at
the presented basis, select the prefix's first imbalanced transaction, recompute the
extractor's value from the run's own data, and rebuild the reduction's relation behind
decidable guards — the integer imbalance, the no-overflow bound, and the binding-key
equation. Computable, and free of any validity hypothesis: on an event sample the guards
pass because validity supplies the same facts the reduction derived. -/
def valueRelFinder (hne_idx : v_idx ≠ r_idx) (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (table : Q → ZMod r) (basis : Fin m → G) :
    Option (AlgebraicRelationWitness (F := ZMod r) basis) :=
  match failTxOfAnn m P₀ ((LA basis).run table) i with
  | none => none
  | some tx_rep =>
      letI tx := tx_rep.1
      letI bsk :=
        match (LA basis).findLabel table
            (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => tx_rep.2.key r_idx
      if h : (((txBundle tx).map Prod.fst).sum
            - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance ≠ 0)
          ∧ ((((txBundle tx).map Prod.fst).sum
            - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance).natAbs < r)
          ∧ bindingVK (basis v_idx) (basis r_idx) (castBundle (txBundle tx)) (castBundle [])
              (tx.vBalance : ZMod r) = bsk • basis r_idx then
        some ((NontrivialRelation.ofBundleIntImbalance (basis v_idx) (basis r_idx) (txBundle tx) []
            tx.vBalance bsk h.1 h.2.1 h.2.2).toAlgebraicRelationWitnessAt basis v_idx r_idx
          hne_idx rfl rfl)
      else none

omit [Fintype Q] [Inhabited Q] in
/-- On a relation-arm sample at the presented `basis` the finder returns a relation, for
the finder at any prefix `k` at least the failing prefix. The arm breaks at the first
imbalanced transaction of its prefix. That transaction is the same for every prefix
containing it, so one finder serves every prefix it covers. -/
theorem valueRelation_finder_isSomeAt [DecidableEq (ZMod r)]
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) {i k : ℕ} (hik : i ≤ k)
    {table : Q → ZMod r} {basis : Fin m → G}
    (hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis table) kv issuance
      maxActions (((LA basis).run table).map Prod.fst))
    {w : BindingSignature.NontrivialRelation (F := ZMod r)
      (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table).Vbase
      (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table).Rbase}
    (heq : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
          |>.premissOrBreakFallible (bindingAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
            hval hr (extractorAtBasis m r_idx queryOf P₀ k LA basis table) tx htx) i
      = .inr (.inl w)) :
    (valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis).isSome := by
  obtain ⟨tx, hfind, hex⟩ :=
    balanceConservationOrBreak_valueRelation hval _ _ hr
      (extractorAtBasis m r_idx queryOf P₀ k LA basis table) i heq
  have hex' : bvkAt m v_idx r_idx P₀ basis tx
      = extractorAtBasis m r_idx queryOf P₀ k LA basis table
          (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash
          (toSig tx.bindingSig) • basis r_idx := hex
  obtain ⟨tx_rep, hpr, hfst⟩ : ∃ tx_rep,
      failTxOfAnn m P₀ ((LA basis).run table) i = some tx_rep ∧ tx_rep.1 = tx := by
    rw [← List.map_take, List.find?_map] at hfind
    obtain ⟨tx_rep, hpr, hfst⟩ := Option.map_eq_some_iff.mp hfind
    exact ⟨tx_rep, hpr, hfst⟩
  obtain ⟨rep, rfl⟩ : ∃ rep, tx_rep = (tx, rep) := ⟨tx_rep.2, by rw [← hfst, Prod.mk.eta]⟩
  have hfindAnnK : failTxOfAnn m P₀ ((LA basis).run table) k = some (tx, rep) :=
    find?_take_eq_some_of_le hik hpr
  have hmem : (tx, rep) ∈ (LA basis).run table :=
    (List.take_sublist k _).subset (List.mem_of_find?_eq_some hfindAnnK)
  have htx : tx ∈ ((LA basis).run table).map Prod.fst :=
    List.mem_map_of_mem hmem
  -- the finder's recomputed extractor value is the extractor's
  have hbsk : extractorAtBasis m r_idx queryOf P₀ k LA basis table
        (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash (toSig tx.bindingSig)
      = (match (LA basis).findLabel table
            (queryOf (toSig tx.bindingSig).R
              (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => rep.key r_idx) := by
    unfold extractorAtBasis
    cases (LA basis).findLabel table
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx)
          tx.sighash) <;>
      simp [hfindAnnK]
    rfl
  -- decide the three guards from validity and the selection
  have heqtx : txNetValue tx ≠ tx.vBalance := by
    have := List.find?_some hfind
    simpa using this
  have hc1 : ((txBundle tx).map Prod.fst).sum
      - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance ≠ 0 := by
    simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
    exact sub_ne_zero.mpr heqtx
  have hc2 : (((txBundle tx).map Prod.fst).sum
      - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance).natAbs < r := by
    simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
    exact hval.imbalance_natAbs_lt hr htx
  have hc3 : bindingVK (basis v_idx) (basis r_idx)
      (castBundle (txBundle tx)) (castBundle []) (tx.vBalance : ZMod r)
      = (match (LA basis).findLabel table
            (queryOf (toSig tx.bindingSig).R
              (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => rep.key r_idx) • basis r_idx := by
    have hb := bvk_eq (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
      (hval.satisfied tx htx)
    rw [← hbsk]
    exact hb.symm.trans hex'
  unfold valueRelFinder
  rw [hfindAnnK]
  dsimp only
  rw [dif_pos ⟨hc1, hc2, hc3⟩]
  rfl

end ArmBound

end Zcash.Security.Ledger.Model
