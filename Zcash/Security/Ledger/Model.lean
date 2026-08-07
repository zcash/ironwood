import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Statement

/-!
# The witness-annotated ledger model

An annotated ledger is a list of transactions (we do not model blocks). Each
transaction carries its Actions, its net value balance, and the sighash its
spend-authorization signatures are over. Every action comes annotated with a
witness satisfying the Action statement — the oracle's hidden bookkeeping from
the ledger-games-design modelling. So the games quantify over all statement-
satisfying annotated ledgers — a superset of what a real adversary can reach.

The tree is a deterministic function of public data. Each action appends its
new note commitment's extracted coordinate `cmx_new`. An anchor is valid when
it is the Merkle root of the leaf list for some prefix of note commitments
ending at a transaction boundary, padded with `uncommitted`. Anchors are at
transaction granularity, so an action can never spend an output of its own
transaction.

`ValidLedger` collects the consensus rules the games consume: statement
satisfaction, nullifier uniqueness, anchor validity, tree capacity, signature
verification, nonnegativity of the transparent pool balance, and a
per-transaction action-count bound. `output_rho_nodup` is the ρ-uniqueness
lemma: output notes carry pairwise-distinct ρ, because each is equal to its
action's revealed nullifier. This is the mechanism for Faerie-Gold protection
in the Orchard protocol, and it needs no cryptographic hypothesis.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}

/-- One Action of a transaction: the public instance, the witness the oracle's
bookkeeping annotates it with, and the spend-authorization signature over the
transaction's sighash. -/
structure Action (KW F G RHO PSI MHASH MENC SIG : Type*) (d : ℕ) where
  inst : ActionInstance G MHASH RHO
  w : ActionWitness KW F G RHO PSI MHASH MENC d
  sig : SIG

/-- A transaction: its Actions, the net value flowing out of the pool (positive
`vBalance` means value leaving), the sighash its signatures are over, and its binding
signature (verified under `Tx.bvk` by validity). -/
structure Tx (KW F G RHO PSI MHASH MENC MSG SIG : Type*) (d : ℕ) where
  actions : List (Action KW F G RHO PSI MHASH MENC SIG d)
  vBalance : ℤ
  sighash : MSG
  bindingSig : SIG

/-- A ledger: a linearization of transactions (design doc, "Modelling decisions"). -/
abbrev Ledger (KW F G RHO PSI MHASH MENC MSG SIG : Type*) (d : ℕ) :=
  List (Tx KW F G RHO PSI MHASH MENC MSG SIG d)

/-- The tree position index of a path-position bit vector: bit `i` weighs `2^i`.
Defined as a fold over `List.finRange` rather than a `Finset` sum, to avoid an
unnecessary dependency on `Classical.choice`. -/
def posVal {d : ℕ} (pos : Fin d → Bool) : ℕ :=
  (List.finRange d).foldr (fun i acc => (pos i).toNat + 2 * acc) 0

/-- One bit off the front: the index is the low bit plus twice the rest. -/
theorem posVal_succ {d : ℕ} (pos : Fin (d + 1) → Bool) :
    posVal pos = (pos 0).toNat + 2 * posVal (fun i => pos i.succ) := by
  simp only [posVal, List.finRange_succ, List.foldr_cons, List.foldr_map]

/-- Position indices lie below the tree capacity. -/
theorem posVal_lt {d : ℕ} (pos : Fin d → Bool) : posVal pos < 2 ^ d := by
  induction d with
  | zero => simp [posVal]
  | succ d ih =>
      have h := ih fun i => pos i.succ
      have hb : (pos 0).toNat ≤ 1 := by cases pos 0 <;> simp
      rw [posVal_succ, pow_succ]
      omega

/-- The ledger's leaf list, from public data alone: each action appends its new note
commitment's extracted coordinate. -/
def leafList (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) : List MHASH :=
  ledger.flatMap fun tx => tx.actions.map fun a => a.inst.cmx_new

/-- The tree's leaf function for a leaf list: position `pos` holds the entry at index
`posVal pos`, and `uncommitted` past the end. -/
def leafFun (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) (l : List MHASH) :
    (Fin P.depth → Bool) → MHASH :=
  fun pos => l.getD (posVal pos) P.uncommitted

/-- The anchor after the first `j` transactions: the Merkle root of their leaf list, or
`none` if a compression along the honest tree escapes. This recomputes the full tree,
which is exponential in `depth` — fine for proofs, but evaluating at realistic depths
(e.g. against full-depth test vectors) would need the cached empty-subtree roots that
real implementations use. -/
def rootAfter (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth) (j : ℕ) : Option MHASH :=
  Merkle.root P.merkle (leafFun P (leafList (ledger.take j)))

/-- All nullifiers a ledger reveals, in order. -/
def nullifiers (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) : List RHO :=
  ledger.flatMap fun tx => tx.actions.map fun a => a.inst.nf_old

/-- The transparent chain value pool balance after the first `i` transactions: issuance
minted so far, plus the net value the shielded pool has released (positive `vBalance`
means value leaving the shielded pool). The model tracks the transparent pool only as
this overall balance — enough to model issuance and to state balance for nonzero value
balances, with no further transparent structure. -/
def transparentPoolBalance (issuance : ℕ → ℕ)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) : ℤ :=
  ((ledger.take i).zipIdx.map fun p => (issuance p.2 : ℤ) + p.1.vBalance).sum

/-- Prefix-roots persist: an anchor of `ledger` is an anchor of any extension of `ledger`. This is
what makes the tree append-only for the persistence argument. -/
theorem rootAfter_prefix (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    {ledger ledger' : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth} (hpre : ledger <+: ledger') {j : ℕ}
    (hj : j ≤ ledger.length) : rootAfter P ledger' j = rootAfter P ledger j := by
  obtain ⟨t, rfl⟩ := hpre
  rw [rootAfter, rootAfter, List.take_append_of_le_length hj]

/-- The leaf list distributes over ledger concatenation. -/
theorem leafList_append (ledger ledger' : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    leafList (ledger ++ ledger') = leafList ledger ++ leafList ledger' := by
  simp [leafList]

/-- A prefix balance ignores an extension: the first `i` transactions of `ledger ++ ledger'`
are those of `ledger` when `i` is within `ledger`. -/
theorem transparentPoolBalance_append_of_le (issuance : ℕ → ℕ)
    {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {i : ℕ} (hi : i ≤ ledger.length)
    (ledger' : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    transparentPoolBalance issuance (ledger ++ ledger') i =
      transparentPoolBalance issuance ledger i := by
  rw [transparentPoolBalance, transparentPoolBalance, List.take_append_of_le_length hi]

/-- The balance saturates at the ledger's length: taking more transactions than exist
changes nothing. -/
theorem transparentPoolBalance_of_length_le (issuance : ℕ → ℕ)
    {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {i : ℕ} (hi : ledger.length ≤ i) :
    transparentPoolBalance issuance ledger i =
      transparentPoolBalance issuance ledger ledger.length := by
  rw [transparentPoolBalance, transparentPoolBalance, List.take_of_length_le hi,
    List.take_length]

/-- The balance across an appended transaction: the previous total, plus the issuance
minted at the new index, plus the transaction's declared net value. -/
theorem transparentPoolBalance_append_singleton (issuance : ℕ → ℕ)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d)
    (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG d) :
    transparentPoolBalance issuance (ledger ++ [tx]) (ledger.length + 1) =
      transparentPoolBalance issuance ledger ledger.length
        + ((issuance ledger.length : ℤ) + tx.vBalance) := by
  rw [transparentPoolBalance, transparentPoolBalance, List.take_length,
    List.take_of_length_le (by simp), List.zipIdx_append, List.map_append, List.sum_append]
  simp

section Validity

variable [Field F] [AddCommGroup G] [Module F G]

/-- The binding verification key of a transaction: the sum of its actions' net value
commitments, minus a zero-randomness commitment to its declared `vBalance`
(`bvk = ∑ cv_net − ValueCommit_0(vBalance)`). -/
def Tx.bvk (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG d) : G :=
  (tx.actions.map fun a => a.inst.cv_net).sum - P.valueCommit tx.vBalance 0

/-- Validity of a witness-annotated ledger — the premiss of every game. `issuance` is the
intended issuance schedule and `maxActions` bounds each transaction's action count; both
are consensus data the games quantify over. -/
structure ValidLedger (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK) (issuance : ℕ → ℕ) (maxActions : ℕ)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth) : Prop where
  /-- Every action's witness satisfies the Action statement. -/
  satisfied : ∀ tx ∈ ledger, ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w
  /-- No nullifier is revealed twice (the consensus nullifier-set rule; this forbids
  duplicates even within one transaction). -/
  nf_nodup : (nullifiers ledger).Nodup
  /-- Each anchor is the root after some earlier transaction boundary: an action of
  transaction `i` (zero-based) may reference the tree after any `j ≤ i` transactions,
  so only outputs of strictly earlier transactions. The equation also asserts that the
  referenced tree is defined (no compression along it escapes). Anchors are
  per-action, a documented simplification: deployed Orchard encodes one anchor for
  the whole transaction (Sapling v4 allowed per-spend anchors), and per-action
  anchors only widen what the adversary may do. -/
  anchor_valid : ∀ i : Fin ledger.length, ∀ a ∈ (ledger.get i).actions,
    ∃ j ≤ (i : ℕ), rootAfter P ledger j = some a.inst.rt
  /-- The tree never overflows (the consensus capacity rule). -/
  capacity : (leafList ledger).length ≤ 2 ^ P.depth
  /-- Each action's spend-authorization signature verifies under its `rk`, over its
  transaction's sighash. -/
  sig_verifies : ∀ tx ∈ ledger, ∀ a ∈ tx.actions, P.spendAuthVerify a.inst.rk tx.sighash a.sig
  /-- Each transaction's binding signature verifies under its binding verification key,
  over its sighash (the consensus binding-signature rule). -/
  binding_verified : ∀ tx ∈ ledger, P.bindingVerify (tx.bvk P) tx.sighash tx.bindingSig
  /-- Each transaction's declared value balance is in range. The consensus rule
  (§7.1.2, [NU5 onward]) is `valueBalanceOrchard ∈ {-MAX_MONEY .. MAX_MONEY}` (inclusive;
  MAX_MONEY ~2^51 zatoshi), i.e. `|vBalance| <= MAX_MONEY`. This conjunct states the
  weaker `natAbs < valueBound` (= 2^64 at the intended instantiation), a loose consequence
  that suffices for the no-overflow bound in the integer-balance lift. -/
  vbalance_bound : ∀ tx ∈ ledger, tx.vBalance.natAbs < P.valueBound
  /-- The transparent pool balance never goes negative: a transaction can move value
  into the shielded pool only from issuance already minted, less what earlier
  transactions consumed. This is the consensus non-negative chain value balance rule for
  the transparent pool (ZIP 209). Stated cumulatively because transparent funds
  accumulate — a per-transaction bound against its own index's issuance would underpower
  the adversary. -/
  transparent_nonneg : ∀ i : ℕ, 0 ≤ transparentPoolBalance issuance ledger i
  /-- Bounded action count per transaction (consumed by the integer-balance lift). -/
  action_bound : ∀ tx ∈ ledger, tx.actions.length ≤ maxActions

variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}

/-- On a statement-satisfying ledger, the output notes' ρ list is the nullifier list:
each output's ρ is its action's revealed nullifier (`ρ_new_eq`). -/
theorem output_rho_eq_nullifiers
    (hsat : ∀ tx ∈ ledger, ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w) :
    (ledger.flatMap fun tx => tx.actions.map fun a => a.w.note_new.ρ) = nullifiers ledger := by
  induction ledger with
  | nil => rfl
  | cons tx ledger ih =>
      rw [List.flatMap_cons, nullifiers, List.flatMap_cons, ← nullifiers,
        ih fun tx' htx' a ha => hsat tx' (List.mem_cons_of_mem _ htx') a ha]
      congr 1
      exact List.map_congr_left fun a ha =>
        (hsat tx List.mem_cons_self a ha).ρ_new_eq

/-- **ρ-uniqueness.** A valid ledger's output notes carry pairwise-distinct ρ values,
because each equals its action's revealed nullifier and those are `Nodup`. So two
outputs of identical notes cannot occur, and a spent note determines the output that
created it — the Orchard Faerie-Gold protection, with no cryptographic hypothesis. -/
theorem output_rho_nodup {issuance : ℕ → ℕ} {maxActions : ℕ}
    (hval : ValidLedger P kv issuance maxActions ledger) :
    (ledger.flatMap fun tx => tx.actions.map fun a => a.w.note_new.ρ).Nodup := by
  rw [output_rho_eq_nullifiers hval.satisfied]
  exact hval.nf_nodup

end Validity

end Zcash.Security.Ledger.Model
