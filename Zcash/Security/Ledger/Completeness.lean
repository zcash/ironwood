import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.Spendability

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# Honest-spend completeness

The games constrain what an adversary can do. This module checks the other direction:
the protocol's intended use actually works. `HonestAction` packages what an honest
wallet knows for one Action. The spend may either be a dummy, or spend a note that
the wallet received; the package holds the spent note's opening and key witness, the
note's tree position under an anchor the ledger accepted, and fresh output data.
From that data alone we construct the Action (`witness`, `inst`, `action`) and prove
the Action statement (`satisfied`). An honest transaction (`honestTx`) bundles any
number of such Actions up to the action bound; appending it preserves ledger
validity (`honestTx_valid`).

The Merkle side rests on `Merkle.path_of_root`: the honest authentication data
exists because the referenced tree is defined (`root_defined`). Inclusion is only
required of nonzero-valued spends, so zero-valued dummy spends — whose path data is
arbitrary — are covered; `HonestAction.withDummySpend` constructs one. The honest
transaction declares its true net value, so the Balance game's transaction-balance
premiss holds for it (`txNetValue_honestTx`).

The Actions of one honest transaction may reference different anchors, matching the
model's per-action anchor rule — a documented simplification: deployed Orchard
encodes one anchor for the whole transaction (Sapling v4 allowed per-spend anchors).
The deployed case is the instance with all `anchor` fields equal.

`spendabilityOrBreak` is the Spendability capstone at this deterministic layer: the
owner of a received note can spend it. Either appending the honest transaction keeps
the ledger valid, or the ledger's own data computes the obstruction — an action
already spending the owner's exact opening (`Respend`, the case Spend Authority
covers), a note-commitment break, or a nullifier collision. The nullifier roadblock
is decided by searching the ledger for the revealing action and running the roadblock
inversion (`respendOrBreak`) against the owner's satisfied action.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

section Honest

variable [Field F] [AddCommGroup G] [Module F G]

/-- What an honest wallet knows for one Action. The spend may either be a dummy, or
spend a note that the wallet received; in the latter case the wallet supplies the
spent note's opening and key witness `kw`, the note's tree position `pos` under the
anchor after `anchor` transactions, and the output data with the signature
randomizer `α` and the value commitment randomness `rcv`. The opening comprises
`rcm_old`, `note_old`, and `cm_old`; the output data comprise `rcm_new`, `note_new`,
and `cm_new`. The Prop fields are the facts the wallet's own records give it;
`root_defined` holds for every anchor the ledger accepted, and `included` says the
tree position holds the spent commitment — required only of nonzero-valued spends,
so a zero-valued dummy may use arbitrary position data. -/
structure HonestAction (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth) where
  kw : KW
  rcm_old : F
  note_old : Note G RHO PSI
  cm_old : G
  /-- The spent note's tree position, leaf-to-root bits. -/
  pos : Fin P.depth → Bool
  /-- The referenced anchor is the root after this many transactions. -/
  anchor : ℕ
  rcm_new : F
  note_new : Note G RHO PSI
  cm_new : G
  α : F
  rcv : F
  /-- The spent note's commitment opens. -/
  commit_old : P.noteCommit rcm_old note_old = some cm_old
  /-- The key witness satisfies the key-binding condition. -/
  key_binding : kv.KB kw
  /-- The spent note is addressed to the key witness. -/
  pkd_eq : note_old.pkd = P.emb (kv.ivk kw) • note_old.gd
  /-- The spent note's diversified base is not zero. -/
  gd_ne : note_old.gd ≠ 0
  /-- The output note's commitment opens. -/
  commit_new : P.noteCommit rcm_new note_new = some cm_new
  /-- The output note's ρ is the revealed nullifier (ρ-uniqueness). -/
  ρ_new_eq : note_new.ρ = P.deriveNullifier (kv.nk kw) note_old.ρ note_old.ψ cm_old
  /-- Spent-note value range. -/
  v_old_lt : note_old.v < P.valueBound
  /-- Output-note value range. -/
  v_new_lt : note_new.v < P.valueBound
  /-- The anchor is at or before the ledger's end. -/
  anchor_le : anchor ≤ ledger.length
  /-- The referenced tree is defined (no compression along it escapes). -/
  root_defined : (rootAfter P ledger anchor).isSome
  /-- For a nonzero-valued spend, the tree position holds the spent commitment's
  extracted coordinate. A zero-valued dummy needs no inclusion. -/
  included : note_old.v ≠ 0 →
    leafFun P (leafList (ledger.take anchor)) pos = P.extract cm_old

namespace HonestAction

variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The referenced anchor value. -/
def rt (hs : HonestAction P kv ledger) : MHASH :=
  (rootAfter P ledger hs.anchor).get hs.root_defined

/-- The anchor equation, in the form `ValidLedger`'s anchor rule consumes. -/
theorem root_eq (hs : HonestAction P kv ledger) :
    rootAfter P ledger hs.anchor = some hs.rt :=
  (Option.some_get hs.root_defined).symm

/-- The honest authentication data exists because the referenced tree is defined. -/
theorem authChildren_isSome (hs : HonestAction P kv ledger) :
    (Merkle.authChildren P.merkle P.depth le_rfl
      (leafFun P (leafList (ledger.take hs.anchor))) hs.pos).isSome :=
  Merkle.authChildren_isSome P.merkle P.depth le_rfl _ hs.pos hs.root_eq

/-- The honest authentication data: at each height, the canonical encodings of the two
child subroots along the spent position's path. -/
def authData (hs : HonestAction P kv ledger) : Fin P.depth → MENC × MENC :=
  (Merkle.authChildren P.merkle P.depth le_rfl
    (leafFun P (leafList (ledger.take hs.anchor))) hs.pos).get hs.authChildren_isSome

/-- The witness of the honest Action. -/
def witness (hs : HonestAction P kv ledger) :
    ActionWitness KW F G RHO PSI MHASH MENC P.depth where
  path := hs.authData
  side := hs.pos
  note_old := hs.note_old
  note_new := hs.note_new
  cm_old := hs.cm_old
  cm_new := hs.cm_new
  kw := hs.kw
  α := hs.α
  rcv := hs.rcv
  rcm_old := hs.rcm_old
  rcm_new := hs.rcm_new

/-- The revealed nullifier of the honest spend. -/
def nf (hs : HonestAction P kv ledger) : RHO :=
  P.deriveNullifier (kv.nk hs.kw) hs.note_old.ρ hs.note_old.ψ hs.cm_old

/-- The public instance of the honest Action. -/
def inst (hs : HonestAction P kv ledger) : ActionInstance G MHASH RHO where
  rt := hs.rt
  nf_old := hs.nf
  rk := P.randomizePublic hs.α (kv.akP hs.kw)
  cv_net := P.valueCommit ((hs.note_old.v : ℤ) - hs.note_new.v) hs.rcv
  cmx_new := P.extract hs.cm_new

/-- **Statement completeness.** The honest Action satisfies the Action statement. The
Merkle conjunct is `Merkle.path_of_root` on the honest authentication data, with the
committed leaf rewritten to the spent commitment by `included`; every other conjunct
is a field or definitional. -/
theorem satisfied (hs : HonestAction P kv ledger) :
    ActionSatisfied P kv hs.inst hs.witness where
  commit_old := hs.commit_old
  merkle_path := fun hv => by
    have hauth : Merkle.authChildren P.merkle P.depth le_rfl
        (leafFun P (leafList (ledger.take hs.anchor))) hs.pos = some hs.authData :=
      (Option.some_get hs.authChildren_isSome).symm
    have hpath := Merkle.path_of_root P.merkle hs.pos hs.root_eq hauth
    rw [hs.included hv] at hpath
    exact hpath
  nf_old_eq := rfl
  key_binding := hs.key_binding
  pkd_eq := hs.pkd_eq
  gd_ne := hs.gd_ne
  rk_eq := rfl
  commit_new := hs.commit_new
  cmx_new_eq := rfl
  ρ_new_eq := hs.ρ_new_eq
  v_old_lt := hs.v_old_lt
  v_new_lt := hs.v_new_lt
  cv_net_eq := rfl

/-- The honest Action, with its spend-authorization signature. -/
def action (hs : HonestAction P kv ledger) (sig : SIG) :
    Action KW F G RHO PSI MHASH MENC SIG P.depth where
  inst := hs.inst
  w := hs.witness
  sig := sig

/-- A dummy note: zero value, addressed to `kw` (`pk_d = [ivk] g_d`) with diversified
base `gd`. The wallet's random samples (`gd`, `ρ`, `ψ`) are parameters, since the
model has no randomness. -/
def dummyNote (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK) (kw : KW) (gd : G) (ρ : RHO) (ψ : PSI) :
    Note G RHO PSI :=
  ⟨gd, P.emb (kv.ivk kw) • gd, 0, ρ, ψ⟩

/-- An honest Action whose spend half is a dummy: it spends `dummyNote` — with
default `ρ`/`ψ` samples and `rcm = 0` — at an arbitrary tree position (all-`false`).
This demonstrates that an honest wallet does not need a received note to create an
Action. The input side reduces to a nonzero `gd` and the definedness of the dummy's
commitment (`hcm`; `noteCommit` is partial), with the spent commitment recovered from
`hcm`; the spent-note value range reduces to `0 < P.valueBound`. Address integrity
and inclusion are discharged by construction (the latter vacuously). -/
def withDummySpend [Inhabited RHO] [Inhabited PSI] (kw : KW) (key_binding : kv.KB kw)
    (gd : G) (gd_ne : gd ≠ 0)
    (hcm : (P.noteCommit 0 (dummyNote P kv kw gd default default)).isSome)
    (hvb : 0 < P.valueBound)
    (anchor : ℕ) (anchor_le : anchor ≤ ledger.length)
    (root_defined : (rootAfter P ledger anchor).isSome)
    (rcm_new : F) (note_new : Note G RHO PSI) (cm_new : G)
    (commit_new : P.noteCommit rcm_new note_new = some cm_new)
    (ρ_new_eq : note_new.ρ = P.deriveNullifier (kv.nk kw) default default
      ((P.noteCommit 0 (dummyNote P kv kw gd default default)).get hcm))
    (v_new_lt : note_new.v < P.valueBound)
    (α rcv : F) : HonestAction P kv ledger where
  kw := kw
  rcm_old := 0
  note_old := dummyNote P kv kw gd default default
  cm_old := (P.noteCommit 0 (dummyNote P kv kw gd default default)).get hcm
  pos := fun _ => false
  anchor := anchor
  rcm_new := rcm_new
  note_new := note_new
  cm_new := cm_new
  α := α
  rcv := rcv
  commit_old := (Option.some_get hcm).symm
  key_binding := key_binding
  pkd_eq := rfl
  gd_ne := gd_ne
  commit_new := commit_new
  ρ_new_eq := ρ_new_eq
  v_old_lt := hvb
  v_new_lt := v_new_lt
  anchor_le := anchor_le
  root_defined := root_defined
  included := fun hv => absurd rfl hv

end HonestAction

variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The honest transaction over a list of honest Actions, each with its
spend-authorization signature: it declares the true summed net value and carries the
given binding signature. -/
def honestTx (spends : List (HonestAction P kv ledger × SIG)) (sighash : MSG)
    (bindingSig : SIG) :
    Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth where
  actions := spends.map fun p => p.1.action p.2
  vBalance := (spends.map fun p => (p.1.note_old.v : ℤ) - p.1.note_new.v).sum
  sighash := sighash
  bindingSig := bindingSig

/-- The honest transaction declares its true net value, so the Balance game's
transaction-balance premiss holds for it. -/
theorem txNetValue_honestTx (spends : List (HonestAction P kv ledger × SIG))
    (sighash : MSG) (bindingSig : SIG) :
    txNetValue (honestTx spends sighash bindingSig) = (honestTx spends sighash bindingSig).vBalance := by
  simp [txNetValue, honestTx, HonestAction.action, HonestAction.witness, List.map_map,
    Function.comp_def]

/-- The honest transaction's nullifier list is the spends' nullifiers, in order. -/
theorem nullifiers_honestTx (spends : List (HonestAction P kv ledger × SIG))
    (sighash : MSG) (bindingSig : SIG) :
    nullifiers [honestTx spends sighash bindingSig] = spends.map fun p => p.1.nf := by
  simp [nullifiers, honestTx, HonestAction.action, HonestAction.inst, List.map_map,
    Function.comp_def]

variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- **Ledger completeness.** Appending an honest transaction to a valid ledger keeps it
valid, given the boundary facts the wallet checks: the signatures verify over the
shared sighash, the revealed nullifiers are fresh and pairwise distinct, the tree has
room, the transparent pool stays nonnegative at the new index, and the action bound
admits the action count. Anchors transport by `rootAfter_prefix`, exactly as in
`validLedger_append`; the difference is that here the new transaction's own validity
conjuncts are proven from `HonestAction`, not assumed. -/
theorem honestTx_valid
    (hval : ValidLedger P kv issuance maxActions ledger)
    (spends : List (HonestAction P kv ledger × SIG)) (sighash : MSG)
    (bindingSig : SIG)
    (hsig : ∀ p ∈ spends,
      P.spendAuthVerify (P.randomizePublic p.1.α (kv.akP p.1.kw)) sighash p.2)
    (hfresh : ∀ p ∈ spends, p.1.nf ∉ nullifiers ledger)
    (hnodup : (spends.map fun p => p.1.nf).Nodup)
    (hcap : (leafList ledger).length + spends.length ≤ 2 ^ P.depth)
    (htrans : 0 ≤ transparentPoolBalance issuance ledger ledger.length
        + ((issuance ledger.length : ℤ) + (honestTx spends sighash bindingSig).vBalance))
    (hbind : P.bindingVerify ((honestTx spends sighash bindingSig).bvk P) sighash
        bindingSig)
    (hvb : (honestTx spends sighash bindingSig).vBalance.natAbs < P.valueBound)
    (hbound : spends.length ≤ maxActions) :
    ValidLedger P kv issuance maxActions (ledger ++ [honestTx spends sighash bindingSig]) := by
  have hmem : ∀ tx ∈ ledger ++ [honestTx spends sighash bindingSig],
      tx ∈ ledger ∨ tx = honestTx spends sighash bindingSig := by
    intro tx htx
    rcases List.mem_append.mp htx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hact : ∀ a ∈ (honestTx spends sighash bindingSig).actions,
      ∃ p ∈ spends, a = p.1.action p.2 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact ⟨p, hp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `satisfied`: per-Action; old Actions from `hval`, new ones from `HonestAction.satisfied`.
  · intro tx htx a ha
    rcases hmem tx htx with h | rfl
    · exact hval.satisfied tx h a ha
    · obtain ⟨p, hp, rfl⟩ := hact a ha
      exact p.1.satisfied
  -- `nf_nodup`: split at the append; the new nullifiers are pairwise distinct
  -- (`hnodup`) and fresh against the old list (`hfresh`).
  · rw [nullifiers_append, nullifiers_honestTx]
    refine List.nodup_append.mpr ⟨hval.nf_nodup, hnodup, ?_⟩
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact fun heq => hfresh p hp (heq ▸ hx)
  -- `anchor_valid`: old anchors transport along the extension by `rootAfter_prefix`;
  -- the new Actions' anchors are `root_eq`, transported the same way.
  · intro i a hai
    by_cases hi : (i : ℕ) < ledger.length
    · have hget : (ledger ++ [honestTx spends sighash bindingSig]).get i = ledger.get ⟨(i : ℕ), hi⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hi]
      rw [hget] at hai
      obtain ⟨j, hj, hrt⟩ := hval.anchor_valid ⟨(i : ℕ), hi⟩ a hai
      refine ⟨j, hj, ?_⟩
      rw [rootAfter_prefix P ⟨[honestTx spends sighash bindingSig], rfl⟩ (le_trans hj (le_of_lt hi))]
      exact hrt
    · have hieq : (i : ℕ) = ledger.length := by
        have := i.isLt
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hget : (ledger ++ [honestTx spends sighash bindingSig]).get i = honestTx spends sighash bindingSig := by
        simp [List.get_eq_getElem, hieq]
      rw [hget] at hai
      obtain ⟨p, hp, rfl⟩ := hact a hai
      refine ⟨p.1.anchor, hieq ▸ p.1.anchor_le, ?_⟩
      rw [rootAfter_prefix P ⟨[honestTx spends sighash bindingSig], rfl⟩ p.1.anchor_le]
      exact p.1.root_eq
  -- `capacity`: the honest transaction appends one leaf per spend.
  · rw [leafList_append]
    have hlen : (leafList [honestTx spends sighash bindingSig]).length = spends.length := by
      simp [leafList, honestTx]
    rw [List.length_append, hlen]
    exact hcap
  -- `sig_verifies`: old Actions from `hval`; new ones from `hsig` (the honest `rk`
  -- is the α-randomization of the key witness's `akP`).
  · intro tx htx a ha
    rcases hmem tx htx with h | rfl
    · exact hval.sig_verifies tx h a ha
    · obtain ⟨p, hp, rfl⟩ := hact a ha
      exact hsig p hp
  -- `binding_verified`: old transactions from `hval`; the new one is the boundary
  -- hypothesis `hbind`.
  · intro tx htx
    rcases hmem tx htx with h | rfl
    · exact hval.binding_verified tx h
    · exact hbind
  -- `vbalance_bound`: old from `hval`; the new declared balance is in range (`hvb`).
  · intro tx htx
    rcases hmem tx htx with h | rfl
    · exact hval.vbalance_bound tx h
    · exact hvb
  -- `transparent_nonneg`: prefix indices see the old balance; indices past the end
  -- saturate at the new length, where the balance steps by issuance plus `vBalance`
  -- (`htrans`).
  · intro i
    by_cases hi : i ≤ ledger.length
    · rw [transparentPoolBalance_append_of_le issuance hi]
      exact hval.transparent_nonneg i
    · rw [transparentPoolBalance_of_length_le issuance
        (by simp; omega), List.length_append, List.length_singleton,
        transparentPoolBalance_append_singleton]
      exact htrans
  -- `action_bound`: old transactions from `hval`; the new count is `hbound`.
  · intro tx htx
    rcases hmem tx htx with h | rfl
    · exact hval.action_bound tx h
    · simpa [honestTx] using hbound

/-! ## The Spendability capstone -/

/-- All actions of a ledger, each paired with its transaction — the searchable form
of "some action reveals this nullifier". -/
def actionsWithTx (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth) :
    List (Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth
      × Action KW F G RHO PSI MHASH MENC SIG P.depth) :=
  ledger.flatMap fun tx => tx.actions.map fun a => (tx, a)

/-- Membership in the paired action list gives both memberships. -/
theorem mem_of_mem_actionsWithTx
    {p : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth
      × Action KW F G RHO PSI MHASH MENC SIG P.depth}
    (h : p ∈ actionsWithTx ledger) : p.1 ∈ ledger ∧ p.2 ∈ p.1.actions := by
  obtain ⟨tx, htx, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  exact ⟨htx, ha⟩

/-- A revealed nullifier comes from some action of the paired list. -/
theorem exists_actionsWithTx_of_mem_nullifiers {x : RHO} (h : x ∈ nullifiers ledger) :
    ∃ p ∈ actionsWithTx ledger, p.2.inst.nf_old = x := by
  simp only [nullifiers, List.mem_flatMap, List.mem_map] at h
  obtain ⟨tx, htx, a, ha, rfl⟩ := h
  exact ⟨(tx, a),
    List.mem_flatMap.mpr ⟨tx, htx, List.mem_map.mpr ⟨a, ha, rfl⟩⟩, rfl⟩

/-- A ledger action spending the given opening. For the owner's opening this is the
roadblock's benign arm — the case Spend Authority covers: the action's signature
verifies under a randomization of ± the owner's key. -/
structure Respend (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth)
    (rcm : F) (note : Note G RHO PSI) where
  tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth
  htx : tx ∈ ledger
  a : Action KW F G RHO PSI MHASH MENC SIG P.depth
  ha : a ∈ tx.actions
  opening_eq : (a.w.rcm_old, a.w.note_old) = (rcm, note)

/-- **The Spendability capstone.** The owner of a received note — an `HonestAction` —
can spend it: either appending the honest transaction keeps the ledger valid, or the
ledger's own data computes the obstruction. The arms: an action already spending the
owner's exact opening (`Respend` — the case Spend Authority covers); a
note-commitment break; a nullifier collision. The nullifier roadblock is decided by
searching the ledger for the revealing action and running `respendOrBreak` against
the owner's satisfied action. -/
def spendabilityOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq NK]
    [DecidableEq RHO] [DecidableEq PSI]
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hs : HonestAction P kv ledger) (sig : SIG) (sighash : MSG) (bsig : SIG)
    (hsig : P.spendAuthVerify (P.randomizePublic hs.α (kv.akP hs.kw)) sighash sig)
    (hcap : (leafList ledger).length + 1 ≤ 2 ^ P.depth)
    (htrans : 0 ≤ transparentPoolBalance issuance ledger ledger.length
        + ((issuance ledger.length : ℤ) + (honestTx [(hs, sig)] sighash bsig).vBalance))
    (hbind : P.bindingVerify ((honestTx [(hs, sig)] sighash bsig).bvk P) sighash bsig)
    (hvb : (honestTx [(hs, sig)] sighash bsig).vBalance.natAbs < P.valueBound)
    (hbound : 1 ≤ maxActions) :
    ValidLedger P kv issuance maxActions (ledger ++ [honestTx [(hs, sig)] sighash bsig])
      ⊕' Respend ledger hs.rcm_old hs.note_old
      ⊕' (NoteCommitBreak P ⊕' NullifierCollision P) :=
  if hmem : hs.nf ∈ nullifiers ledger then
    have hex : ((actionsWithTx ledger).find? fun q => q.2.inst.nf_old = hs.nf).isSome := by
      rw [List.find?_isSome]
      obtain ⟨q, hq, hnf⟩ := exists_actionsWithTx_of_mem_nullifiers hmem
      exact ⟨q, hq, by simp [hnf]⟩
    let p := ((actionsWithTx ledger).find? fun q => q.2.inst.nf_old = hs.nf).get hex
    have hfind : (actionsWithTx ledger).find? (fun q => q.2.inst.nf_old = hs.nf)
        = some p := (Option.some_get hex).symm
    have hpmem := mem_of_mem_actionsWithTx (List.mem_of_find?_eq_some hfind)
    have hpnf : p.2.inst.nf_old = hs.nf := by
      have := List.find?_some hfind
      simpa using this
    have hsat : ActionSatisfied P kv p.2.inst p.2.w :=
      hval.satisfied p.1 hpmem.1 p.2 hpmem.2
    match respendOrBreak hsat hs.satisfied hpnf with
    | .inl heq => .inr (.inl ⟨p.1, hpmem.1, p.2, hpmem.2, heq⟩)
    | .inr b => .inr (.inr b)
  else
    .inl (honestTx_valid hval [(hs, sig)] sighash bsig
      (by rintro q hq; rw [List.mem_singleton] at hq; subst hq; exact hsig)
      (by rintro q hq; rw [List.mem_singleton] at hq; subst hq; exact hmem)
      (by simp)
      (by simpa using hcap)
      htrans
      hbind
      hvb
      (by simpa using hbound))

end Honest

end Zcash.Security.Ledger.Model
