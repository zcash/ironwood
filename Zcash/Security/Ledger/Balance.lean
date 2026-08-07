import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.List.GetD
import Zcash.Security.Ledger.Effects

/-!
# Balance-subset: every nonzero spend is a committed output

The first Balance theorem, as a computed reduction. For a valid ledger, the nonzero
spends of the first `i + 1` transactions form a sub-multiset of the positioned outputs
of the first `i` — outputs of *strictly earlier* transactions (since an anchor
references the tree at a transaction boundary, a spend can never match an output of
its own transaction). Each spend is the opening of the output that created its
commitment, at that output's leaf position, and no positioned opening is spent twice;
otherwise the ledger's own data computes a `BalanceBreak`:

* a Merkle `Collision` — one height's compression collided, with both evaluations
  successful — when a spend's authentication path validates a leaf that is not the
  committed one;
* a `NoteCommitBreak`, when a spend's commitment matches an output's but their openings
  differ;
* a key-binding break, when two spends of one note tuple would otherwise have to reveal
  the same nullifier twice.

The shape of the argument (design doc, "The theorems"):

* the anchor pins each spend's path to a prefix tree;
* position binding pins the leaf;
* `uncommitted_ne` rules out the note commitment tree padding; and
* the opening comparison pins the output or computes the note-commitment break.

Duplicate spends of one positioned opening are found by `findPair`. Its result is
certified as a two-element *sublist*, which carries "two distinct occurrences" with
no index arithmetic.

Everything is a plain computable `def` per breaks-as-computed-data; the anchor index
and the duplicate pair are found by decidable search, so no data is conjured from the
validity hypothesis's existentials.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}

/-! ## Finding a duplicate, certified as a sublist -/

/-- Scan for the first two entries with equal images under `f`, returned in list order.
`findPair_spec` certifies them as a two-element sublist — which is what carries "two
distinct occurrences" without any index arithmetic — and `findPair_none` certifies that
a failed scan means the images are pairwise distinct. -/
def findPair {α β : Type*} [DecidableEq β] (f : α → β) : List α → Option (α × α)
  | [] => none
  | a :: t =>
    match t.find? fun b => f b = f a with
    | some b => some (a, b)
    | none => findPair f t

/-- A successful scan certifies its pair: equal images under `f`, and the two entries
form a two-element sublist of the input — distinct occurrences, in list order. -/
theorem findPair_spec {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l : List α} {a₁ a₂ : α}, findPair f l = some (a₁, a₂) →
      f a₁ = f a₂ ∧ List.Sublist [a₁, a₂] l
  | [], _, _, h => by simp [findPair] at h
  | a :: t, a₁, a₂, h => by
    rw [findPair] at h
    cases hf : t.find? fun b => f b = f a with
    | some b =>
        rw [hf] at h
        obtain ⟨rfl, rfl⟩ : a = a₁ ∧ b = a₂ := by simpa [eq_comm] using h
        refine ⟨?_, ?_⟩
        · have := List.find?_some hf
          simpa [eq_comm] using this
        · exact (List.singleton_sublist.mpr (List.mem_of_find?_eq_some hf)).cons_cons a
    | none =>
        rw [hf] at h
        obtain ⟨hfa, hsub⟩ := findPair_spec f h
        exact ⟨hfa, hsub.trans (List.sublist_cons_self a t)⟩

/-- A failed scan certifies that all images under `f` are pairwise distinct. -/
theorem findPair_none {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l : List α}, findPair f l = none → (l.map f).Nodup
  | [], _ => by simp
  | a :: t, h => by
    rw [findPair] at h
    cases hf : t.find? fun b => f b = f a with
    | some b => rw [hf] at h; exact absurd h (by simp)
    | none =>
        rw [hf] at h
        have hnot : ∀ b ∈ t, ¬ f b = f a := by
          have := List.find?_eq_none.mp hf
          simpa using this
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, findPair_none f h⟩
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
        exact hnot b hb hfb

/-! ## List plumbing: sublists and prefixes through the ledger's flat maps -/

/-- A pointwise sublist of chunks is a sublist of the flat maps. -/
theorem flatMap_sublist {α β : Type*} {l : List α} {g g' : α → List β}
    (h : ∀ x ∈ l, List.Sublist (g x) (g' x)) :
    List.Sublist (l.flatMap g) (l.flatMap g') := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih fun x hx => h x (by simp [hx]))

/-- A ledger prefix contributes a prefix of the flattened action list. -/
theorem outputActions_prefix {l₁ l₂ : Ledger KW F G RHO PSI MHASH MENC MSG SIG d}
    (h : l₁ <+: l₂) : outputActions l₁ <+: outputActions l₂ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨outputActions r, by simp [outputActions, List.flatMap_append]⟩

/-- A ledger prefix contributes a prefix of the revealed-nullifier list. -/
theorem nullifiers_prefix {l₁ l₂ : Ledger KW F G RHO PSI MHASH MENC MSG SIG d}
    (h : l₁ <+: l₂) : nullifiers l₁ <+: nullifiers l₂ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨nullifiers r, by simp [nullifiers, List.flatMap_append]⟩

/-- Earlier prefixes of a ledger are prefixes of later ones. -/
theorem take_prefix_take {l : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {j i : ℕ}
    (h : j ≤ i) : l.take j <+: l.take i := by
  have : l.take j = (l.take i).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.take_prefix j (l.take i)

/-- The spends' nullifiers sit inside the ledger's nullifier list, occurrence for
occurrence. -/
theorem spendActions_map_nf_sublist
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    List.Sublist ((spendActions ledger i).map fun a => a.inst.nf_old)
      (nullifiers ledger) := by
  have h1 : List.Sublist ((spendActions ledger i).map fun a => a.inst.nf_old)
      (nullifiers (ledger.take i)) := by
    rw [spendActions, nullifiers, List.map_flatMap]
    exact flatMap_sublist fun tx _ => tx.actions.filter_sublist.map _
  exact h1.trans (nullifiers_prefix (List.take_prefix i ledger)).sublist

/-- Leaves and output actions correspond index for index. -/
theorem length_leafList (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    (leafList ledger).length = (outputActions ledger).length := by
  rw [leafList_eq_map, List.length_map]

/-- A prefix agrees with the longer list at every index it has. -/
private theorem getElem_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {p : ℕ}
    (hp : p < l₁.length) : l₂[p]'(lt_of_lt_of_le hp h.length_le) = l₁[p] := by
  obtain ⟨r, rfl⟩ := h
  exact List.getElem_append_left hp

@[simp] theorem length_positionedOutputs
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    (positionedOutputs ledger i).length = (outputActions (ledger.take i)).length := by
  simp [positionedOutputs, outputOpenings]

/-- The `p`-th positioned output is the `p`-th output action's opening at position `p`. -/
theorem positionedOutputs_getElem
    {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {i p : ℕ}
    (hp : p < (outputActions (ledger.take i)).length) :
    (positionedOutputs ledger i)[p]'(by simpa using hp)
      = ⟨p, outputOpening ((outputActions (ledger.take i))[p])⟩ := by
  simp [positionedOutputs, outputOpenings]

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The break data a Balance violation computes: a tree-hash collision at one height, a
note-commitment opening collision, or a key-binding break on the two spends' key
witnesses. -/
inductive BalanceBreak (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK) where
  | merkle (c : Merkle.Collision P.merkle)
  | noteCommit (b : NoteCommitBreak P)
  | keyBinding (w₁ w₂ : KW) (h : kv.Break w₁ w₂)

/-- A spend whose commitment `extract`-matches an output's, with a different opening,
computes a note-commitment break — `noteCommitBreakOfNe`'s spend-versus-output twin. -/
def noteCommitBreakOfOutputNe {inst₁ inst₂ : ActionInstance G MHASH RHO}
    {w₁ w₂ : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hx : P.extract w₁.cm_old = P.extract w₂.cm_new)
    (hne : (w₁.rcm_old, w₁.note_old) ≠ (w₂.rcm_new, w₂.note_new)) :
    NoteCommitBreak P :=
  ⟨_, _, _, _, _, _, hne, h₁.commit_old, h₂.commit_new, hx, h₁.v_old_lt, h₂.v_new_lt⟩

/-- Membership in the spends carries statement satisfaction and nonzero value. -/
theorem satisfied_of_spendMem
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ spendActions ledger i) :
    ActionSatisfied P kv a.inst a.w ∧ a.w.note_old.v ≠ 0 := by
  obtain ⟨tx, htx, hafil⟩ := List.mem_flatMap.mp ha
  have htx' : tx ∈ ledger := (List.take_sublist i ledger).subset htx
  refine ⟨hval.satisfied tx htx' a (List.mem_of_mem_filter hafil), ?_⟩
  simpa using (List.mem_filter.mp hafil).2

/-- A spend's anchor is the root after some prefix within range. -/
theorem anchor_of_spendMem
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ spendActions ledger i) :
    ∃ j, j < i ∧ rootAfter P ledger j = some a.inst.rt := by
  obtain ⟨tx, htx, hafil⟩ := List.mem_flatMap.mp ha
  obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp htx
  have hki : k < i := lt_of_lt_of_le hk (by simp [List.length_take])
  have hkl : k < ledger.length := lt_of_lt_of_le hk (by simp [List.length_take])
  have hget : ledger.get ⟨k, hkl⟩ = tx := by
    rw [List.get_eq_getElem, ← List.getElem_take (h := hk)]
    exact hgetk
  obtain ⟨j, hjk, hrt⟩ := hval.anchor_valid ⟨k, hkl⟩ a
    (by rw [hget]; exact List.mem_of_mem_filter hafil)
  exact ⟨j, lt_of_le_of_lt hjk hki, hrt⟩

/-- **Per-spend pinning.** A nonzero spend of a valid ledger is the positioned opening
of the output that created its commitment — or the ledger data computes a `BalanceBreak`.
The anchor prefix is recovered by decidable search (`Nat.find`), so the branches stay
computable. -/
def spendPinnedOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth}
    (ha : a ∈ spendActions ledger (i + 1)) :
    (spendRecord a ∈ positionedOutputs ledger i) ⊕' BalanceBreak P kv :=
  have hex : ∃ j, j < i + 1 ∧ rootAfter P ledger j = some a.inst.rt :=
    anchor_of_spendMem hval ha
  let j := Nat.find hex
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Nat.find_spec hex).1
  have hpath : Merkle.Path P.merkle (P.extract a.w.cm_old) a.inst.rt a.w.path a.w.side :=
    (satisfied_of_spendMem hval ha).1.merkle_path (satisfied_of_spendMem hval ha).2
  have hroot : Merkle.root P.merkle (leafFun P (leafList (ledger.take j)))
      = some a.inst.rt := (Nat.find_spec hex).2
  if hleaf : P.extract a.w.cm_old = leafFun P (leafList (ledger.take j)) a.w.side then
    if hp : posVal a.w.side < (leafList (ledger.take j)).length then
      have hpa : posVal a.w.side < (outputActions (ledger.take j)).length := by
        rwa [← length_leafList]
      let out := (outputActions (ledger.take j))[posVal a.w.side]
      have hcx : P.extract a.w.cm_old = out.inst.cmx_new := by
        rw [hleaf, leafFun, List.getD_eq_getElem _ _ hp]
        have := leafList_eq_map (ledger.take j)
        simp only [out, this, List.getElem_map]
      have hout_sat : ActionSatisfied P kv out.inst out.w := by
        have hmem : out ∈ outputActions (ledger.take j) := List.getElem_mem hpa
        obtain ⟨tx, htx, hout⟩ := List.mem_flatMap.mp hmem
        exact hval.satisfied tx ((List.take_sublist j ledger).subset htx) out hout
      if hop : (⟨a.w.rcm_old, a.w.note_old⟩ : Opening F G RHO PSI) = outputOpening out then
        .inl (by
          have hpre : outputActions (ledger.take j) <+: outputActions (ledger.take i) :=
            outputActions_prefix (take_prefix_take hji)
          have hpi : posVal a.w.side < (outputActions (ledger.take i)).length :=
            lt_of_lt_of_le hpa hpre.length_le
          refine List.mem_iff_getElem.mpr ⟨posVal a.w.side, by simpa using hpi, ?_⟩
          rw [positionedOutputs_getElem hpi, getElem_of_prefix hpre hpa]
          rw [spendRecord, ← hop])
      else
        .inr (.noteCommit (noteCommitBreakOfOutputNe (satisfied_of_spendMem hval ha).1
          hout_sat (hcx.trans hout_sat.cmx_new_eq)
          (fun hpair => hop (by
            simp only [Prod.mk.injEq] at hpair
            simp [outputOpening, hpair.1, hpair.2]))))
    else
      absurd (by
          rw [hleaf, leafFun, List.getD_eq_default]
          omega) (P.uncommitted_ne a.w.cm_old)
  else
    .inr (.merkle (Merkle.collisionOfWrongLeaf P.merkle hpath hroot hleaf))

/-- Run the per-spend pinning over a list of spends, stopping at the first break. -/
def allPinnedOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ} :
    (L : List (Action KW F G RHO PSI MHASH MENC SIG P.depth)) →
    (∀ a ∈ L, a ∈ spendActions ledger (i + 1)) →
    ((∀ a ∈ L, spendRecord a ∈ positionedOutputs ledger i) ⊕' BalanceBreak P kv)
  | [], _ => .inl (by simp)
  | a :: t, hL =>
    match spendPinnedOrBreak hval (hL a (by simp)) with
    | .inr b => .inr b
    | .inl hmem =>
      match allPinnedOrBreak hval t (fun x hx => hL x (by simp [hx])) with
      | .inr b => .inr b
      | .inl hall => .inl (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          exacts [hmem, hall x hx'])

/-- **Balance-subset, as a computed reduction.** For a valid ledger, the nonzero spends
of the first `i + 1` transactions are a sub-multiset of the positioned outputs of the
first `i` — or the ledger data computes a `BalanceBreak`. The one-transaction lag is the
strictly-earlier constraint: an anchor references a transaction boundary, so a spend
never matches an output of its own transaction. Duplicate spends are located by
`findPair`; sharing a positioned opening forces sharing a revealed nullifier
(`nfOldEqOrBreak`), which nullifier uniqueness forbids, so the surviving branch is a
key-binding break. -/
def balanceSubsetOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
    [NoZeroSMulDivisors F G]
    (hval : ValidLedger P kv issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i)) ⊕' BalanceBreak P kv :=
  match hfp : findPair spendRecord (spendActions ledger (i + 1)) with
  | some (a₁, a₂) =>
      have hspec := findPair_spec spendRecord hfp
      have h₁ : a₁ ∈ spendActions ledger (i + 1) := hspec.2.subset (by simp)
      have h₂ : a₂ ∈ spendActions ledger (i + 1) := hspec.2.subset (by simp)
      have hrcm : a₁.w.rcm_old = a₂.w.rcm_old := by
        have := congrArg (fun r => r.opening.rcm) hspec.1
        simpa [spendRecord] using this
      have hnote : a₁.w.note_old = a₂.w.note_old := by
        have := congrArg (fun r => r.opening.note) hspec.1
        simpa [spendRecord] using this
      match nfOldEqOrBreak (satisfied_of_spendMem hval h₁).1
          (satisfied_of_spendMem hval h₂).1 hrcm hnote with
      | .inr hbr => .inr (.keyBinding a₁.w.kw a₂.w.kw hbr)
      | .inl hnf =>
          -- one nullifier at two distinct occurrences — impossible in a valid ledger
          have hsubnf : List.Sublist [a₁.inst.nf_old, a₂.inst.nf_old] (nullifiers ledger) := by
            have h := (hspec.2.map fun a => a.inst.nf_old).trans
              (spendActions_map_nf_sublist ledger (i + 1))
            simpa using h
          have hnd : [a₁.inst.nf_old, a₂.inst.nf_old].Nodup :=
            hval.nf_nodup.sublist hsubnf
          absurd hnf (by simpa using hnd)
  | none =>
      have hnodup : ((spendActions ledger (i + 1)).map spendRecord).Nodup :=
        findPair_none spendRecord hfp
      match allPinnedOrBreak hval (spendActions ledger (i + 1)) (fun _ h => h) with
      | .inr b => .inr b
      | .inl hall =>
          .inl (by
            rw [nonZeroSpends]
            refine (Multiset.le_iff_subset (by simpa using hnodup)).mpr ?_
            intro x hx
            obtain ⟨a, haL, rfl⟩ := List.mem_map.mp (by simpa using hx)
            simpa using hall a haL)

/-- The key-binding arm's witness pair, when the break lies in that arm. -/
def BalanceBreak.kbPair : BalanceBreak P kv → Option (KW × KW)
  | .keyBinding w₁ w₂ _ => some (w₁, w₂)
  | .merkle _ => none
  | .noteCommit _ => none

/-- The key-binding pair read directly off the ledger: the two key witnesses of the
duplicate positioned opening that `findPair` locates. Oracle-free — it consumes no
validity proof — so an oracle machine can output it. `balanceSubsetOrBreak_kbPair` shows
it is exactly the pair of whatever break the reduction computes. -/
def kbPairOf [DecidableEq F] [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI]
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth) (i : ℕ) :
    Option (KW × KW) :=
  (findPair spendRecord (spendActions ledger (i + 1))).map fun p => (p.1.w.kw, p.2.w.kw)

/-- Per-spend pinning never computes a key-binding break: its breaks are the
note-commitment collision (`hop` fails) and the Merkle collision (`hleaf` fails). -/
theorem spendPinnedOrBreak_kbPair [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth}
    (ha : a ∈ spendActions ledger (i + 1)) {b : BalanceBreak P kv} :
    spendPinnedOrBreak hval ha = .inr b → b.kbPair = none := by
  revert b
  fun_cases spendPinnedOrBreak hval ha <;>
    intro b hb <;>
    (try simp_all only [reduceCtorEq, PSum.inr.injEq, BalanceBreak.kbPair]) <;>
    (subst hb; rfl)

/-- The pinning scan never computes a key-binding break (`spendPinnedOrBreak_kbPair`,
propagated through the recursion). -/
theorem allPinnedOrBreak_kbPair [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ} :
    ∀ (L : List (Action KW F G RHO PSI MHASH MENC SIG P.depth))
      (hL : ∀ a ∈ L, a ∈ spendActions ledger (i + 1)) {b : BalanceBreak P kv},
      allPinnedOrBreak hval L hL = .inr b → b.kbPair = none := by
  intro L
  induction L with
  | nil => intro hL b hb; simp only [allPinnedOrBreak, reduceCtorEq] at hb
  | cons a t ih =>
      intro hL b hb
      rw [allPinnedOrBreak] at hb
      split at hb
      · rename_i b' hsp
        rw [PSum.inr.injEq] at hb; subst hb
        exact spendPinnedOrBreak_kbPair hval _ hsp
      · split at hb
        · rename_i b' hall
          rw [PSum.inr.injEq] at hb; subst hb
          exact ih (fun x hx => hL x (by simp [hx])) hall
        · simp only [reduceCtorEq] at hb

/-- **Key-binding-arm localization.** Whatever break `balanceSubsetOrBreak` computes, its
key-binding pair is the oracle-free `kbPairOf`: a key-binding break arises only from the
`findPair` duplicate, whose pair is `kbPairOf`, and every other break has no pair. This is
what lets an oracle machine output the arm's pair without running the reduction. -/
theorem balanceSubsetOrBreak_kbPair [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
    [NoZeroSMulDivisors F G]
    (hval : ValidLedger P kv issuance maxActions ledger) (i : ℕ) {b : BalanceBreak P kv} :
    balanceSubsetOrBreak hval i = .inr b → b.kbPair = kbPairOf ledger i := by
  revert b
  fun_cases balanceSubsetOrBreak hval i <;> intro b hb <;>
    (try (rw [PSum.inr.injEq] at hb; subst hb)) <;>
    (try simp_all only [reduceCtorEq])
  · -- key-binding break from a `findPair` duplicate: its pair is `kbPairOf`
    simp_all [BalanceBreak.kbPair, kbPairOf]
  · -- no duplicate: the pinning scan's break has no pair, and `kbPairOf` is `none`
    rename_i hfpNone _ _ hallp
    have hnone := allPinnedOrBreak_kbPair hval _ _ hallp
    simp [kbPairOf, hfpNone, hnone]

end Validity

/-! ## Balance conservation

The ledger balances: what the shielded pool holds plus what the transparent pool
holds is exactly what issuance has minted —up to a transaction-balance premiss— and
both pool balances are non-negative. The premiss says each transaction's witnessed
net value matches its declared `vBalance`, or a balance break of the caller's type
is exhibited. The intended deployed discharge is the binding-signature machinery
(`NontrivialRelation.ofBundleIntImbalance` with the statement's value ranges and the
action-count bound), with a nontrivial discrete-log relation as the break. That glue
is formalized —`ValueShape.premissOrBreakFallible` in `ExtractionArm.lean`, against
`ValidLedger.binding_verified`— with the extractor a bare function and its failures
exhibited as data, bounded by the named knowledge error `κ` (see `Value.lean`'s
module doc for why a total extraction hypothesis would carry no computational
content).

Modulo that named bound, and given the transparent pool balance never goes negative
(`ValidLedger.transparent_nonneg`), a corollary is that the shielded pool holds at
most what was minted. -/

/-- A transaction's net value, read off its witnesses: spent minus created, over all
actions (zero-valued dummies contribute zero). -/
def txNetValue (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG d) : ℤ :=
  (tx.actions.map fun a => (a.w.note_old.v : ℤ) - a.w.note_new.v).sum

/-- The issuance minted alongside the first `i` transactions. -/
def issuanceTotal (issuance : ℕ → ℕ)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) : ℤ :=
  ((ledger.take i).zipIdx.map fun p => (issuance p.2 : ℤ)).sum

section SumToolbox

/-- Summing over a flat map is summing the per-chunk sums. -/
private theorem sum_flatMap {α β : Type*} (g : α → List β) (f : β → ℤ) (l : List α) :
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- The sum of pointwise differences is the difference of sums. -/
private theorem sum_map_sub {α : Type*} (f g : α → ℤ) (l : List α) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Mapping a function of the entry over an index-zipped list ignores the indices. -/
private theorem map_zipIdx_fst {α β : Type*} {f : α → β} :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map fun p => f p.1) = l.map f
  | [], _ => rfl
  | a :: t, n => by
    simp only [List.zipIdx_cons, List.map_cons]
    rw [map_zipIdx_fst t (n + 1)]

end SumToolbox

/-- The transparent pool balance splits into minted issuance plus declared balances. -/
theorem transparentPoolBalance_eq (issuance : ℕ → ℕ)
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    transparentPoolBalance issuance ledger i
      = issuanceTotal issuance ledger i
        + ((ledger.take i).map fun tx => tx.vBalance).sum := by
  rw [transparentPoolBalance, issuanceTotal, List.sum_map_add, map_zipIdx_fst]

/-- The outputs' value total, transaction by transaction. -/
theorem positionedOutputs_value_sum
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    ((positionedOutputs ledger i).map fun p => (p.opening.note.v : ℤ)).sum
      = ((ledger.take i).map fun tx =>
          (tx.actions.map fun a => (a.w.note_new.v : ℤ)).sum).sum := by
  rw [positionedOutputs, List.map_map]
  rw [show ((fun p : PositionedOpening F G RHO PSI => (p.opening.note.v : ℤ))
        ∘ fun p : Opening F G RHO PSI × ℕ => (⟨p.2, p.1⟩ : PositionedOpening F G RHO PSI))
      = fun p : Opening F G RHO PSI × ℕ => (p.1.note.v : ℤ) from rfl]
  rw [show ((outputOpenings (ledger.take i)).zipIdx.map fun p => (p.1.note.v : ℤ))
      = (outputOpenings (ledger.take i)).map fun o => (o.note.v : ℤ) from
    map_zipIdx_fst (f := fun o : Opening F G RHO PSI => (o.note.v : ℤ)) _ 0]
  rw [outputOpenings, List.map_map]
  rw [show ((fun o : Opening F G RHO PSI => (o.note.v : ℤ)) ∘ outputOpening)
      = fun a : Action KW F G RHO PSI MHASH MENC SIG d => (a.w.note_new.v : ℤ) from rfl]
  rw [outputActions, sum_flatMap]

/-- The nonzero spends' value total is every spend's value total: the filtered-out
spends have value zero. -/
theorem nonZeroSpends_value_sum
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    ((nonZeroSpends ledger i).map fun p => (p.opening.note.v : ℤ)).sum
      = ((ledger.take i).map fun tx =>
          (tx.actions.map fun a => (a.w.note_old.v : ℤ)).sum).sum := by
  have hfil : ∀ acts : List (Action KW F G RHO PSI MHASH MENC SIG d),
      (((acts.filter fun a => a.w.note_old.v ≠ 0).map fun a =>
          (a.w.note_old.v : ℤ))).sum
        = (acts.map fun a => (a.w.note_old.v : ℤ)).sum := by
    intro acts
    induction acts with
    | nil => rfl
    | cons a t ih =>
        rw [List.filter_cons]
        by_cases h : a.w.note_old.v ≠ 0
        · rw [if_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
            List.map_cons, List.sum_cons]
        · rw [if_neg (by simpa using h), ih, List.map_cons, List.sum_cons]
          have h0 : a.w.note_old.v = 0 := by omega
          rw [h0]
          simp
  rw [nonZeroSpends]
  rw [show ((↑((spendActions ledger i).map spendRecord) :
        Multiset (PositionedOpening F G RHO PSI)).map
          fun p => (p.opening.note.v : ℤ)).sum
      = (((spendActions ledger i).map spendRecord).map
          fun p => (p.opening.note.v : ℤ)).sum by simp]
  rw [List.map_map]
  rw [show ((fun p : PositionedOpening F G RHO PSI => (p.opening.note.v : ℤ))
        ∘ spendRecord)
      = fun a : Action KW F G RHO PSI MHASH MENC SIG d => (a.w.note_old.v : ℤ) from rfl]
  rw [spendActions, sum_flatMap]
  exact congrArg List.sum (List.map_congr_left fun tx _ => hfil tx.actions)

/-- The shielded pool balance is the negated sum of the transactions' net values. -/
theorem shieldedPoolBalance_eq_neg
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    shieldedPoolBalance ledger i = -((ledger.take i).map txNetValue).sum := by
  rw [shieldedPoolBalance, positionedOutputs_value_sum, nonZeroSpends_value_sum]
  rw [show ((ledger.take i).map txNetValue).sum
      = ((ledger.take i).map fun tx =>
            (tx.actions.map fun a => (a.w.note_old.v : ℤ)).sum).sum
        - ((ledger.take i).map fun tx =>
            (tx.actions.map fun a => (a.w.note_new.v : ℤ)).sum).sum by
    rw [← sum_map_sub]
    exact congrArg List.sum (List.map_congr_left fun tx _ => by
      rw [txNetValue, sum_map_sub])]
  ring

section Conservation

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- Run the transaction-balance premiss over a list, stopping at the first break. -/
def allConservedOrBreak {VB : Type*}
    (perTx : (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ledger →
      (txNetValue tx = tx.vBalance) ⊕' VB) :
    (L : List (Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth)) → (∀ tx ∈ L, tx ∈ ledger) →
    ((∀ tx ∈ L, txNetValue tx = tx.vBalance) ⊕' VB)
  | [], _ => .inl (by simp)
  | tx :: t, hL =>
    match perTx tx (hL tx (by simp)) with
    | .inr b => .inr b
    | .inl heq =>
      match allConservedOrBreak perTx t (fun x hx => hL x (by simp [hx])) with
      | .inr b => .inr b
      | .inl hall => .inl (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          exacts [heq, hall x hx'])

/-- **Balance conservation.** Up to the transaction-balance premiss's break, the
shielded pool plus the transparent pool is exactly the minted issuance. -/
def balanceConservationOrBreak {VB : Type*}
    (perTx : (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ledger →
      (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    (shieldedPoolBalance ledger i + transparentPoolBalance issuance ledger i
        = issuanceTotal issuance ledger i) ⊕' VB :=
  match allConservedOrBreak perTx (ledger.take i)
      (fun _ h => (List.take_sublist i ledger).subset h) with
  | .inr b => .inr b
  | .inl hall => .inl (by
      have hsum : ((ledger.take i).map txNetValue).sum
          = ((ledger.take i).map fun tx => tx.vBalance).sum :=
        congrArg List.sum (List.map_congr_left fun tx htx => hall tx htx)
      rw [shieldedPoolBalance_eq_neg, transparentPoolBalance_eq, hsum]
      ring)

/-- **Shielded balance cap.** Given that the transparent pool never goes negative,
the shielded pool holds at most what issuance has minted — up to the transaction-balance
premiss's break. -/
def shieldedBalanceCapOrBreak {VB : Type*}
    (hval : ValidLedger P kv issuance maxActions ledger)
    (perTx : (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ledger →
      (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    (shieldedPoolBalance ledger i ≤ issuanceTotal issuance ledger i) ⊕' VB :=
  match balanceConservationOrBreak (issuance := issuance) perTx i with
  | .inr b => .inr b
  | .inl h => .inl (by
      have hnn := hval.transparent_nonneg i
      omega)

omit [Field F] [AddCommGroup G] [Module F G] in
/-- A sub-multiset of positioned openings sums to no more value: the opening values are
non-negative. -/
theorem sum_val_le_of_le
    {s t : Multiset (PositionedOpening F G RHO PSI)} (h : s ≤ t) :
    (s.map fun p => (p.opening.note.v : ℤ)).sum
      ≤ (t.map fun p => (p.opening.note.v : ℤ)).sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [Multiset.map_add, Multiset.sum_add]
  have hu : 0 ≤ (u.map fun p => (p.opening.note.v : ℤ)).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hx
      exact Int.natCast_nonneg _
  linarith

omit [Field F] [AddCommGroup G] [Module F G] in
/-- The positioned outputs' total value is monotone in the prefix length: outputs only
accumulate, and their values are non-negative. -/
theorem positionedOutputs_value_sum_mono
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) {i j : ℕ} (hij : i ≤ j) :
    ((positionedOutputs ledger i).map fun p => (p.opening.note.v : ℤ)).sum
      ≤ ((positionedOutputs ledger j).map fun p => (p.opening.note.v : ℤ)).sum := by
  rw [positionedOutputs_value_sum, positionedOutputs_value_sum]
  obtain ⟨r, hr⟩ := take_prefix_take (l := ledger) hij
  rw [← hr, List.map_append, List.sum_append]
  have : 0 ≤ (r.map fun tx =>
      (tx.actions.map fun a => (a.w.note_new.v : ℤ)).sum).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨tx, -, rfl⟩ := List.mem_map.mp hx
      exact List.sum_nonneg fun y hy => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
        exact Int.natCast_nonneg _
  linarith

omit [Field F] [AddCommGroup G] [Module F G] in
/-- **Shielded pool balance lower bound.** When the nonzero spends of the first `i + 1`
transactions are covered by the positioned outputs of the first `i` — the Balance-subset
conclusion — the shielded pool holds non-negative value: no value is spent that was not
created. -/
theorem shieldedPoolBalance_nonneg
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ)
    (hsub : nonZeroSpends ledger (i + 1) ≤ (↑(positionedOutputs ledger i) : Multiset _)) :
    0 ≤ shieldedPoolBalance ledger (i + 1) := by
  rw [shieldedPoolBalance, sub_nonneg]
  have h1 : ((nonZeroSpends ledger (i + 1)).map fun p => (p.opening.note.v : ℤ)).sum
      ≤ ((positionedOutputs ledger i).map fun p => (p.opening.note.v : ℤ)).sum := by
    refine le_trans (sum_val_le_of_le hsub) ?_
    rw [Multiset.map_coe, Multiset.sum_coe]
  exact le_trans h1 (positionedOutputs_value_sum_mono ledger (Nat.le_succ i))

/-- **Balance integrity.** In a valid ledger, either the value after the first
`i + 1` transactions is accounted for exactly —the shielded and transparent pools
are both non-negative and sum to the minted issuance— or the ledger's own data
computes a break: a Balance-subset break (a Merkle, note-commitment, or key-binding
break) or the transaction-balance premiss's break.

In the absence of a break, this matches (modulo the simplification of only one
shielded pool made in the modelling) the rules in ZIP 209. More specifically
it ensures that those rules only reinforce properties that are in any case
cryptographically guaranteed. That is, there will be no "turnstile violation".

Facts from three places come together to ensure balance integrity:

* The shielded pool is non-negative by `shieldedPoolBalance_nonneg`, from
  Balance-subset: no value is spent that was not created.
* The transparent pool is non-negative by validity (`transparent_nonneg`).
* The two pools sum to issuance by balance conservation
  (`balanceConservationOrBreak`, from the binding signature: value balances within
  a transaction). -/
def balanceIntegrityOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
    [NoZeroSMulDivisors F G] {VB : Type*}
    (hval : ValidLedger P kv issuance maxActions ledger)
    (perTx : (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ledger →
      (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    (0 ≤ shieldedPoolBalance ledger (i + 1)
        ∧ 0 ≤ transparentPoolBalance issuance ledger (i + 1)
        ∧ shieldedPoolBalance ledger (i + 1) + transparentPoolBalance issuance ledger (i + 1)
            = issuanceTotal issuance ledger (i + 1))
      ⊕' (BalanceBreak P kv ⊕' VB) :=
  match balanceSubsetOrBreak hval i,
      balanceConservationOrBreak (issuance := issuance) perTx (i + 1) with
  | .inr b, _ => .inr (.inl b)
  | _, .inr vb => .inr (.inr vb)
  | .inl hsub, .inl hcons =>
      .inl ⟨shieldedPoolBalance_nonneg ledger i hsub, hval.transparent_nonneg (i + 1), hcons⟩

end Conservation

end Zcash.Security.Ledger.Model
