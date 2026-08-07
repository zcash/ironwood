import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Merkle

/-!
# The abstract Action statement and its pinning lemmas

This module transcribes the games-relevant conjuncts of an Orchard-shaped Action statement
(Zcash protocol specification §4.17.4) over abstract primitives, as the interface consumed
by the ledger-model security games (Balance, Spendability, Spend Authority). Two
instantiations are intended to satisfy it. The statements themselves are not formalized
yet, though the key-binding layer already reduces breaks of the `Commit^ivk` opening to
Pedersen-scalar ±-collisions — essentially note-commitment binding:

* the deployed (pre-quantum) Orchard Action statement, where the key-binding condition is
  the bare `Commit^ivk` opening, and note-commitment breaks reduce on paper to
  Sinsemilla/DLR relations (spec Theorems 5.4.3 and 5.4.4); and
* the ZIP 2005 Recovery Statement, which adds derivation constraints (`KB_deriv`, the
  `H^rcm`/`H^ψ` checks) so that the same breaks reduce to random-oracle collisions
  (ZIP 2005's key-binding theorem).

The key material is decoupled behind `KeyBindingInterface`: the games see only the
projections (`ivk`, `nk`, `akP`), the key-binding condition `KB` enforced by the statement,
and a `Break` predicate with two guarantees: `KB`-witnesses sharing an `ivk` are a break
if they disagree on `nk`, or if their `akP`s are not equal up to sign (`=±`, the notation
scoped in `Zcash.Security.RandomOracle`). The concrete witness structure, the factoring
`KB = KBOpening ∧ KBDerivation`, and the reduction from `Break` to random-oracle
collisions live in the key-binding layer (`keep/keybinding-design.md`).

The lemmas here are the deterministic pinning steps of the Balance argument:

* `ivk_pinned` — an address `(g_d, pk_d)` determines `ivk` (ZIP 2005's `ivk`-pinning lemma;
  needs only `g_d ≠ 0` and torsion-freeness of the group, no cryptography);
* `nk_eq_or_break` — hence `nk` is determined up to an exhibited key-binding break;
* `noteCommitBreakOfNe` — an `extract`-equal commitment pins the note tuple `(rcm, note)`,
  else this reduction computes a note-commitment break (data, per breaks-as-computed-data);
* `nf_old_eq_or_break` — nullifier determinism: spends of the same note tuple reveal the
  same nullifier, up to an exhibited key-binding break.
-/

namespace Zcash.Security.Ledger

open scoped Zcash.Security.RandomOracle

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

/-- An Orchard-shaped note. Point encodings and type conversions are abstracted away:
`gd` and `pkd` are group elements, `ρ` and `ψ` base-field values, `v` a natural number
(range-bounded by the statement). -/
structure Note (G RHO PSI : Type*) where
  gd : G
  pkd : G
  v : ℕ
  ρ : RHO
  ψ : PSI
  deriving DecidableEq

/-- The public inputs of an Action that the games consume: the anchor, the revealed
nullifier, the randomized verification key, the net value commitment, and the new note
commitment's extracted coordinate. The deployed circuit's instance additionally copies
the bundle-level flags (`enable_spend`, `enable_output`, `disable_cross_address`) into
every action; the games-facing instance deliberately omits them — the bridge reports
their exact circuit semantics as side facts (`Bridge.EnableFlagsSatisfied`,
`Bridge.CrossAddressSatisfied`) pending the games' actual interface (see the TODO on
`ActionSatisfied`). -/
structure ActionInstance (G MHASH RHO : Type*) where
  rt : MHASH
  /-- `⦂ RHO`: nullifiers share ρ's type, forced by ρ-uniqueness (`ρ_new = nf_old`). -/
  nf_old : RHO
  rk : G
  cv_net : G
  cmx_new : MHASH

/-- The abstract primitives of an Orchard-shaped shielded protocol. No algebraic structure
is required of the fields themselves; the group algebra enters only through the statement
and lemmas. `emb` is the embedding of base-field values used as scalars
(`[0, q) ⊆ [0, r)` concretely). `MSG` and `SIG` are the sighash and signature types of the
spend-authorization scheme. -/
structure Primitives (F G IVK NK RHO PSI MHASH MENC MSG SIG : Type*) where
  valueBound : ℕ
  emb : IVK → F
  emb_injective : Function.Injective emb
  extract : G → MHASH
  noteCommit : F → Note G RHO PSI → Option G
  /-- Nullifiers share ρ's type (`RHO`), forced by ρ-uniqueness (`ρ_new = nf_old`). -/
  deriveNullifier : NK → RHO → PSI → G → RHO
  /-- The raw-encoding partial Merkle interface (`Zcash.Security.Ledger.Merkle`): tree
  nodes are `MHASH` values, `MENC` is the raw child encoding consumed by the
  height-personalized partial compression. Non-canonical encodings are accepted — a
  conscious trade-off from Sapling onward: the circuit does not pay for a canonicity
  check, so collisions are counted over the encoding domain, per height. -/
  merkle : MerklePrimitives MHASH MENC
  /-- The padding value for tree positions beyond the appended leaves
  (`Uncommitted^Orchard` concretely). -/
  uncommitted : MHASH
  /-- No extracted note commitment collides with the padding value (spec Thm 5.4.6
  concretely). -/
  uncommitted_ne : ∀ g, extract g ≠ uncommitted
  randomizePublic : F → G → G
  valueCommit : ℤ → F → G
  /-- Verification of a spend-authorization signature under the randomized key `rk`, over
  a transaction sighash. -/
  spendAuthVerify : G → MSG → SIG → Prop
  /-- Verification of a transaction's binding signature under the binding verification
  key, over a transaction sighash. -/
  bindingVerify : G → MSG → SIG → Prop

/-- The tree depth, read off the Merkle interface. -/
abbrev Primitives.depth (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) : ℕ :=
  P.merkle.depth

/-- The games-facing view of a key-binding witness type `KW`: projections, the key-binding
condition `KB` enforced by the statement, and a `Break` predicate. `break_of_nk_ne`
(consumed by Balance) and `break_of_akP_ne` (consumed by Spend Authority) are the
guarantees the games use; the key-binding layer instantiates `Break` and discharges
both, reducing breaks onward to random-oracle collisions. `Break` is deliberately an
opaque `Prop`: the games exhibit the witness pair as data and certify the break
propositionally, which is exactly the event the probabilistic bound
(`toInterface_break_measure_le`) covers; data-level onward reductions
(`CollisionUpToSign.ofBreak`) live below the interface. -/
structure KeyBindingInterface (KW G IVK NK : Type*) [Neg G] where
  ivk : KW → IVK
  nk : KW → NK
  akP : KW → G
  KB : KW → Prop
  Break : KW → KW → Prop
  break_of_nk_ne : ∀ {w₁ w₂ : KW}, KB w₁ → KB w₂ →
    ivk w₁ = ivk w₂ → nk w₁ ≠ nk w₂ → Break w₁ w₂
  /-- Two `KB`-witnesses sharing an `ivk` whose `akP`s are not equal up to sign are a
  break. The key-binding layer discharges this from the ±-property of the `ak`
  extraction: `ak` is consumed as a single extracted coordinate, pinned only up to
  y-sign. -/
  break_of_akP_ne : ∀ {w₁ w₂ : KW}, KB w₁ → KB w₂ →
    ivk w₁ = ivk w₂ → ¬ akP w₁ =± akP w₂ → Break w₁ w₂

/-- The auxiliary inputs of an Action. `cm_old`/`cm_new` are carried explicitly so that the
statement's commitment checks pin them; `kw` is the key-binding witness. -/
structure ActionWitness (KW F G RHO PSI MHASH MENC : Type*) (d : ℕ) where
  /-- Both raw child encodings at every height, in leaf-to-root order. -/
  path : Fin d → MENC × MENC
  /-- The child encoding selected by the path (`false` = left, `true` = right). -/
  side : Fin d → Bool
  note_old : Note G RHO PSI
  note_new : Note G RHO PSI
  cm_old : G
  cm_new : G
  kw : KW
  α : F
  rcv : F
  rcm_old : F
  rcm_new : F

/-- The games-relevant conjuncts of the Action statement, for instance `inst` and witness
`w`. Both the deployed Orchard Action statement and the ZIP 2005 Recovery Statement
satisfy this interface (the latter enforces strictly more).

This is the security-game statement — the abstract ledger meaning of a successful
action — and it is deliberately separate from the circuit-facing `ActionSpec`:
`Bridge.actionSpec_to_ledger` verifies that every `ActionSpec` case becomes either this
statement or an exhibited `Bridge.ActionBreak`. The interface itself stays
`Prop`-only; the breaks-as-computed-data pattern applies at the bridge
(`Bridge.classifyAction`, reduced onward to the games-facing discrete-log-relation
object by `Bridge.relationOfBreakData`), not here.

TODO: Verify the exact Action interface the Balance and Spendability games consume.
The NU6.3 flag conditions belong in the game instance rather than a circuit-facing
wrapper — the adversary must be allowed to submit transactions both before and after
NU6.3 — so `ActionInstance` grows the flag fields when those games land. -/
structure ActionSatisfied (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK) (inst : ActionInstance G MHASH RHO)
    (w : ActionWitness KW F G RHO PSI MHASH MENC P.depth) : Prop where
  /-- Spend-side commitment integrity: `cm_old` opens `note_old` with `rcm_old`. -/
  commit_old : P.noteCommit w.rcm_old w.note_old = some w.cm_old
  /-- Merkle path validity for nonzero-valued spends. -/
  merkle_path : w.note_old.v ≠ 0 →
    Merkle.Path P.merkle (P.extract w.cm_old) inst.rt w.path w.side
  /-- Nullifier integrity. -/
  nf_old_eq : inst.nf_old =
    P.deriveNullifier (kv.nk w.kw) w.note_old.ρ w.note_old.ψ w.cm_old
  /-- The key-binding condition on the key witness. -/
  key_binding : kv.KB w.kw
  /-- Diversified address integrity: `pk_d = [ivk] g_d`. -/
  pkd_eq : w.note_old.pkd = P.emb (kv.ivk w.kw) • w.note_old.gd
  /-- `g_d` is not the zero element. -/
  gd_ne : w.note_old.gd ≠ 0
  /-- Spend authority: `rk` is the `α`-randomization of the verification key. -/
  rk_eq : inst.rk = P.randomizePublic w.α (kv.akP w.kw)
  /-- Output-side commitment integrity: `cm_new` opens `note_new` with `rcm_new`. -/
  commit_new : P.noteCommit w.rcm_new w.note_new = some w.cm_new
  /-- The instance exposes the extracted coordinate of `cm_new`. -/
  cmx_new_eq : inst.cmx_new = P.extract w.cm_new
  /-- ρ-uniqueness: the output note's `ρ` is the spend's nullifier. -/
  ρ_new_eq : w.note_new.ρ = inst.nf_old
  /-- Spent-note value range. -/
  v_old_lt : w.note_old.v < P.valueBound
  /-- Output-note value range. -/
  v_new_lt : w.note_new.v < P.valueBound
  /-- Value commitment integrity over the net value. -/
  cv_net_eq : inst.cv_net = P.valueCommit ((w.note_old.v : ℤ) - (w.note_new.v : ℤ)) w.rcv

/-- A note-commitment break, as data (per the breaks-as-computed-data
convention in `Zcash.Security.RandomOracle`): two distinct `(rcm, note)` tuples whose commitments have
equal extracted coordinates. Computed by the games' reductions; nothing in this
development reduces it further. The intended onward reductions are a Sinsemilla/DLR
relation pre-quantum (spec Theorems 5.4.3 and 5.4.4), and an `H^rcm` ±-collision for the
Recovery Statement (via the Pedersen lift and the `extract` ±-property).

The value bounds travel with the break object: `Note.v` is an unbounded `ℕ` while the
concrete commitment consumes it through a 64-bit encoding, so without them the structure
would be inhabitable by value-overflow aliasing (`v` versus `v + 2^64`) with no
cryptographic content, and the onward reductions above would be false as stated.  The
producers mint breaks from `ActionSatisfied` pairs, whose `v_old_lt`/`v_new_lt` conjuncts
supply the bounds directly. -/
structure NoteCommitBreak (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) where
  rcm₁ : F
  n₁ : Note G RHO PSI
  rcm₂ : F
  n₂ : Note G RHO PSI
  cm₁ : G
  cm₂ : G
  ne : (rcm₁, n₁) ≠ (rcm₂, n₂)
  open₁ : P.noteCommit rcm₁ n₁ = some cm₁
  open₂ : P.noteCommit rcm₂ n₂ = some cm₂
  extract_eq : P.extract cm₁ = P.extract cm₂
  v₁_lt : n₁.v < P.valueBound
  v₂_lt : n₂.v < P.valueBound

section Pinning

variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {inst₁ inst₂ : ActionInstance G MHASH RHO}
variable {w₁ w₂ : ActionWitness KW F G RHO PSI MHASH MENC P.depth}

/-- **`ivk`-pinning** (ZIP 2005 `lemma-ivk-pinning`): the address `(g_d, pk_d)` of the
spent note determines `ivk`. Pure module algebra: needs only `g_d ≠ 0`, injectivity of the
scalar embedding, and torsion-freeness of the group (satisfied by a prime-order group). -/
theorem ivk_pinned [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hgd : w₁.note_old.gd = w₂.note_old.gd) (hpkd : w₁.note_old.pkd = w₂.note_old.pkd) :
    kv.ivk w₁.kw = kv.ivk w₂.kw := by
  have hs : P.emb (kv.ivk w₁.kw) • w₂.note_old.gd
      = P.emb (kv.ivk w₂.kw) • w₂.note_old.gd := by
    rw [← hgd, ← h₁.pkd_eq, hpkd, h₂.pkd_eq, hgd]
  have hz : (P.emb (kv.ivk w₁.kw) - P.emb (kv.ivk w₂.kw)) • w₂.note_old.gd = 0 := by
    rw [sub_smul, hs, sub_self]
  rcases smul_eq_zero.mp hz with hc | hgd0
  · exact P.emb_injective (sub_eq_zero.mp hc)
  · exact absurd hgd0 h₂.gd_ne

/-- `nk`-pinning up to a break: two satisfied spends of notes with the same address agree
on `nk`, or their key witnesses exhibit a key-binding break. -/
theorem nk_eq_or_break [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hgd : w₁.note_old.gd = w₂.note_old.gd) (hpkd : w₁.note_old.pkd = w₂.note_old.pkd) :
    kv.nk w₁.kw = kv.nk w₂.kw ∨ kv.Break w₁.kw w₂.kw := by
  by_cases hnk : kv.nk w₁.kw = kv.nk w₂.kw
  · exact Or.inl hnk
  · exact Or.inr (kv.break_of_nk_ne h₁.key_binding h₂.key_binding
      (ivk_pinned h₁ h₂ hgd hpkd) hnk)

/-- **Note-tuple pinning, as an explicit reduction**: two satisfied spends with
`extract`-equal commitments but distinct note tuples `(rcm_old, note_old)` yield a
note-commitment break. This is the step that converts Merkle-pinned leaves into pinned
notes in the Balance argument; consumers with `DecidableEq` on the tuple case-split and
call this in the ≠ branch. -/
def noteCommitBreakOfNe
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hx : P.extract w₁.cm_old = P.extract w₂.cm_old)
    (hne : (w₁.rcm_old, w₁.note_old) ≠ (w₂.rcm_old, w₂.note_old)) :
    NoteCommitBreak P :=
  ⟨_, _, _, _, _, _, hne, h₁.commit_old, h₂.commit_old, hx, h₁.v_old_lt, h₂.v_old_lt⟩

/-- **Nullifier determinism up to a break** — **nf-pinning** (ZIP 2005 `lemma-nf-pinning`,
consumed by the Spendability argument), as computed data per the breaks-as-computed-data
convention: two satisfied spends of the same note tuple either reveal the same nullifier or
their key witnesses exhibit a key-binding break, with the branch decided on the
nullifier-key comparison. Together with `tuple_eq_or_noteCommitBreak` this is what turns a
repeated spend of a positioned note into a repeated nullifier in the Balance argument. The
nullifier here is a function by definition; the circuit-soundness layer must separately
ensure the deployed circuit computes `DeriveNullifier` deterministically as a function of
`(nk, ρ, ψ, cm)`. -/
def nfOldEqOrBreak [DecidableEq NK] [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hrcm : w₁.rcm_old = w₂.rcm_old) (hnote : w₁.note_old = w₂.note_old) :
    (inst₁.nf_old = inst₂.nf_old) ⊕' kv.Break w₁.kw w₂.kw :=
  if hnk : kv.nk w₁.kw = kv.nk w₂.kw then
    .inl (by
      have hcm : w₁.cm_old = w₂.cm_old := by
        have h := h₁.commit_old
        rw [hrcm, hnote, h₂.commit_old] at h
        exact (Option.some.inj h).symm
      rw [h₁.nf_old_eq, h₂.nf_old_eq, hnk, hcm, hnote])
  else
    .inr (kv.break_of_nk_ne h₁.key_binding h₂.key_binding
      (ivk_pinned h₁ h₂ (congrArg Note.gd hnote) (congrArg Note.pkd hnote)) hnk)

end Pinning

end Zcash.Security.Ledger
