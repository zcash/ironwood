import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Statement
import Zcash.Security.Ledger.Pool
import Zcash.Security.Ledger.SinsemillaDLR

/-!
# The Orchard-protocol note-commitment break computes a discrete-log relation

The pre-quantum discharge of the note-commitment arm: a `NoteCommitBreak` at the
Orchard-protocol primitives — two openings with distinct `(rcm, note)` pairs whose
commitments share an extracted coordinate — computes a nontrivial relation among the
Sinsemilla table, the `NoteCommit` domain point, and the randomness base. The
reduction unpacks the two openings into their defined Sinsemilla chains and blinding
scalars and applies the chain-collision reducer `relationOfChainPmEq`.

The reduction is hypothesis-free. The chunk-coefficient injectivity is `preCoeffs_inj`
and the 109-chunk message encoding is injective by `noteCommitChunks_inj`. Recovering
the note from its scalars additionally uses `eq_of_toPoint_x_eq_of_y_parity_eq`,
because the message carries each point as its `x`-coordinate and `y`-parity bit.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool

/-- A scalar acts on the group as its canonical natural representative. -/
theorem smul_eq_val_nsmul (r : Fq) (P : PallasGroup) : r • P = r.val • P := by
  rw [← Nat.cast_smul_eq_nsmul Fq, ZMod.natCast_zmod_val]

/-- Every note value below the Orchard-protocol bound is below the base-field order. -/
theorem valueBound_lt_card {v : ℕ} (hv : v < 2 ^ 64) :
    v < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD :=
  lt_trans hv (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

/-- A defined `noteCommit` hit names a defined `noteHash` chain. -/
theorem noteCommit_hash_isSome {rcm : Fq} {n : Note PallasGroup Fp Fp}
    {cm : PallasGroup} (h : noteCommit rcm n = some cm) : (noteHash n).isSome := by
  unfold noteCommit at h
  rcases Option.bind_eq_some_iff.mp h with ⟨bp, hbp, -⟩
  exact hbp ▸ rfl

/-- The chain a defined `noteCommit` hit names is valid. -/
theorem noteCommit_get_valid {rcm : Fq} {n : Note PallasGroup Fp Fp}
    {cm : PallasGroup} (h : noteCommit rcm n = some cm) :
    ((noteHash n).get (noteCommit_hash_isSome h)).Valid :=
  hashToPoint_valid (Or.inl noteQ_onCurve) (fun _ hm => chunksOf_mem_lt hm)
    (Option.some_get (noteCommit_hash_isSome h)).symm

/-- A defined `noteCommit` hit decomposes as its chain plus the blinding term. -/
theorem noteCommit_get_eq {rcm : Fq} {n : Note PallasGroup Fp Fp}
    {cm : PallasGroup} (h : noteCommit rcm n = some cm) :
    cm = sinsemillaCommitBlind (PallasGroup.ofPoint _ (noteCommit_get_valid h))
      rcm noteCommitRpt := by
  show cm = PallasGroup.ofPoint _ (noteCommit_get_valid h) + rcm • noteCommitRpt
  have hval : ((noteHash n).get (noteCommit_hash_isSome h)
      + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point).Valid :=
    Point.valid_add (noteCommit_get_valid h)
      (Point.valid_nsmul (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve) rcm.val)
  have hsome := noteCommit_eq_some_of_hashToPoint
    (Option.some_get (noteCommit_hash_isSome h)).symm rfl hval
  rw [smul_eq_val_nsmul, noteCommitRpt, ← PallasGroup.ofPoint_nsmul,
    ← PallasGroup.ofPoint_add (noteCommit_get_valid h)
      (Point.valid_nsmul (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve) rcm.val)]
  exact Option.some_inj.mp (h.symm.trans hsome)

/-- **The Orchard-protocol note-commitment break computes a discrete-log relation.** Two
openings with distinct `(rcm, note)` pairs whose commitments share an extracted
coordinate: the reduction unpacks them into their defined Sinsemilla chains and blinding
scalars and applies the chain-collision reducer at the `NoteCommit` domain point and
randomness base. -/
def relationOfNoteCommitBreak {MSG SIG : Type*}
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (brk : NoteCommitBreak (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify)) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  toOrchardPoints (V := ![noteQpt, noteCommitRpt])
    (g := ![.idxNoteQ, .idxNoteCommitR])
    (gr := fun s => match s with
      | .idxNoteQ => some 0
      | .idxNoteCommitR => some 1
      | _ => none)
    (hg := by intro x y; fin_cases x <;> cases y <;> decide)
    (hpt := fun i => by fin_cases i <;> rfl) <|
  relationOfChainPmEq (Q := noteQ) (Or.inl noteQ_onCurve) (W := noteCommitRpt)
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp [Pool.noteScalars])
    (Option.some_get (noteCommit_hash_isSome brk.open₁)).symm
    (noteCommit_get_valid brk.open₁)
    (Option.some_get (noteCommit_hash_isSome brk.open₂)).symm
    (noteCommit_get_valid brk.open₂)
    (by
      have hx : extract brk.cm₁ = extract brk.cm₂ := brk.extract_eq
      rw [noteCommit_get_eq brk.open₁, noteCommit_get_eq brk.open₂] at hx
      exact (PallasGroup.toPoint_x_eq_iff _ _).mp hx)
    (by simp [Pool.noteScalars])
    (by
      rintro ⟨hl, hr⟩
      simp only [Pool.noteScalars, NoteCommit.noteScalars] at hl
      obtain ⟨hgx, hgy, hpx, hpy, hv, hrho, hpsi⟩ := noteCommitChunks_inj
        (fp_val_lt _) (Nat.mod_lt _ (by norm_num)) (fp_val_lt _)
        (Nat.mod_lt _ (by norm_num))
        (by
          rw [ZMod.val_natCast_of_lt (valueBound_lt_card brk.v₁_lt)]
          exact brk.v₁_lt)
        (fp_val_lt _) (fp_val_lt _)
        (fp_val_lt _) (Nat.mod_lt _ (by norm_num)) (fp_val_lt _)
        (Nat.mod_lt _ (by norm_num))
        (by
          rw [ZMod.val_natCast_of_lt (valueBound_lt_card brk.v₂_lt)]
          exact brk.v₂_lt)
        (fp_val_lt _) (fp_val_lt _) hl
      have hgd : brk.n₁.gd = brk.n₂.gd :=
        PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq (ZMod.val_injective _ hgx) hgy
      have hpkd : brk.n₁.pkd = brk.n₂.pkd :=
        PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq (ZMod.val_injective _ hpx) hpy
      have hvv : brk.n₁.v = brk.n₂.v := by
        rwa [ZMod.val_natCast_of_lt (valueBound_lt_card brk.v₁_lt),
          ZMod.val_natCast_of_lt (valueBound_lt_card brk.v₂_lt)] at hv
      have hrho' : brk.n₁.ρ = brk.n₂.ρ := ZMod.val_injective _ hrho
      have hpsi' : brk.n₁.ψ = brk.n₂.ψ := ZMod.val_injective _ hpsi
      refine brk.ne ?_
      have hn : brk.n₁ = brk.n₂ := by
        rw [show brk.n₁ = ⟨brk.n₁.gd, brk.n₁.pkd, brk.n₁.v, brk.n₁.ρ, brk.n₁.ψ⟩ from rfl,
          hgd, hpkd, hvv, hrho', hpsi']
      rw [hn, hr])

end Zcash.Security.Ledger.Bridge
