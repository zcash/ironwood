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

/-- The `NoteCommit` domain point `Q("z.cash:Orchard-NoteCommit-M")`, as a group
element. -/
def noteQpt : PallasGroup := PallasGroup.ofPoint noteQ (Or.inl noteQ_onCurve)

/-- The `NoteCommit` randomness base, as a group element. -/
def noteCommitRpt : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.noteCommitR.point
    (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve)

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

/-- The chain a defined `noteCommit` hit names is valid, and the hit decomposes as
the chain plus the blinding term. -/
theorem noteCommit_get_spec {rcm : Fq} {n : Note PallasGroup Fp Fp}
    {cm : PallasGroup} (h : noteCommit rcm n = some cm) :
    ∃ hv : ((noteHash n).get (noteCommit_hash_isSome h)).Valid,
      cm = PallasGroup.ofPoint _ hv + rcm • noteCommitRpt := by
  unfold noteCommit at h
  rcases Option.bind_eq_some_iff.mp h with ⟨bp, hbp, hop⟩
  have hget : (noteHash n).get (noteCommit_hash_isSome h) = bp := by simp [hbp]
  have hbpv : bp.Valid := hashToPoint_valid (Or.inl noteQ_onCurve)
    (fun m hm => chunksOf_mem_lt hm) hbp
  rw [hget]
  refine ⟨hbpv, ?_⟩
  unfold PallasGroup.ofPoint? at hop
  split at hop
  · rw [← Option.some_inj.mp hop]
    rw [smul_eq_val_nsmul, noteCommitRpt, ← PallasGroup.ofPoint_nsmul,
      ← PallasGroup.ofPoint_add hbpv
        (Point.valid_nsmul (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve) rcm.val)]
  · exact absurd hop (by simp)

/-- **The Orchard-protocol note-commitment break computes a discrete-log relation.** Two
openings with distinct `(rcm, note)` pairs whose commitments share an extracted
coordinate: the reduction unpacks them into their defined Sinsemilla chains and blinding
scalars and applies the chain-collision reducer at the `NoteCommit` domain point and
randomness base. -/
def relationOfNoteCommitBreak {MSG SIG : Type*}
    (verify bverify : PallasGroup → MSG → SIG → Prop)
    (b : NoteCommitBreak (primitives (MSG := MSG) (SIG := SIG) verify bverify)) :
    NontrivialRelation (F := Fq) pallasS noteQpt noteCommitRpt :=
  relationOfChainPmEq (Q := noteQ) (Or.inl noteQ_onCurve) (W := noteCommitRpt)
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp [Pool.noteScalars])
    (Option.some_get (noteCommit_hash_isSome b.open₁)).symm
    (noteCommit_get_spec b.open₁).choose
    (Option.some_get (noteCommit_hash_isSome b.open₂)).symm
    (noteCommit_get_spec b.open₂).choose
    (by
      have hx : extract b.cm₁ = extract b.cm₂ := b.extract_eq
      rw [(noteCommit_get_spec b.open₁).choose_spec,
        (noteCommit_get_spec b.open₂).choose_spec] at hx
      exact (PallasGroup.toPoint_x_eq_iff _ _).mp hx)
    (by simp [Pool.noteScalars])
    (by
      rintro ⟨hl, hr⟩
      simp only [Pool.noteScalars, NoteCommit.noteScalars] at hl
      obtain ⟨hgx, hgy, hpx, hpy, hv, hrho, hpsi⟩ := noteCommitChunks_inj
        (fp_val_lt _) (Nat.mod_lt _ (by norm_num)) (fp_val_lt _)
        (Nat.mod_lt _ (by norm_num))
        (by
          rw [ZMod.val_natCast_of_lt (valueBound_lt_card b.v₁_lt)]
          exact b.v₁_lt)
        (fp_val_lt _) (fp_val_lt _)
        (fp_val_lt _) (Nat.mod_lt _ (by norm_num)) (fp_val_lt _)
        (Nat.mod_lt _ (by norm_num))
        (by
          rw [ZMod.val_natCast_of_lt (valueBound_lt_card b.v₂_lt)]
          exact b.v₂_lt)
        (fp_val_lt _) (fp_val_lt _) hl
      have hgd : b.n₁.gd = b.n₂.gd :=
        PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq (ZMod.val_injective _ hgx) hgy
      have hpkd : b.n₁.pkd = b.n₂.pkd :=
        PallasGroup.eq_of_toPoint_x_eq_of_y_parity_eq (ZMod.val_injective _ hpx) hpy
      have hvv : b.n₁.v = b.n₂.v := by
        rwa [ZMod.val_natCast_of_lt (valueBound_lt_card b.v₁_lt),
          ZMod.val_natCast_of_lt (valueBound_lt_card b.v₂_lt)] at hv
      have hrho' : b.n₁.ρ = b.n₂.ρ := ZMod.val_injective _ hrho
      have hpsi' : b.n₁.ψ = b.n₂.ψ := ZMod.val_injective _ hpsi
      refine b.ne ?_
      have hn : b.n₁ = b.n₂ := by
        rw [show b.n₁ = ⟨b.n₁.gd, b.n₁.pkd, b.n₁.v, b.n₁.ρ, b.n₁.ψ⟩ from rfl,
          hgd, hpkd, hvv, hrho', hpsi']
      rw [hn, hr])

end Zcash.Security.Ledger.Bridge
