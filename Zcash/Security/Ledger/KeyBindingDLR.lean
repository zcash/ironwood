import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Pool
import Zcash.Security.Ledger.SinsemillaDLR

/-!
# The Orchard-protocol key-binding break computes a discrete-log relation

The pre-quantum discharge of the key-binding arm's ε: a
`KeyBinding.Pool.CommitIvkCollision` — two valid `Commit^ivk` openings of the same `ivk`
disagreeing on their opening projection — computes a nontrivial discrete-log relation
among the Sinsemilla table generators, the `CommitIvk` domain point, and the `CommitIvk`
randomness base. This folds ε_kb into the same DL terminal as the Merkle and
note-commitment arms, with no random-oracle model and no probability accounting: the
reduction is deterministic.

The shared machinery is `Bridge.relationOfChainPmEq` (`SinsemillaDLR`); this module
instantiates it at the `CommitIvk` domain point and randomness base, unpacking the
break's two openings into their defined Sinsemilla chains and turning the equal-`ivk`
extraction into the up-to-sign equation via the `Extract_ℙ` ±-fibre property.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool

/-- The `CommitIvk` domain point `Q("z.cash:Orchard-CommitIvk-M")`, as a group element. -/
def ivkQpt : PallasGroup := PallasGroup.ofPoint ivkQ (Or.inl ivkQ_onCurve)

/-- The `CommitIvk` randomness base, as a group element — the `commitIvkR` argument of
the Orchard-protocol `keyBinding` interface. -/
def commitIvkRpt : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
    (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve)

/-- A defined `commitIvkHash` hit names a defined, valid `hashToPoint` chain. -/
theorem commitIvkHash_isSome {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    (hashToPoint orchardGenerators.S ivkQ (commitIvkChunks a.val n.val)).isSome := by
  unfold commitIvkHash at h
  rcases Option.bind_eq_some_iff.mp h with ⟨p, hp, -⟩
  exact hp ▸ rfl

/-- The chain a defined `commitIvkHash` hit names is valid, and the hit is its image. -/
theorem commitIvkHash_get_spec {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    ∃ hv : ((hashToPoint orchardGenerators.S ivkQ
        (commitIvkChunks a.val n.val)).get (commitIvkHash_isSome h)).Valid,
      g = PallasGroup.ofPoint _ hv := by
  unfold commitIvkHash at h
  rcases Option.bind_eq_some_iff.mp h with ⟨p, hp, hop⟩
  have hget : (hashToPoint orchardGenerators.S ivkQ
      (commitIvkChunks a.val n.val)).get (commitIvkHash_isSome h) = p := by
    simp [hp]
  rw [hget]
  unfold PallasGroup.ofPoint? at hop
  split at hop
  · rename_i hv
    exact ⟨hv, (Option.some_inj.mp hop).symm⟩
  · exact absurd hop (by simp)

/-- **The Orchard-protocol key-binding break computes a discrete-log relation.** Two
valid `Commit^ivk` openings of the same `ivk` disagreeing on their opening projection:
the reduction unpacks them into their defined Sinsemilla chains and blinding scalars
and applies the chain-collision reducer at the `CommitIvk` domain point and randomness
base. The reduction is hypothesis-free: the chunk-coefficient injectivity is
`preCoeffs_inj` (spec Theorem 5.4.3's binary-expansion core, proven) and the
chunk-encoding injectivity is `commitIvkChunks_inj`. -/
def relationOfKeyBindingBreak
    {w₁ w₂ : KeyBinding.Pool.Witness Fq PallasGroup Fp}
    (b : KeyBinding.Pool.CommitIvkCollision extract commitIvkHash commitIvkRpt w₁ w₂)
 :
    NontrivialRelation (F := Fq) pallasS ivkQpt commitIvkRpt :=
  let hs₁ := commitIvkHash_isSome b.kb₁.hash_eq
  let hs₂ := commitIvkHash_isSome b.kb₂.hash_eq
  relationOfChainPmEq (Q := ivkQ) (Or.inl ivkQ_onCurve) (W := commitIvkRpt)
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp)
    (Option.some_get hs₁).symm (commitIvkHash_get_spec b.kb₁.hash_eq).choose
    (Option.some_get hs₂).symm (commitIvkHash_get_spec b.kb₂.hash_eq).choose
    (by
      have hx : extract (w₁.hashPoint + w₁.rivk • commitIvkRpt)
          = extract (w₂.hashPoint + w₂.rivk • commitIvkRpt) := by
        rw [← b.kb₁.ivk_eq, ← b.kb₂.ivk_eq]
        exact b.ivk_eq
      have hpm := (PallasGroup.toPoint_x_eq_iff _ _).mp hx
      rwa [(commitIvkHash_get_spec b.kb₁.hash_eq).choose_spec,
        (commitIvkHash_get_spec b.kb₂.hash_eq).choose_spec] at hpm)
    (by simp)
    (by
      rintro ⟨hl, hr⟩
      obtain ⟨hak, hnk⟩ := commitIvkChunks_inj
        (fp_val_lt _) (fp_val_lt _) (fp_val_lt _) (fp_val_lt _) hl
      refine b.projection_ne ?_
      unfold KeyBinding.Pool.Witness.breakProjection
      rw [ZMod.val_injective _ hak, ZMod.val_injective _ hnk, hr])

end Zcash.Security.Ledger.Bridge
