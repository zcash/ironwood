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

/-- A defined `commitIvkHash` hit names a defined, valid `hashToPoint` chain. -/
theorem commitIvkHash_isSome {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    (hashToPoint orchardGenerators.S ivkQ (commitIvkChunks a.val n.val)).isSome := by
  unfold commitIvkHash at h
  rcases Option.bind_eq_some_iff.mp h with ⟨p, hp, -⟩
  exact hp ▸ rfl

/-- The chain a defined `commitIvkHash` hit names is valid. -/
theorem commitIvkHash_get_valid {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    ((hashToPoint orchardGenerators.S ivkQ
      (commitIvkChunks a.val n.val)).get (commitIvkHash_isSome h)).Valid :=
  hashToPoint_valid (Or.inl ivkQ_onCurve) (fun _ hm => chunksOf_mem_lt hm)
    (Option.some_get (commitIvkHash_isSome h)).symm

/-- A defined `commitIvkHash` hit is the image of its chain. -/
theorem commitIvkHash_get_eq {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    g = PallasGroup.ofPoint _ (commitIvkHash_get_valid h) :=
  Option.some_inj.mp (h.symm.trans (commitIvkHash_eq_some_of_hashToPoint
    (Option.some_get (commitIvkHash_isSome h)).symm (commitIvkHash_get_valid h)))

/-- **The Orchard-protocol key-binding break computes a discrete-log relation.** Two
valid `Commit^ivk` openings of the same `ivk` disagreeing on their opening projection:
the reduction unpacks them into their defined Sinsemilla chains and blinding scalars
and applies the chain-collision reducer at the `CommitIvk` domain point and randomness
base. The reduction is hypothesis-free: the chunk-coefficient injectivity is
`preCoeffs_inj` (spec Theorem 5.4.3's binary-expansion core, proven) and the
chunk-encoding injectivity is `commitIvkChunks_inj`. -/
def relationOfKeyBindingBreak
    {w₁ w₂ : KeyBinding.Pool.Witness Fq PallasGroup Fp}
    (brk : KeyBinding.Pool.CommitIvkCollision extract commitIvkHash commitIvkRpt w₁ w₂)
 :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  let hs₁ := commitIvkHash_isSome brk.kb₁.hash_eq
  let hs₂ := commitIvkHash_isSome brk.kb₂.hash_eq
  toOrchardPoints (V := ![ivkQpt, commitIvkRpt])
    (g := ![.idxIvkQ, .idxCommitIvkR])
    (gr := fun s => match s with
      | .idxIvkQ => some 0
      | .idxCommitIvkR => some 1
      | _ => none)
    (hg := by intro x y; fin_cases x <;> cases y <;> decide)
    (hpt := fun i => by fin_cases i <;> rfl) <|
  relationOfChainPmEq (Q := ivkQ) (Or.inl ivkQ_onCurve) (W := commitIvkRpt)
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp)
    (Option.some_get hs₁).symm (commitIvkHash_get_valid brk.kb₁.hash_eq)
    (Option.some_get hs₂).symm (commitIvkHash_get_valid brk.kb₂.hash_eq)
    (by
      have hx : extract (w₁.hashPoint + w₁.rivk • commitIvkRpt)
          = extract (w₂.hashPoint + w₂.rivk • commitIvkRpt) := by
        rw [← brk.kb₁.ivk_eq, ← brk.kb₂.ivk_eq]
        exact brk.ivk_eq
      have hpm := (PallasGroup.toPoint_x_eq_iff _ _).mp hx
      rwa [commitIvkHash_get_eq brk.kb₁.hash_eq,
        commitIvkHash_get_eq brk.kb₂.hash_eq] at hpm)
    (by simp)
    (by
      rintro ⟨hl, hr⟩
      obtain ⟨hak, hnk⟩ := commitIvkChunks_inj
        (fp_val_lt _) (fp_val_lt _) (fp_val_lt _) (fp_val_lt _) hl
      refine brk.projection_ne ?_
      unfold KeyBinding.Pool.Witness.breakProjection
      rw [ZMod.val_injective _ hak, ZMod.val_injective _ hnk, hr])

end Zcash.Security.Ledger.Bridge
