import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Common.RandomOracle
import Zcash.Security.Ledger.Pool
import Zcash.Security.Ledger.SinsemillaDLR

/-!
# An Orchard-protocol Merkle collision computes a Sinsemilla discrete-log relation

The pre-quantum discharge of the Merkle arm: a defined collision of the layer-`i`
compression — two distinct child pairs with the same defined output — computes a
nontrivial relation among the Sinsemilla table and the Merkle domain point. The
reduction unpacks both children into their defined Sinsemilla chains and applies the
chain-collision reducer with zero blinding. The resulting relation has no
randomness-base component, so it converts to the one-generator form.

The reduction is hypothesis-free: the chunk-coefficient injectivity is
`preCoeffs_inj`, and the 52-chunk compression encoding is injective by
`merkleChunks_inj`.
-/

set_option exponentiation.threshold 600

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool

/-- The chunk values of a Merkle compression message are table indices. -/
theorem merkleChunks_mem_lt {l lv rv m : ℕ} (hm : m ∈ merkleChunks l lv rv) :
    m < 2 ^ K :=
  chunksOf_mem_lt (merkleChunks_eq_chunksOf l lv rv ▸ hm)

/-- A defined layer compression names a defined Sinsemilla chain. -/
theorem merkleCompress_isSome {i : Fin 32} {ch : Encoding × Encoding} {out : Fp}
    (h : merkleCompress i ch = some out) :
    (hashToPoint orchardGenerators.S merkleQ (merkleChunks i.1 ch.1.1 ch.2.1)).isSome := by
  unfold merkleCompress at h
  rcases Option.map_eq_some_iff.mp h with ⟨p, hp, -⟩
  exact hp ▸ rfl

/-- The defined output is the chain value's `x`-coordinate. -/
theorem merkleCompress_get_x {i : Fin 32} {ch : Encoding × Encoding} {out : Fp}
    (h : merkleCompress i ch = some out) :
    out = ((hashToPoint orchardGenerators.S merkleQ
      (merkleChunks i.1 ch.1.1 ch.2.1)).get (merkleCompress_isSome h)).x := by
  unfold merkleCompress at h
  rcases Option.map_eq_some_iff.mp h with ⟨p, hp, hout⟩
  have hget : (hashToPoint orchardGenerators.S merkleQ
      (merkleChunks i.1 ch.1.1 ch.2.1)).get (merkleCompress_isSome h) = p := by
    simp [hp]
  rw [hget, hout]

/-- The chain a defined layer compression names is valid. -/
theorem merkleCompress_get_valid {i : Fin 32} {ch : Encoding × Encoding} {out : Fp}
    (h : merkleCompress i ch = some out) :
    ((hashToPoint orchardGenerators.S merkleQ
      (merkleChunks i.1 ch.1.1 ch.2.1)).get (merkleCompress_isSome h)).Valid :=
  hashToPoint_valid (Or.inl merkleQ_onCurve) (fun _ hm => merkleChunks_mem_lt hm)
    (Option.some_get (merkleCompress_isSome h)).symm

/-- **An Orchard-protocol Merkle collision computes a Sinsemilla discrete-log
relation.** The collision's two children are unpacked into their defined Sinsemilla
chains, and the chain-collision reducer is applied with zero blinding at the Merkle
domain point.
The relation then converts to the one-generator form, because its randomness-base
coefficient is zero. -/
def relationOfMerkleCollision {i : Fin 32}
    (c : Zcash.Security.RandomOracle.DefinedCollision (merkleCompress i)) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  let rel := relationOfChainPmEq (Q := merkleQ) (Or.inl merkleQ_onCurve)
    (W := (0 : PallasGroup))
    (fun _ hm => merkleChunks_mem_lt hm) (fun _ hm => merkleChunks_mem_lt hm)
    (by simp [merkleChunks_eq_chunksOf])
    (Option.some_get (merkleCompress_isSome c.eval₁)).symm
    (merkleCompress_get_valid c.eval₁)
    (Option.some_get (merkleCompress_isSome c.eval₂)).symm
    (merkleCompress_get_valid c.eval₂)
    (r₁ := 0) (r₂ := 0)
    (by
      have hx : (PallasGroup.toPoint (PallasGroup.ofPoint _
            (merkleCompress_get_valid c.eval₁))).x
          = (PallasGroup.toPoint (PallasGroup.ofPoint _
            (merkleCompress_get_valid c.eval₂))).x := by
        rw [PallasGroup.toPoint_ofPoint, PallasGroup.toPoint_ofPoint,
          ← merkleCompress_get_x c.eval₁, ← merkleCompress_get_x c.eval₂]
      have hpm := (PallasGroup.toPoint_x_eq_iff _ _).mp hx
      simpa [zero_smul, add_zero] using hpm)
    (by simp [merkleChunks_eq_chunksOf])
    (by
      rintro ⟨hl, -⟩
      obtain ⟨-, hlv, hrv⟩ := merkleChunks_inj
        (lt_trans i.2 (by norm_num)) c.q₁.1.2 c.q₁.2.2
        (lt_trans i.2 (by norm_num)) c.q₂.1.2 c.q₂.2.2 hl
      exact c.ne (Prod.ext (Subtype.ext hlv) (Subtype.ext hrv)))
  toOrchardPoints (V := ![merkleQpt]) (g := ![.idxMerkleQ])
    (gr := fun s => match s with
      | .idxMerkleQ => some 0
      | _ => none)
    (hg := by intro x y; fin_cases x; cases y <;> decide)
    (hpt := fun i => by fin_cases i; rfl) <|
  rel.toOne (by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp rel.nontrivial
    rcases i with i | j
    · exact Or.inl (Function.ne_iff.mpr ⟨i, hi⟩)
    · fin_cases j
      · exact Or.inr hi
      · exact absurd (relationOfChainPmEq_zero_beta _ _ _ _ _ _ _ _ _ _ _) hi)

end Zcash.Security.Ledger.Bridge
