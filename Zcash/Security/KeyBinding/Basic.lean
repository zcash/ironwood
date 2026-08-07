import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Common.RandomOracle

/-!
# Key binding (Orchard / Ironwood)

The deterministic layer of the
[ZIP 2005 key-binding theorem (ROM)](https://zips.z.cash/zip-2005#thm-key-binding-rom): a
verifying Recovery-Statement witness pins the key components — `ak` up to y-sign, `nk`, and the
`qk`/`sk` branch with its key — to `ivk`, unless an explicit break event is computed.

The route, each step proven here:

1. `commit_scalar_pm` — two openings of one `Commitivk` value force their Pedersen scalars equal
   or negated; `CollisionUpToSign.ofOpeningBreak` packages this as computed data.
2. `rivk_eq_finalOracle` — under the derivation constraints, `rivk` is the combined final
   oracle's output at the witness's decoded query.
3. `CollisionUpToSign.ofBreak` — a full `Break` computes a ±-collision of the shifted combined
   oracle at distinct queries; `residual_of_finalQuery_eq` handles coinciding queries.
4. `nk_pinned` / `ak_pinned` / `qk_or_sk_pinned` — without a break, the components agree
   (consumed by the Balance and Spend Authorization arguments).

The probabilistic side — producing the computed collision is hard — is the birthday bound
`ε_kb ≤ q(q-1)/|RIVK|` (`Birthday.lean`, with `|RIVK| = r_ℙ` at the intended Pallas
instantiation), ZIP 2005's `ε_kb` as sharpened in zcash/zips#1338.
nf-pinning, which the Spendability argument consumes, is the games'
`nfOldEqOrBreak` (`Security/Ledger/Statement.lean`).

Abstract setting: a prime-order group `G` as an `RIVK`-vector space. The scalar types are
`RIVK` (rivk values and the rivk-derivation oracle outputs) and `ASK` (`H^ask` outputs, acting
on `G` via `SMul`); both are `= ZMod r` concretely. The base-field types are `IVK`, `AK`, and
`NK` (all `= ZMod q` concretely). An `Extractor` bundles the two extract maps:
`toIVK : G → IVK` carrying the ±-property (`toIVK_pm`), and `toAK : G → AK` for the
derivation side; both instantiate to `Extract_P`. `ivk`'s nonzeroness is the
`KBOpening.nonzero` hypothesis, not a type refinement (`Commit^ivk` can return 0 in circuit
contexts, §4.1.8).

`Commitivk` is required to have the Pedersen structure (not opaque), which is what makes the break
reduction provable; no Pallas instantiation is included (the intended concrete route is via
CompElliptic).
-/

namespace Zcash.Security.KeyBinding

open Zcash.Security.RandomOracle

/-- Which key material backs a witness: the `qk`-branch (`use_qsk = true`) or the `sk`-branch
(`use_qsk = false`). A witness carries exactly one of `qk` or `sk`. -/
inductive Branch (QK SK : Type*) where
  /-- qk-branch: `rivk_ext` derives via `Hrivk_ext`. -/
  | qk : QK → Branch QK SK
  /-- sk-branch: the keys derive via `BindKeys^sk`. -/
  | sk : SK → Branch QK SK
  deriving DecidableEq

/-- A Recovery-Statement / Orchard key witness (ZIP 2005 §"key binding"). `use_qsk` is encoded by
the `qk_or_sk` constructor. The internal-vs-external `ivk` choice is encoded by `rivk`'s value,
not a tag (see `finalQueryOf`). -/
structure Witness (G IVK AK NK RIVK QK SK : Type*) where
  ivk      : IVK
  akP      : G
  nk       : NK
  rivk_ext : RIVK
  rivk     : RIVK
  qk_or_sk : Branch QK SK

variable {G IVK AK NK RIVK ASK QK SK : Type*}

/-- The Pedersen-scalar map a `Commitivk` opening reduces to: `(ak, nk, rivk) ↦ h ak nk + rivk`.
An `OpeningBreak` is exhibited as a `CollisionUpToSign` of this map by
`CollisionUpToSign.ofOpeningBreak`. -/
def pedersenScalar [Add RIVK] (hfn : AK → NK → RIVK) (t : AK × NK × RIVK) : RIVK :=
  let (ak, nk, rivk) := t
  hfn ak nk + rivk

/-- The "final input" to the final `rivk`-derivation random oracle (ZIP 2005 key-binding proof):
the query at which `rivk` is that oracle's output, selected by the `qk`/`sk` branch and the
external/internal ivk choice. -/
inductive FinalQuery (AK NK RIVK QK SK : Type*) where
  /-- qk-branch, external ivk: `rivk = H.rivk_ext qk ak nk`. -/
  | ext : QK → AK → NK → FinalQuery AK NK RIVK QK SK
  /-- sk-branch, external ivk: `rivk = H.rivk_legacy sk`. -/
  | legacy : SK → FinalQuery AK NK RIVK QK SK
  /-- internal ivk: `rivk = Hrivk_int rivk_ext ak nk`. -/
  | int : RIVK → AK → NK → FinalQuery AK NK RIVK QK SK
  deriving DecidableEq

/-- The combined final `rivk`-derivation random oracle: dispatch each final query to its oracle. -/
def FinalQuery.eval (Hrivk_legacy : SK → RIVK) (Hrivk_ext : QK → AK → NK → RIVK)
    (Hrivk_int : RIVK → AK → NK → RIVK) : FinalQuery AK NK RIVK QK SK → RIVK
  | .ext qk ak nk => Hrivk_ext qk ak nk
  | .legacy sk => Hrivk_legacy sk
  | .int rivk_ext ak nk => Hrivk_int rivk_ext ak nk

/-- The two extract maps of the key-binding model; both instantiate to `Extract_P`
concretely, and both carry the ±-property. `toIVK` serves the commitment opening; `toAK`
serves the derivation and projection side. -/
structure Extractor (G IVK AK : Type*) [Neg G] where
  toIVK : G → IVK
  toAK : G → AK
  /-- `toIVK` identifies exactly the ±-pairs (the x-coordinate property). At the identity
  point the concrete x-coordinate instantiation needs "no Pallas point has x = 0"
  (x = 0 forces y² = 5, a non-square). -/
  toIVK_pm : ∀ P Q : G, toIVK P = toIVK Q ↔ P =± Q
  /-- `toAK` identifies exactly the ±-pairs, like `toIVK`. The forward direction is what
  discharges the games' `break_of_akP_ne`: `ak` is consumed as a single extracted
  coordinate, so two witnesses whose `ak^ℙ` differ by more than y-sign have different
  break projections. -/
  toAK_pm : ∀ P Q : G, toAK P = toAK Q ↔ P =± Q

/-- `toIVK` is at most 2-to-1 (`toIVK_pm`), so the `IVK` domain is at least half the group:
`|G| ≤ 2·|IVK|`. An `IVK` small enough to find collisions in admits no `Extractor` at all —
undersized instantiations make the key-binding theorems vacuous rather than falsely secure.
This is why the birthday bounds involve only `|RIVK|`: `ivk`-derivation collisions are
excluded exactly, which the deployed x-coordinate extraction satisfies (exactly 2-to-1 on
±-pairs). A hash-derived `ivk` (Sapling's `CRH^ivk`) does not satisfy `toIVK_pm` and would
need a collision-resistance term in the bound instead. -/
theorem Extractor.card_ivk_ge [Neg G] [Fintype G] [Fintype IVK] [DecidableEq G]
    [DecidableEq IVK] (Extract : Extractor G IVK AK) :
    Fintype.card G ≤ 2 * Fintype.card IVK := by
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := Extract.toIVK) (fun a _ => Finset.mem_univ _) 2 fun b _ => ?_
  by_cases hb : ∃ P, Extract.toIVK P = b
  · obtain ⟨P, hP⟩ := hb
    calc ((Finset.univ : Finset G).filter fun x => Extract.toIVK x = b).card
        ≤ ({P, -P} : Finset G).card := Finset.card_le_card fun x hx => by
            rw [Finset.mem_filter] at hx
            rcases (Extract.toIVK_pm x P).mp (hx.2.trans hP.symm) with h | h <;>
              simp [Finset.mem_insert, h]
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
  · rw [Finset.filter_eq_empty_iff.mpr fun {x} _ => fun hx => hb ⟨x, hx⟩]
    simp

section Algebra
variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [NoZeroSMulDivisors RIVK G]

/-- The `ivk` commitment as a Pedersen lift:
`Commitivk rivk ak nk = Extract.toIVK ((h ak nk + rivk) • S)`, with `h` abstract-but-non-querying and `S`
a fixed base. Mirrors the `NoteCommit` repair `(H^rcm + f) • R`. -/
def Commitivk (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (rivk : RIVK)
    (ak : AK) (nk : NK) : IVK :=
  Extract.toIVK ((hfn ak nk + rivk) • S)

omit [Field IVK] in
/-- Algebraic core: two openings of the same `Commitivk` value force their Pedersen scalars to be
equal or negatives — the deterministic content the whole key-binding reduction rests on. Proved
from the `toIVK` ±-property and injectivity of `· • S` for `S ≠ 0` (`smul_left_injective`;
`G` is an `F`-vector space). -/
theorem commit_scalar_pm
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (hS : S ≠ 0)
    {rivk₁ rivk₂ : RIVK} {ak₁ ak₂ : AK} {nk₁ nk₂ : NK}
    (hcm : Commitivk Extract S hfn rivk₁ ak₁ nk₁ = Commitivk Extract S hfn rivk₂ ak₂ nk₂) :
    hfn ak₁ nk₁ + rivk₁ =± hfn ak₂ nk₂ + rivk₂ := by
  unfold Commitivk at hcm
  rw [Extract.toIVK_pm] at hcm
  rcases hcm with hcm | hcm
  · exact Or.inl (smul_left_injective RIVK hS hcm)
  · refine Or.inr (smul_left_injective RIVK hS ?_)
    show (hfn ak₁ nk₁ + rivk₁) • S = (-(hfn ak₂ nk₂ + rivk₂)) • S
    rw [neg_smul]
    exact hcm

/-- `KBOpening` — the commitment-opening core of the key-binding condition (what statement-validity
yields). -/
structure KBOpening (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (w : Witness G IVK AK NK RIVK QK SK) : Prop where
  /-- `ivk` opens as `Commitivk` at `(rivk, ak, nk)`. -/
  commit : w.ivk = Commitivk Extract S hfn w.rivk (Extract.toAK w.akP) w.nk
  /-- `ivk ≠ 0` (ZIP 2005 requires `ivk ∉ {0, ⊥}`). No proof in this development consumes
  it; its discharge belongs to the statement instantiation. -/
  nonzero : w.ivk ≠ 0

/-- `OpeningBreak` — a `Commitivk`-opening collision (produced by the games layer): two valid
`KBOpening` witnesses with the same `ivk` but differing `(ak, nk, rivk)`. -/
structure OpeningBreak (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK)
    (w₁ w₂ : Witness G IVK AK NK RIVK QK SK) : Prop where
  opening₁ : KBOpening Extract S hfn w₁
  opening₂ : KBOpening Extract S hfn w₂
  ivk_eq : w₁.ivk = w₂.ivk
  /-- The witnesses differ in the opening data. -/
  proj_ne : (Extract.toAK w₁.akP, w₁.nk, w₁.rivk) ≠ (Extract.toAK w₂.akP, w₂.nk, w₂.rivk)

/-- The deterministic reduction (composable core), as computed data: an `OpeningBreak` exhibits a
±-collision of the Pedersen-scalar map `pedersenScalar hfn`. The colliding queries are the two
`(ak, nk, rivk)` triples read off the witnesses; the break's distinctness and `commit_scalar_pm`
supply the erased `Prop` fields, so the data is genuinely computed, not extracted from a proof.

This is an intermediate certificate, not a break event: `pedersenScalar` is affine in `rivk`, so a
standalone inhabitant is computable outright. The security content is conditional on the
`OpeningBreak` hypothesis; hardness enters per-instantiation, where `rivk` is an `H^*` output
(`KBDerivation`) and the birthday bound applies. -/
def _root_.Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (hS : S ≠ 0)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK} (hbrk : OpeningBreak Extract S hfn w₁ w₂) :
    RandomOracle.CollisionUpToSign (pedersenScalar hfn) where
  q₁ := (Extract.toAK w₁.akP, w₁.nk, w₁.rivk)
  q₂ := (Extract.toAK w₂.akP, w₂.nk, w₂.rivk)
  ne := hbrk.proj_ne
  pm := by
    -- Commitivk(w₁) = w₁.ivk = w₂.ivk = Commitivk(w₂)
    simpa [pedersenScalar] using
      commit_scalar_pm Extract S hfn hS
        (hbrk.opening₁.commit.symm.trans (hbrk.ivk_eq.trans hbrk.opening₂.commit))

end Algebra


/-- The five random oracles of the key-binding model (ZIP 2005): `H^ask`, `H^nk`, and the
three final `rivk`-derivation oracles. Bundled so the derivation layer's signatures carry
one parameter; the probabilistic capstones assemble the bundle from `H^ask`/`H^nk` and the
sampled table's restrictions. -/
structure Oracles (AK NK RIVK ASK QK SK : Type*) where
  ask : SK → ASK
  nk : SK → NK
  rivk_legacy : SK → RIVK
  rivk_ext : QK → AK → NK → RIVK
  rivk_int : RIVK → AK → NK → RIVK

section Derivation
variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [SMul ASK G]

/-- `BindKeys^sk` (ZIP 2005): the `sk`-branch derivation constraints. -/
structure BindKeysSk (Ggen : G) (H : Oracles AK NK RIVK ASK QK SK)
    (sk : SK) (akP : G) (nk : NK) (rivk_ext : RIVK) : Prop where
  akP_eq : akP = (H.ask sk) • Ggen
  nk_eq : nk = H.nk sk
  rivk_ext_eq : rivk_ext = H.rivk_legacy sk

/-- `KBDerivation` — the ZIP 2005 derivation constraints (the `qk_or_sk` branch structure is
enforced by the `Branch` type). -/
structure KBDerivation (Extract : Extractor G IVK AK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    (w : Witness G IVK AK NK RIVK QK SK) : Prop where
  /-- The per-branch constraint: `Hrivk_ext` on the qk-branch, `BindKeys^sk` on the sk-branch. -/
  branch : match w.qk_or_sk with
    | .qk qk => w.rivk_ext = H.rivk_ext qk (Extract.toAK w.akP) w.nk
    | .sk sk => BindKeysSk Ggen H sk w.akP w.nk w.rivk_ext
  /-- `rivk ∈ {rivk_ext, Hrivk_int ...}`. -/
  rivk_choice : w.rivk = w.rivk_ext ∨ w.rivk = H.rivk_int w.rivk_ext (Extract.toAK w.akP) w.nk

end Derivation

section Full
variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [SMul ASK G]

/-- The full key-binding condition: commitment opening and key derivation constraints. -/
structure KB (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    (w : Witness G IVK AK NK RIVK QK SK) : Prop where
  opening : KBOpening Extract S hfn w
  derivation : KBDerivation Extract Ggen H w

/-- The break projection of a witness: the components a key-binding break must differ in. Using
`ak = Extract.toAK ak^ℙ` quotients the y-sign of `ak^ℙ`. -/
structure BreakProj (AK NK RIVK QK SK : Type*) where
  ak : AK
  nk : NK
  rivk : RIVK
  qk_or_sk : Branch QK SK

/-- The break projection, read off a witness. -/
def Witness.breakProj (Extract : Extractor G IVK AK) (w : Witness G IVK AK NK RIVK QK SK) :
    BreakProj AK NK RIVK QK SK :=
  ⟨Extract.toAK w.akP, w.nk, w.rivk, w.qk_or_sk⟩

/-- A full key-binding break (ZIP 2005): two valid witnesses with equal `ivk` and differing
break projections. -/
structure Break (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    (w₁ w₂ : Witness G IVK AK NK RIVK QK SK) : Prop where
  kb₁ : KB Extract S hfn Ggen H w₁
  kb₂ : KB Extract S hfn Ggen H w₂
  ivk_eq : w₁.ivk = w₂.ivk
  /-- The witnesses differ in the break projection. -/
  proj_ne : w₁.breakProj Extract ≠ w₂.breakProj Extract

/-- `nk`-pinning (consumed by the Balance argument): two valid witnesses with the same `ivk`
that do **not** form a key-binding break must share the same nullifier key `nk`. (The
probability that a break *does* occur is the birthday bound.) -/
theorem nk_pinned (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (h₁ : KB Extract S hfn Ggen H w₁)
    (h₂ : KB Extract S hfn Ggen H w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen H w₁ w₂) :
    w₁.nk = w₂.nk := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  exact congrArg BreakProj.nk heq

/-- `ak`-pinning up to y-sign (consumed by the Spend Authorization argument): two valid
witnesses with the same `ivk` that do *not* form a key-binding break share the same
`ak = Extract.toAK ak^ℙ` — i.e. `ak^ℙ` is pinned up to its y-sign, matching the protocol's
choice to consume `ak` as a single x-coordinate. -/
theorem ak_pinned (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (h₁ : KB Extract S hfn Ggen H w₁)
    (h₂ : KB Extract S hfn Ggen H w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen H w₁ w₂) :
    Extract.toAK w₁.akP = Extract.toAK w₂.akP := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  exact congrArg BreakProj.ak heq

/-- `qk`/`sk`-pinning (consumed by the Spend Authorization argument): two valid witnesses
with the same `ivk` that do *not* form a key-binding break share the same branch — the same
`qk` or the same `sk`, including *which* of the two backs the witness. This is stronger than
ZIP 2005's former statement, which determined `qk`'s value when present but not which branch
backs the witness. -/
theorem qk_or_sk_pinned (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (h₁ : KB Extract S hfn Ggen H w₁)
    (h₂ : KB Extract S hfn Ggen H w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen H w₁ w₂) :
    w₁.qk_or_sk = w₂.qk_or_sk := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  exact congrArg BreakProj.qk_or_sk heq

end Full

section Onward
variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [SMul ASK G] [DecidableEq RIVK]

/-- The `rivk_ext`-derivation query of a witness: the query at which the combined final oracle
produces its `rivk_ext`, selected by the branch. Never `.int` (`extQueryOf_ne_int`). -/
def extQueryOf (Extract : Extractor G IVK AK) (w : Witness G IVK AK NK RIVK QK SK) : FinalQuery AK NK RIVK QK SK :=
  match w.qk_or_sk with
  | .qk qk => .ext qk (Extract.toAK w.akP) w.nk
  | .sk sk => .legacy sk

/-- The final query of a witness: which final oracle produces its `rivk`, and at what input.
Selected by the external/internal ivk choice (`rivk = rivk_ext`?) and then the branch.
The external/internal choice is decoded from the fields, not carried as witness data: at a
fixpoint `Hrivk_int rivk_ext ak nk = rivk_ext`, an internally-derived witness decodes as
external — harmless for `rivk_eq_finalOracle` (which holds either way), but the birthday
accounting must partition query pairs by this decode, not by how the witnesses were
derived. -/
def finalQueryOf (Extract : Extractor G IVK AK) (w : Witness G IVK AK NK RIVK QK SK) : FinalQuery AK NK RIVK QK SK :=
  if w.rivk = w.rivk_ext then extQueryOf Extract w
  else .int w.rivk_ext (Extract.toAK w.akP) w.nk

omit [Field IVK] [Field RIVK] [Module RIVK G] in
/-- **Final-random-oracle representation** (ZIP 2005 key-binding proof, "Final-random-oracle
structure"): under the derivation constraints, `rivk` is the output of the combined final oracle at
the witness's `finalQueryOf`. It bridges the Pedersen-scalar collision
(`CollisionUpToSign.ofOpeningBreak`) to a collision of the actual `H^*` oracles. What remains
probabilistic is only the birthday bound over the final-query space. -/
theorem rivk_eq_finalOracle
    (Extract : Extractor G IVK AK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w : Witness G IVK AK NK RIVK QK SK}
    (hd : KBDerivation Extract Ggen H w) :
    w.rivk = (finalQueryOf Extract w).eval H.rivk_legacy H.rivk_ext H.rivk_int := by
  obtain ⟨hbc, hrivk⟩ := hd
  unfold finalQueryOf extQueryOf
  by_cases hext : w.rivk = w.rivk_ext
  · rw [if_pos hext]
    rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc ⊢ <;> simp only [FinalQuery.eval]
    · rw [hext, hbc]
    · rw [hext, hbc.rivk_ext_eq]
  · rw [if_neg hext]
    simp only [FinalQuery.eval]
    exact hrivk.resolve_left hext

/-- The non-querying shift: `hfn` at the query's key data (for `.legacy sk`, `ak`/`nk` are
recovered via `Hask`/`Hnk`, so the shift is a function of the query alone). -/
def shiftOf (Extract : Extractor G IVK AK) (Ggen : G) (hfn : AK → NK → RIVK)
    (Hask : SK → ASK) (Hnk : SK → NK) : FinalQuery AK NK RIVK QK SK → RIVK
  | .ext _ ak nk => hfn ak nk
  | .legacy sk => hfn (Extract.toAK ((Hask sk) • Ggen)) (Hnk sk)
  | .int _ ak nk => hfn ak nk

/-- The *shifted* combined final oracle: the `H^*` output offset by the non-querying shift.
The ±-collision a `Break` computes (`CollisionUpToSign.ofBreak`) is of this map — the event
the birthday layer bounds. -/
def shiftedFinalOracle (Extract : Extractor G IVK AK) (Ggen : G) (hfn : AK → NK → RIVK)
    (H : Oracles AK NK RIVK ASK QK SK)
    (q : FinalQuery AK NK RIVK QK SK) : RIVK :=
  shiftOf Extract Ggen hfn H.ask H.nk q + q.eval H.rivk_legacy H.rivk_ext H.rivk_int

omit [Field IVK] [Module RIVK G] in
/-- On a witness's `finalQueryOf`, the shifted oracle is the shift plus the `H^*` output — the form
`sameIvk_finalOracle_pm`'s equation is stated in. -/
theorem shiftedFinalOracle_finalQueryOf
    (Extract : Extractor G IVK AK) (Ggen : G) (hfn : AK → NK → RIVK)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w : Witness G IVK AK NK RIVK QK SK}
    (hd : KBDerivation Extract Ggen H w) :
    shiftedFinalOracle Extract Ggen hfn H
        (finalQueryOf Extract w)
      = hfn (Extract.toAK w.akP) w.nk
          + (finalQueryOf Extract w).eval H.rivk_legacy H.rivk_ext H.rivk_int := by
  obtain ⟨hbc, hrivk⟩ := hd
  unfold finalQueryOf extQueryOf
  by_cases hext : w.rivk = w.rivk_ext
  · rw [if_pos hext]
    rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc ⊢
    · simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval]
    · obtain ⟨hakP, hnk, _⟩ := hbc
      simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval, ← hakP, ← hnk]
  · rw [if_neg hext]
    simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval]

end Onward

section OnwardCollision
variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [NoZeroSMulDivisors RIVK G]
variable [SMul ASK G] [DecidableEq RIVK]

/-- **Same-`ivk` ±-equation over `H^*`.** Two witnesses opening the same `ivk` (`KBOpening`), both
satisfying the derivation constraints, give the ZIP 2005 break equation with the final-oracle
structure substituted: `h(ak₁,nk₁) + H^*(q₁) = ±(h(ak₂,nk₂) + H^*(q₂))`, where `H^*` is the
combined final oracle (`FinalQuery.eval`) and `qᵢ = finalQueryOf wᵢ`.

No distinctness is needed: the ±-equation holds for *every* same-`ivk` pair, and only the break
notions (`OpeningBreak`, `Break`) carry a distinctness witness. That is why this is a bare
equation rather than a full `CollisionUpToSign`; the `ne` field arrives with
`CollisionUpToSign.ofBreak`'s case split. -/
theorem sameIvk_finalOracle_pm
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (hop₁ : KBOpening Extract S hfn w₁) (hop₂ : KBOpening Extract S hfn w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hd₁ : KBDerivation Extract Ggen H w₁)
    (hd₂ : KBDerivation Extract Ggen H w₂) :
    hfn (Extract.toAK w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval H.rivk_legacy H.rivk_ext H.rivk_int
      =± hfn (Extract.toAK w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval H.rivk_legacy H.rivk_ext H.rivk_int := by
  have hcm : Commitivk Extract S hfn w₁.rivk (Extract.toAK w₁.akP) w₁.nk
      = Commitivk Extract S hfn w₂.rivk (Extract.toAK w₂.akP) w₂.nk :=
    hop₁.commit.symm.trans (hivk.trans hop₂.commit)
  have hpm := commit_scalar_pm Extract S hfn hS hcm
  rw [rivk_eq_finalOracle Extract Ggen H hd₁,
      rivk_eq_finalOracle Extract Ggen H hd₂] at hpm
  exact hpm

/-- The `H^*` ±-equation from an `OpeningBreak` (the object the games produce): the same-`ivk`
core `sameIvk_finalOracle_pm` applied to the break's two openings. -/
theorem openingBreak_finalOracle_pm
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (hbrk : OpeningBreak Extract S hfn w₁ w₂)
    (hd₁ : KBDerivation Extract Ggen H w₁)
    (hd₂ : KBDerivation Extract Ggen H w₂) :
    hfn (Extract.toAK w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval H.rivk_legacy H.rivk_ext H.rivk_int
      =± hfn (Extract.toAK w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval H.rivk_legacy H.rivk_ext H.rivk_int :=
  sameIvk_finalOracle_pm Extract S hfn Ggen hS H
    hbrk.opening₁ hbrk.opening₂ hbrk.ivk_eq hd₁ hd₂

/-- The `H^*` ±-equation from a full key-binding `Break` (break projections differing). The
derivation constraints are already inside the `Break` (via `KB`), and *no* `Break → OpeningBreak`
upgrade is needed: the equation depends only on the openings and `ivk`-equality, never on how the
projections differ. `CollisionUpToSign.ofBreak` builds its case split on this. -/
theorem break_finalOracle_pm
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (hbrk : Break Extract S hfn Ggen H w₁ w₂) :
    hfn (Extract.toAK w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval H.rivk_legacy H.rivk_ext H.rivk_int
      =± hfn (Extract.toAK w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval H.rivk_legacy H.rivk_ext H.rivk_int :=
  sameIvk_finalOracle_pm Extract S hfn Ggen hS H
    hbrk.kb₁.opening hbrk.kb₂.opening hbrk.ivk_eq hbrk.kb₁.derivation hbrk.kb₂.derivation

/-- The break projection an *externally-decoded* witness must have, read off its
`rivk_ext`-derivation query (`proj_eq_projOfQuery`); `.int` is not in `extQueryOf`'s image. -/
def projOfQuery (Extract : Extractor G IVK AK) (Ggen : G) (H : Oracles AK NK RIVK ASK QK SK) :
    FinalQuery AK NK RIVK QK SK → Option (BreakProj AK NK RIVK QK SK)
  | .ext qk ak nk => some ⟨ak, nk, H.rivk_ext qk ak nk, .qk qk⟩
  | .legacy sk => some ⟨Extract.toAK ((H.ask sk) • Ggen), H.nk sk, H.rivk_legacy sk, .sk sk⟩
  | .int _ _ _ => none

/-- The Branch data of a witness, read off its `rivk_ext`-derivation query
(`branch_eq_branchOfQuery`); `.int` is not in `extQueryOf`'s image. -/
def branchOfQuery : FinalQuery AK NK RIVK QK SK → Option (Branch QK SK)
  | .ext qk _ _ => some (.qk qk)
  | .legacy sk => some (.sk sk)
  | .int _ _ _ => none

omit [Field IVK] [Field RIVK] [NoZeroSMulDivisors RIVK G] [DecidableEq RIVK] in
/-- A witness's Branch data is recoverable from its `rivk_ext`-derivation query. -/
theorem branch_eq_branchOfQuery {w : Witness G IVK AK NK RIVK QK SK} (Extract : Extractor G IVK AK) :
    some w.qk_or_sk = branchOfQuery (extQueryOf Extract w) := by
  rcases hb : w.qk_or_sk with qk | sk <;> simp [extQueryOf, branchOfQuery, hb]

omit [Field IVK] [Field RIVK] [NoZeroSMulDivisors RIVK G] [DecidableEq RIVK] in
/-- A witness's `rivk_ext`-derivation query is never `.int`. -/
theorem extQueryOf_ne_int {w : Witness G IVK AK NK RIVK QK SK} (Extract : Extractor G IVK AK)
    (rivk_ext : RIVK) (ak : AK) (nk : NK) :
    extQueryOf Extract w ≠ .int rivk_ext ak nk := by
  rcases hb : w.qk_or_sk with qk | sk <;> simp [extQueryOf, hb]

omit [Field IVK] [NoZeroSMulDivisors RIVK G] [DecidableEq RIVK] [Field RIVK] [Module RIVK G] in
/-- An externally-decoded witness's break projection is recoverable from its `rivk_ext`-derivation
query: the derivation constraints determine every component from the query. -/
theorem proj_eq_projOfQuery
    (Extract : Extractor G IVK AK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w : Witness G IVK AK NK RIVK QK SK}
    (hd : KBDerivation Extract Ggen H w)
    (hext : w.rivk = w.rivk_ext) :
    some (w.breakProj Extract)
      = projOfQuery Extract Ggen H (extQueryOf Extract w) := by
  obtain ⟨hbc, _⟩ := hd
  rcases hb : w.qk_or_sk with qk | sk <;> simp only [Witness.breakProj, hb] at hbc ⊢ <;>
    simp only [extQueryOf, hb, projOfQuery]
  · rw [hext.trans hbc]
  · obtain ⟨hakP, hnk, hre⟩ := hbc
    rw [hakP, hnk, hext.trans hre]

omit [Field IVK] [NoZeroSMulDivisors RIVK G] [DecidableEq RIVK] [Module RIVK G] in
/-- A witness's shifted-oracle output at its `rivk_ext`-derivation query is
`hfn (ak, nk) + rivk_ext`: the derivation constraints collapse the per-branch shift to the
witness's own key data. -/
theorem shiftedFinalOracle_extQueryOf
    (Extract : Extractor G IVK AK) (Ggen : G) (hfn : AK → NK → RIVK)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w : Witness G IVK AK NK RIVK QK SK}
    (hd : KBDerivation Extract Ggen H w) :
    shiftedFinalOracle Extract Ggen hfn H
        (extQueryOf Extract w)
      = hfn (Extract.toAK w.akP) w.nk + w.rivk_ext := by
  obtain ⟨hbc, _⟩ := hd
  rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc <;>
    simp only [extQueryOf, hb, shiftedFinalOracle, shiftOf, FinalQuery.eval]
  · rw [← hbc]
  · obtain ⟨hakP, hnk, hre⟩ := hbc
    rw [← hakP, ← hnk, ← hre]

omit [NoZeroSMulDivisors RIVK G] in
/-- **The residual case is deterministic**: if a `Break`'s two final queries coincide, then both
witnesses are internally derived, sharing `(ak, nk, rivk_ext, rivk)` and differing in `qk_or_sk`.
The collision then relocates to the `rivk_ext`-derivation queries, at which the shifted oracle's
outputs are *equal* and the queries are *distinct*. -/
theorem residual_of_finalQuery_eq
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (hbrk : Break Extract S hfn Ggen H w₁ w₂)
    (hq : finalQueryOf Extract w₁ = finalQueryOf Extract w₂) :
    extQueryOf Extract w₁ ≠ extQueryOf Extract w₂ ∧
    shiftedFinalOracle Extract Ggen hfn H
        (extQueryOf Extract w₁)
      = shiftedFinalOracle Extract Ggen hfn H
        (extQueryOf Extract w₂) := by
  obtain ⟨⟨hop₁, hd₁⟩, ⟨hop₂, hd₂⟩, hivk, hne5⟩ := hbrk
  unfold finalQueryOf at hq
  by_cases hext₁ : w₁.rivk = w₁.rivk_ext
  · rw [if_pos hext₁] at hq
    by_cases hext₂ : w₂.rivk = w₂.rivk_ext
    · -- external × external: the projections coincide, contradicting the break's distinctness
      rw [if_pos hext₂] at hq
      exact absurd (Option.some_inj.mp
        (((proj_eq_projOfQuery Extract Ggen H
            hd₁ hext₁).trans (by rw [hq])).trans
          (proj_eq_projOfQuery Extract Ggen H
            hd₂ hext₂).symm)) hne5
    · -- external × internal: constructor clash
      rw [if_neg hext₂] at hq
      exact absurd hq (extQueryOf_ne_int Extract _ _ _)
  · rw [if_neg hext₁] at hq
    by_cases hext₂ : w₂.rivk = w₂.rivk_ext
    · -- internal × external: constructor clash
      rw [if_pos hext₂] at hq
      exact absurd hq.symm (extQueryOf_ne_int Extract _ _ _)
    · -- internal × internal: the genuine residual
      rw [if_neg hext₂] at hq
      simp only [FinalQuery.int.injEq] at hq
      obtain ⟨hre, hak, hnk⟩ := hq
      have hrv : w₁.rivk = w₂.rivk := by
        rw [hd₁.rivk_choice.resolve_left hext₁, hd₂.rivk_choice.resolve_left hext₂, hre, hak,
          hnk]
      refine ⟨fun h => hne5 ?_, ?_⟩
      · -- equal `extQueryOf`s would equate qk_or_sk, hence the whole projections
        have hbr : w₁.qk_or_sk = w₂.qk_or_sk :=
          Option.some_inj.mp ((branch_eq_branchOfQuery (w := w₁) Extract).trans
            ((congrArg branchOfQuery h).trans (branch_eq_branchOfQuery (w := w₂) Extract).symm))
        simp only [Witness.breakProj]
        rw [hbr, hak, hnk, hrv]
      · rw [shiftedFinalOracle_extQueryOf Extract Ggen hfn H hd₁,
          shiftedFinalOracle_extQueryOf Extract Ggen hfn H hd₂, hak, hnk, hre]

/-- **The ZIP 2005 break event, as a computed random-oracle ±-collision** — the terminal object of
the deterministic layer. A full key-binding `Break` computes a `CollisionUpToSign` of the shifted
combined final oracle at *distinct* queries: the two witnesses' final queries when they differ, or
(the residual case, `residual_of_finalQuery_eq`) the two `rivk_ext`-derivation queries when they
coincide. What the birthday bound then adds is that inhabiting this event is hard: `hfn` is
non-querying, so a fixed shift cannot be steered to manufacture collisions, and ±-colliding the
shifted oracle at distinct queries has probability at most `q(q-1)/|RIVK|`
(`Birthday.lean`). -/
def _root_.Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak
    [DecidableEq AK] [DecidableEq NK] [DecidableEq QK] [DecidableEq SK]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (H : Oracles AK NK RIVK ASK QK SK)
    {w₁ w₂ : Witness G IVK AK NK RIVK QK SK}
    (hbrk : Break Extract S hfn Ggen H w₁ w₂) :
    RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn H
        (QK := QK) (SK := SK)) :=
  if hq : finalQueryOf Extract w₁ = finalQueryOf Extract w₂ then
    { q₁ := extQueryOf Extract w₁
      q₂ := extQueryOf Extract w₂
      ne := (residual_of_finalQuery_eq Extract S hfn Ggen H hbrk hq).1
      pm := Or.inl (residual_of_finalQuery_eq Extract S hfn Ggen H hbrk hq).2 }
  else
    { q₁ := finalQueryOf Extract w₁
      q₂ := finalQueryOf Extract w₂
      ne := hq
      pm := by
        rw [shiftedFinalOracle_finalQueryOf Extract Ggen hfn H hbrk.kb₁.derivation,
            shiftedFinalOracle_finalQueryOf Extract Ggen hfn H hbrk.kb₂.derivation]
        exact break_finalOracle_pm Extract S hfn Ggen hS H hbrk }

omit [Field IVK] [NoZeroSMulDivisors RIVK G] [Module RIVK G] in
/-- **The bridge to the birthday counting**: the pair of `H^*` outputs at a shifted-oracle
±-collision's queries lies in the shifted ±-collision set that
`Birthday.card_shifted_pm_collision_le` counts, with the shifts read off the queries. Combined
with the collision's `ne` field (distinct queries) this is the per-pair event whose fraction the
birthday layer bounds by `2/|F|`. -/
theorem collision_mem_shifted_pm [Fintype RIVK]
    (Extract : Extractor G IVK AK) (Ggen : G) (hfn : AK → NK → RIVK)
    (H : Oracles AK NK RIVK ASK QK SK)
    (c : RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn H
        (QK := QK) (SK := SK))) :
    (c.q₁.eval H.rivk_legacy H.rivk_ext H.rivk_int, c.q₂.eval H.rivk_legacy H.rivk_ext H.rivk_int)
      ∈ Finset.univ.filter (fun p : RIVK × RIVK =>
          shiftOf Extract Ggen hfn H.ask H.nk c.q₁ + p.1
            =± shiftOf Extract Ggen hfn H.ask H.nk c.q₂ + p.2) := by
  simpa [shiftedFinalOracle] using c.pm

end OnwardCollision

end Zcash.Security.KeyBinding
