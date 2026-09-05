import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Spendability
import Zcash.Common.DiscreteLogRelation

/-!
# The nullifier-binding reduction

`NullifierCollision` (two distinct note openings whose nullifiers agree) reduces to a
nontrivial discrete-log relation, once the derivation's shape is given. The deployed
shape (the [Orchard nullifier design](https://zcash.github.io/orchard/design/nullifiers.html))
is additive:

    DeriveNullifier_nk(ρ, ψ, cm) = Extract((scalar nk ρ ψ) • K + cm)
    NoteCommit_rcm(note)         = (∑ i, coeff(note) i • bases i) + rcm • R

with `K` the nullifier base (𝒦^Orchard), `R` the commitment randomness base, `scalar`
the composite `PRF^nf_nk(ρ) + ψ` — the addition taken in the Pallas *base* field, with
the sum then reinterpreted as a scalar — and the commitment's hash point exposed as a
fixed-base combination: for Sinsemilla, `2^n • 𝒬 + ∑ 2^(n-i) • 𝒮(m_i)` over the fixed
bases `𝒬, 𝒮(0), …`, with the coefficients determined by the note's encoding. Adding
`cm` is what lets the collision argument avoid a PRF-collision assumption: the
nullifier is in effect a Pedersen hash whose input includes ρ directly, so Faerie
Resistance rests on discrete log alone (see the
[design page's rationale](https://zcash.github.io/orchard/design/nullifiers.html#rationale)).

`NontrivialRelation.ofNullifierCollision` computes the reduction: a `NullifierCollision`
yields a `NontrivialRelation` among the commitment bases, `K`, and `R` — the same
terminal, under the same independent-hash-to-curve-bases discharge, as the balance
argument's relations. The extract ±-property splits into two sign cases; nontriviality
comes from the coefficient vectors (their difference is nonzero for distinct notes,
their sum is never zero — concretely both hold via the initial `2^n • 𝒬` term, whose
binary-expansion coefficients determine the message).

The reduction needs no distinct-notes premiss: the collision's own opening distinctness
(`(rcm₁, note₁) ≠ (rcm₂, note₂)`) covers every case — distinct notes use the coefficient
difference, and equal notes force `rcm₁ ≠ rcm₂`, a nonzero randomness coefficient. So it
composes directly with the game-produced collisions of `faerieGoldCore` /
`spendabilityOrBreak`, which hold exactly that inequality at construction. (The
equal-note, equal-`rcm`, distinct-`nk` case — the PRF collision the design page
discusses — cannot arise: equal openings pin `cm`, so the two spends would coincide.)
-/

namespace Zcash.Security.Ledger.Model

open scoped Zcash.Security.RandomOracle

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}

/-- The additive shape of the deployed nullifier derivation: derivation is a scalar
multiple of the nullifier base `K` plus the commitment point, extracted to `RHO`
(nullifiers share ρ's type), and commitments open as a coefficient combination of the
fixed `bases` plus a multiple of the randomness base `R`. `extract` is the shape's own
coordinate extractor — the model types nullifiers as `RHO` while `P.extract` lands in
`MHASH`, though both are `Extract_ℙ` concretely — and `extract_pm` is its ±-property
(fibres `{P, −P}`).

Intended model: the Orchard nullifier design, with `scalar nk ρ ψ` the composite
`PRF^nf_nk(ρ) + ψ` — added in the Pallas base field, the sum then reinterpreted as a
scalar — and the commitment hash Sinsemilla, whose defined values are the fixed-base
combinations `2^n • 𝒬 + ∑ 2^(n-i) • 𝒮(m_i)`. The two coefficient conditions hold
there because every coefficient vector carries the initial term's `2^n` at `𝒬`, and
the per-base coefficients' binary expansions determine the message. -/
structure NullifierShape (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) where
  /-- The number of fixed commitment bases. -/
  numBases : ℕ
  /-- The commitment's fixed bases (for Sinsemilla: `𝒬, 𝒮(0), 𝒮(1), …`). -/
  bases : Fin numBases → G
  /-- The nullifier base (𝒦^Orchard). -/
  K : G
  /-- The commitment randomness base. -/
  R : G
  scalar : NK → RHO → PSI → F
  extract : G → RHO
  /-- The commitment hash's coefficient vector at a note's encoding; `none` is an
  escaped hash. -/
  coeff : Note G RHO PSI → Option (Fin numBases → F)
  derive_eq : ∀ nk ρ ψ cm,
    P.deriveNullifier nk ρ ψ cm = extract (scalar nk ρ ψ • K + cm)
  commit_eq : ∀ rcm note,
    P.noteCommit rcm note
      = (coeff note).map (fun cf => (∑ i, cf i • bases i) + rcm • R)
  extract_pm : ∀ x y : G, extract x = extract y → x =± y
  /-- Distinct notes have distinct coefficient vectors (injective encoding). -/
  coeff_sub_ne : ∀ {note₁ note₂ : Note G RHO PSI} {cf₁ cf₂ : Fin numBases → F},
    coeff note₁ = some cf₁ → coeff note₂ = some cf₂ → note₁ ≠ note₂ → cf₁ - cf₂ ≠ 0
  /-- Coefficient vectors never cancel additively (the initial-base term). -/
  coeff_add_ne : ∀ {note₁ note₂ : Note G RHO PSI} {cf₁ cf₂ : Fin numBases → F},
    coeff note₁ = some cf₁ → coeff note₂ = some cf₂ → cf₁ + cf₂ ≠ 0

namespace NullifierShape

variable (S : NullifierShape P) (c : NullifierCollision P)

/-- The first opening's coefficient vector is defined, from the opening. -/
theorem coeff₁_isSome : (S.coeff c.note₁).isSome := by
  have h := c.open₁
  rw [S.commit_eq] at h
  rcases Option.map_eq_some_iff.mp h with ⟨cf, hcf, -⟩
  simp [hcf]

/-- The second opening's coefficient vector is defined, from the opening. -/
theorem coeff₂_isSome : (S.coeff c.note₂).isSome := by
  have h := c.open₂
  rw [S.commit_eq] at h
  rcases Option.map_eq_some_iff.mp h with ⟨cf, hcf, -⟩
  simp [hcf]

/-- The first commitment decomposes over the fixed bases. -/
theorem cm₁_eq :
    c.cm₁ = (∑ i, (S.coeff c.note₁).get (S.coeff₁_isSome c) i • S.bases i)
      + c.rcm₁ • S.R := by
  have h := c.open₁
  rw [S.commit_eq] at h
  rcases Option.map_eq_some_iff.mp h with ⟨cf, hcf, hcm⟩
  have hget : (S.coeff c.note₁).get (S.coeff₁_isSome c) = cf :=
    Option.some.inj (by rw [Option.some_get, hcf])
  rw [hget]
  exact hcm.symm

/-- The second commitment decomposes over the fixed bases. -/
theorem cm₂_eq :
    c.cm₂ = (∑ i, (S.coeff c.note₂).get (S.coeff₂_isSome c) i • S.bases i)
      + c.rcm₂ • S.R := by
  have h := c.open₂
  rw [S.commit_eq] at h
  rcases Option.map_eq_some_iff.mp h with ⟨cf, hcf, hcm⟩
  have hget : (S.coeff c.note₂).get (S.coeff₂_isSome c) = cf :=
    Option.some.inj (by rw [Option.some_get, hcf])
  rw [hget]
  exact hcm.symm

end NullifierShape

/-- **The nullifier-binding reduction.** A nullifier collision computes a nontrivial
relation among the commitment bases, `K`, and `R`: the extract ±-property turns the
collision into a point equation, the openings decompose both commitments over the
fixed bases, and the coefficient conditions certify nontriviality in either sign case.
No distinct-notes premiss is needed — the opening distinctness `c.ne` suffices: in the
`+` case, distinct notes give a nonzero base-coefficient difference (`coeff_sub_ne`),
and equal notes force `rcm₁ ≠ rcm₂` (a nonzero randomness coefficient); the `−` case
needs no distinctness at all (`coeff_add_ne`). -/
def NontrivialRelation.ofNullifierCollision [DecidableEq G] (S : NullifierShape P)
    (c : NullifierCollision P) :
    NontrivialRelation (F := F) S.bases ![S.K, S.R] :=
  have hcf₁ : S.coeff c.note₁ = some ((S.coeff c.note₁).get (S.coeff₁_isSome c)) :=
    (Option.some_get _).symm
  have hcf₂ : S.coeff c.note₂ = some ((S.coeff c.note₂).get (S.coeff₂_isSome c)) :=
    (Option.some_get _).symm
  have hx : S.extract (S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ • S.K + c.cm₁)
      = S.extract (S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ • S.K + c.cm₂) := by
    rw [← S.derive_eq, ← S.derive_eq]
    exact c.eq
  if hplus : S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ • S.K + c.cm₁
      = S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ • S.K + c.cm₂ then
    NontrivialRelation.ofParts
      ((S.coeff c.note₁).get (S.coeff₁_isSome c) - (S.coeff c.note₂).get (S.coeff₂_isSome c))
      ![S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ - S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ,
        c.rcm₁ - c.rcm₂]
      (by
        by_cases hnn : c.note₁ = c.note₂
        · -- equal notes ⇒ the openings differ only in randomness
          refine Or.inr (Function.ne_iff.mpr ⟨1, ?_⟩)
          simp only [Matrix.cons_val_one, Pi.zero_apply]
          intro hβ
          exact c.ne (Prod.ext (sub_eq_zero.mp hβ) hnn)
        · exact Or.inl (S.coeff_sub_ne hcf₁ hcf₂ hnn))
      (by
        have h := hplus
        rw [S.cm₁_eq c, S.cm₂_eq c] at h
        have h0 := sub_eq_zero.mpr h
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← h0]
        simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        abel)
  else
    have hminus : S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ • S.K + c.cm₁
        = -(S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ • S.K + c.cm₂) :=
      (S.extract_pm _ _ hx).resolve_left hplus
    NontrivialRelation.ofParts
      ((S.coeff c.note₁).get (S.coeff₁_isSome c) + (S.coeff c.note₂).get (S.coeff₂_isSome c))
      ![S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ + S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ,
        c.rcm₁ + c.rcm₂]
      (Or.inl (S.coeff_add_ne hcf₁ hcf₂))
      (by
        have h := hminus
        rw [S.cm₁_eq c, S.cm₂_eq c] at h
        have h0 : (S.scalar c.nk₁ c.note₁.ρ c.note₁.ψ • S.K
            + ((∑ i, (S.coeff c.note₁).get (S.coeff₁_isSome c) i • S.bases i)
              + c.rcm₁ • S.R))
            + (S.scalar c.nk₂ c.note₂.ρ c.note₂.ψ • S.K
            + ((∑ i, (S.coeff c.note₂).get (S.coeff₂_isSome c) i • S.bases i)
              + c.rcm₂ • S.R))
            = 0 := by
          rw [h]
          abel
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← h0]
        simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel)

end Validity

end Zcash.Security.Ledger.Model
