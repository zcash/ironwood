import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Soundness.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the end-to-end theorems apply verbatim.

## Assumptions

* **The Vesta group order — no assumption.** CompElliptic's `Pasta.Vesta.card_eq` proves
  `Nat.card VestaG = scalarFieldOrder` (an elementary point-count bound stands in for Hasse, which
  Mathlib lacks — see CompElliptic's `CurveOrder`), whence every point is annihilated by the group
  order (`vestaOrder`).
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely `SWPoint Vesta.curve`: the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition: every Vesta point is `p`-torsion, i.e. the group order
divides `p = scalarFieldOrder`. Proven unconditionally (`vestaOrder`); carried as a `Fact` so
`vestaFpModule` can consume it. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- The Vesta group order, unconditionally: CompElliptic's `Pasta.Vesta.card_eq` gives
`Nat.card VestaG = scalarFieldOrder` with no assumption, and a finite group is annihilated by its
order. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- The Vesta order `Fact` — hence the `Fp`-module — is supplied unconditionally, from `vestaOrder`
(CompElliptic pins the order with no assumption). -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope (now unconditionally, via `vestaOrder`). Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **Conditional soundness at Vesta.** `orchard_verifier_sound_conditional` specialised to
`SWPoint Vesta.curve`; the Vesta group order (hence the `Fp`-module structure) is pinned
unconditionally. Inherits the conditional status — see that docstring.
The deployed Vesta capstones are `orchard_verifier_vesta_opening_of_forked`/`_constraint_of_forked`
below, with `NontrivialRelation.ofUnopenedForkVesta` the computed break. -/
theorem orchard_verifier_sound_vesta_conditional
    (urs : URS VestaG)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional urs haccepts hextract hencodes

/-- **The deployed binding reduction over Vesta, as a computed relation.**
`NontrivialRelation.ofUnopenedFork` specialised to `SWPoint Vesta.curve`: a forked transcript
whose projection is not cleanly accepted computes a nontrivial discrete-log relation among the
Vesta generators `(g, U, W)`, which DLR hardness forbids (the contrapositive reading — see
`The reduction form` in `Soundness.Main`). -/
def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk ps ch hz fs hne

/-- **Deployed opening over Vesta, given a clean fork.**
`orchard_verifier_deployed_opening_of_forked` specialised to `SWPoint Vesta.curve`: same
hypotheses as the abstract theorem (the Vesta order is unconditional). The opening witness `a` and
`IpaRelation` certificate `hrel` are supplied by the caller (derived from the clean accept via
`ipaRelation_of_acceptV`). -/
theorem orchard_verifier_vesta_opening_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (a : Fin (2 ^ urs.k) → Fp) {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hrel : IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a)
    (hcirc : circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S :=
  orchard_verifier_deployed_opening_of_forked urs hk vk ps ch a fs hrel hcirc hencodes

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` at the challenge `x`, lifted
to the polynomial identity by Schwartz–Zippel (`hgood`). The `hquot`/`hgood` checks now constrain
the single extracted witness `a`. Same hypotheses as the abstract theorem (the Vesta order is
unconditional). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (a : Fin (2 ^ urs.k) → Fp)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hrel : IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a)
    (hquot : quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk ps ch fixedCols decodeAdvice
    decodeInstance y gates hpoly deg x a fs hrel hquot hgood hencodes

/-- The powers evaluation vector has leading entry `1` (`evalVector k x 0 = x⁰ = 1`), discharging the IPA's
`hb0` structural fact at the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- halo2's adjusted IPA witness: `aMulti` with its `g₀`-coefficient shifted by the claimed value `v` and the
synthetic blinder `ξ·s` folded in, so `commit` sends it to the adjusted commitment `⟨aMulti,G⟩ − [v]g₀ + [ξ]S`.
A *definition* (not a posited `aDep` with a relation `hP`), so `hP` holds by `commit`'s linearity. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) : Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment — `hP` holds by linearity, not by assumption. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G] (urs : URS G)
    (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) = commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp, commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'; simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

open scoped ENNReal in
/-- A nonzero blinding shift vanishes for at most a `1 / |Fp|` fraction of uniform `ξ` challenges. -/
theorem blinder_value_recovery_badSet {k : ℕ} (s : Fin (2 ^ k) → Fp) (xEval : Fp)
    (hδ : innerProduct s (evalVector k xEval) ≠ 0) :
    uniformChallenge.toOuterMeasure
        (Finset.univ.filter (fun ξ : Fp => ξ * innerProduct s (evalVector k xEval) = 0))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) :=
  blinder_shift_badSet_measure (innerProduct s (evalVector k xEval)) 0 hδ

open scoped ENNReal in
open Classical in
/-- Open the deployed Orchard commitment over Vesta using the forking result.

`aMulti` opens the commitment after removing its declared `U` and `W` components. Real commitments
are blinded, so this adjusted point—not the raw commitment—has the `g`-only representation supplied
by the algebraic prover. The returned value is `multiopenValue − ξ·⟨s,b⟩`; honest blinding makes the
second term zero.

`hbridge` connects the accept event to the prover strategy, and `hprob` must beat the knowledge
error. This definition remains noncomputable because it selects an existential fork certificate.
`deployed_forking_relation` is the executable kernel for an explicit certificate. -/
noncomputable def orchard_verifier_vesta_forking_opening [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind pU pW : Fp) (s aMulti : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w
          - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval)
        (multiopenValue vk ps ch - ξ * innerProduct s (evalVector urs.k xEval)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hbr : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
      (commit urs (adjustedWitness aMulti s (multiopenValue vk ps ch) ξ)
        + (z * 0) • urs.u + blind • urs.w) χ := by
    intro χ
    rw [commit_adjustedWitness, hcommit]
    exact hbridge χ
  have h := deployed_forking_soundness_of_bridge urs (evalVector urs.k xEval) (multiopenValue vk ps ch) ξ z
    blind aMulti (adjustedWitness aMulti s (multiopenValue vk ps ch) ξ) s Q accepts hz
    (evalVector_zero urs.k xEval) (commit_adjustedWitness urs aMulti s (multiopenValue vk ps ch) ξ)
    hbr hprob
  rwa [hcommit] at h

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the constraint conclusion to `orchard_verifier_vesta_forking_opening`.

`hξ` restores the claimed value by proving the blinding shift is zero. The `hquot` and `hgood`
hypotheses retain the all-openings caveat from the legacy constraint theorem. -/
noncomputable def orchard_verifier_vesta_forking_constraint [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind pU pW : Fp) (s aMulti : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hξ : ξ * innerProduct s (evalVector urs.k xEval) = 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w
          - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening urs hk vk ps ch xEval ξ z blind pU pW s aMulti Q
      accepts hz hcommit hbridge hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

/-- The single-entry value term in the adjusted commitment is `-v • g 0`. -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G] (gg : Fin (2 ^ k) → G)
    (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped ENNReal in
open Classical in
/-- Open the deployed Orchard commitment for a fixed proof string.

The accept event is halo2's verifier equation, and `deployedVerifierEq_iff_flatAccept` proves its
bridge to the constant strategy. The multiopen and `S` witnesses open their points after removing
declared `U` and `W` components; `hU` cancels the remaining `U` component.

`hprob` measures this one proof over all round challenges, not the Fiat–Shamir attack event. It gives
the static statement that acceptance above the knowledge-error threshold yields an opening. Use the
adaptive variants for a prefix-respecting strategy and reprogrammed-oracle runs. -/
noncomputable def orchard_verifier_vesta_forking_opening_deployed [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch ch.x3 ch.xi ch.z
    (pW + ch.xi * sW) pU pW s aMulti
    (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF)
    (fun χ => DeployedIpaVerifierEq gg ww uu vk ps {ch with ipaRound := χ}) hz hcommit ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept]
  have hs' : commit ⟨shape.k, gg, ww, uu⟩ s = ps.ipaS - sU • uu - sW • ww := hs
  have hpU : pU = -(ch.xi * sU) := by linear_combination hU
  have hPwhole :
      (multiopenCommitment gg ww uu vk ps {ch with ipaRound := χ}
          + (∑ i, ([-(multiopenValue vk ps {ch with ipaRound := χ})].getD i.val 0) • gg i)
          + ({ch with ipaRound := χ} : Challenges shape.k Fp).xi • ps.ipaS)
        = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch - pU • uu - pW • ww
            - multiopenValue vk ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
            + (ch.z * 0) • uu + (pW + ch.xi * sW) • ww) := by
    have e1 : multiopenValue vk ps {ch with ipaRound := χ} = multiopenValue vk ps ch := rfl
    have e2 : multiopenCommitment gg ww uu vk ps {ch with ipaRound := χ}
        = multiopenCommitment gg ww uu vk ps ch := rfl
    have e3 : ({ch with ipaRound := χ} : Challenges shape.k Fp).xi = ch.xi := rfl
    rw [e1, e2, e3, sum_getD_single gg (multiopenValue vk ps ch), hs', hpU]
    simp only [deployedCommitment]
    module
  rw [hPwhole]

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the constraint conclusion to `orchard_verifier_vesta_forking_opening_deployed`.

`hξ` restores the claimed value by proving the blinding shift is zero. `hprob` still measures one
fixed proof, not the Fiat–Shamir attack event. The `hquot` and `hgood` hypotheses retain the
all-openings caveat described by `orchard_verifier_deployed_constraint_of_forked`. -/
noncomputable def orchard_verifier_vesta_forking_constraint_deployed [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_deployed urs hk vk ps ch s aMulti pU pW sU sW hz hU
    hcommit hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

open scoped ENNReal in
open Classical in
/-- Open the deployed Orchard commitment for a prefix-respecting prover strategy.

The verifier runs on the proof assembled for each challenge path, and
`deployedVerifierEq_iff_flatAccept_adaptive` proves the bridge to `P`. Thus `hprob` measures an
adaptive strategy rather than one fixed proof. Connecting a real random-oracle adversary to this
strategy, including query loss, remains outside this theorem. -/
noncomputable def orchard_verifier_vesta_forking_opening_adaptive [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch ch.x3 ch.xi ch.z
    (pW + ch.xi * sW) pU pW s
    aMulti P (fun χ => DeployedIpaVerifierEq gg ww uu vk
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ})
    hz hcommit ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept_adaptive]
  have hs' : commit ⟨shape.k, gg, ww, uu⟩ s = ps.ipaS - sU • uu - sW • ww := hs
  have hpU : pU = -(ch.xi * sU) := by linear_combination hU
  have hPwhole : (multiopenCommitment gg ww uu vk ps ch
        + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • gg i) + ch.xi • ps.ipaS)
      = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch - pU • uu - pW • ww
          - multiopenValue vk ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
          + (ch.z * 0) • uu + (pW + ch.xi * sW) • ww) := by
    rw [sum_getD_single gg (multiopenValue vk ps ch), hs', hpU]
    simp only [deployedCommitment]
    module
  rw [hPwhole]

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the constraint conclusion to `orchard_verifier_vesta_forking_opening_adaptive`.

`hξ` restores the claimed value. Connecting the Fiat–Shamir adversary and its query loss remains
outside this theorem. The `hquot` and `hgood` hypotheses retain the all-openings caveat. -/
noncomputable def orchard_verifier_vesta_forking_constraint_adaptive
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_adaptive urs hk vk ps ch s aMulti pU pW sU sW P hz hU
    hcommit hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

/-! ## Forking capstones

The endpoints differ in how much of the prover and rewinding model they include:

* **Constant** — the `_deployed` pair uses one fixed proof. Its probability is over all round
  challenges, not the Fiat–Shamir attack event.
* **Staged** — the `_adaptive` pair uses a prefix-respecting strategy. Connecting a rewound
  random-oracle adversary to that strategy, including query loss, remains open.
* **Constant, rewound** — the `_rewind` pair states the constant event using reprogrammed-oracle runs.
* **Staged, rewound** — the `_adaptive_rewind` pair combines a staged strategy with reprogrammed runs.
* **Abstract** — the base pair receives the prover-to-acceptance bridge as `hbridge`.

The older `_of_forked` pair remains checked but is no longer the main endpoint.

Every endpoint opens commitments after removing their declared `U` and `W` components. Real halo2
commitments are blinded, so only these adjusted points have the required `g` representations. Honest
commitments have no `U` component; their `W` components are the commitment blinds. `hU` cancels the
total declared `U` component of the opened point.

These wrappers remain `noncomputable` because the fork certificate is existential. Executable code
must call `deployed_forking_relation` with an explicit certificate and opening data. -/

open scoped ENNReal in
open Classical in
/-- Apply the fixed-proof opening theorem to reprogrammed-oracle runs.

`roChallenges_reprogramRounds` identifies each run with replacement of the IPA round challenges.
This remains a fixed-proof acceptance statement; the adaptive endpoints model the attack event. -/
noncomputable def orchard_verifier_vesta_forking_opening_rewind [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    (∃ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_opening_deployed urs hk vk ps (roChallenges O init ps)
    s aMulti pU pW sU sW hz hU hcommit hs ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the constraint conclusion to `orchard_verifier_vesta_forking_opening_rewind`.

The accept event uses reprogrammed-oracle runs. The `hquot` and `hgood` all-openings caveat and the
fixed-proof scope are unchanged. -/
noncomputable def orchard_verifier_vesta_forking_constraint_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_constraint_deployed urs hk vk ps (roChallenges O init ps)
    s aMulti pU pW sU sW fixedCols decodeAdvice decodeInstance y gates hpoly deg x hz hU hcommit hs hξ
    hquot hgood hencodes ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open scoped ENNReal in
open Classical in
/-- Apply the round-adaptive opening theorem to reprogrammed-oracle runs on each spliced proof.

`roChallenges_reprogramRounds` supplies the path's round challenges, while
`roChallenges_spliceIpa_pre` shows that splicing leaves the pre-IPA challenges unchanged. -/
noncomputable def orchard_verifier_vesta_forking_opening_adaptive_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    (∃ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_opening_adaptive urs hk vk ps (roChallenges O init ps)
    s aMulti pU pW sU sW P hz hU hcommit hs ?_
  simpa only [roChallenges_reprogramRounds, roChallenges_spliceIpa_pre] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the constraint conclusion to `orchard_verifier_vesta_forking_opening_adaptive_rewind`.

The accept event uses reprogrammed-oracle runs on each spliced proof. The `hquot` and `hgood`
all-openings caveat is unchanged. -/
noncomputable def orchard_verifier_vesta_forking_constraint_adaptive_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs
        (deployedCommitment urs hk vk ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_adaptive_rewind urs hk vk ps O init s aMulti
    pU pW sU sW P hz hU hcommit hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

end Zcash.Snark
