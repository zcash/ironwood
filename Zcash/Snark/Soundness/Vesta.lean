import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed
import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Zcash.Snark.Soundness.Forking.KnowledgeError
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
turns the curve into an `Fp`-module and the abstract theorems specialize to Vesta.

## Assumptions

* **The Vesta group order.** CompElliptic's `Pasta.Vesta.card_eq` supplies
  `Nat.card VestaG = scalarFieldOrder`, from which `vestaOrder` proves that every point is annihilated
  by the scalar-field order. This does not require a caller-supplied hypothesis, but `card_eq` is a
  closed computation certified with `native_decide`; concrete Vesta endpoints inherit that pinned
  compiler-trust axiom.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely `SWPoint Vesta.curve`: the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group-order proposition: every Vesta point is `p`-torsion for
`p = scalarFieldOrder`. `vestaOrder` supplies it from CompElliptic's pinned point-count result, and
`vestaFpModule` consumes it through `Fact`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Derive the Vesta group-order proposition from CompElliptic's `Pasta.Vesta.card_eq` and the fact
that a finite group is annihilated by its cardinality. The theorem has no explicit hypothesis, but
inherits `card_eq`'s pinned `native_decide` axiom. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- Install the Vesta order proved by `vestaOrder` as the `Fact` used by the `Fp`-module instance. -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope; this file installs that fact via `vestaOrder`. Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **The concrete-to-abstract MSM bridge at Vesta.** `Msm.evalNat_eq_eval` specialised to
`SWPoint Vesta.curve`: the pinned Vesta group order supplies the `Fp`-module structure
unconditionally (via `vestaFpModule`, as for the capstones below), so the executable natural-scalar
evaluation the concrete fixtures compute (`capturedMsm.evalNat`, `(assemble ..).evalNat`) coincides
with the module-theoretic `eval` the soundness capstones consume. So the fixtures' `evalNat = 0`
checks *are* the `eval = 0` acceptance condition of the abstract verifier, not merely an analogous
computation. -/
theorem Msm.evalNat_eq_eval_vesta (urs : URS VestaG)
    (m : Msm urs.k Fp VestaG) : m.evalNat urs = m.eval urs :=
  Msm.evalNat_eq_eval urs m

/-- **Conditional soundness at Vesta.** `orchard_verifier_sound_conditional` specialised to
`SWPoint Vesta.curve`; the Vesta group order (hence the `Fp`-module structure) is supplied by the
pinned CompElliptic point-count result. Inherits the conditional status — see that docstring.
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

open Polynomial in
/-- **Soundness at Vesta over the full constraint system.** `orchard_verifier_sound_vesta_conditional`
instantiated at `circuitSatViaConstraints` instead of `circuitSatViaGates`: the extracted witness
satisfies the gate, permutation and lookup constraints together. This is where the two arguments
reach the capstone — the statement the reduction ends in now mentions them. -/
theorem orchard_verifier_sound_vesta_constraints (urs : URS VestaG)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : Polynomial Fp)
    (deg : ℕ) {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v
      (circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg) accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v
      (circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg) a → S) :
    S :=
  orchard_verifier_sound_vesta_conditional urs haccepts hextract hencodes

/-- **The deployed binding reduction over Vesta, as a computed relation.**
`NontrivialRelation.ofUnopenedFork` specialised to `SWPoint Vesta.curve`: a forked transcript
whose projection is not cleanly accepted computes a nontrivial discrete-log relation among the
Vesta generators `(g, U, W)`, which DLR hardness forbids (the contrapositive reading — see
`The reduction form` in `Soundness.Main`). -/
def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk instanceCommitment ps ch hz fs hne

/-- **Deployed opening over Vesta, given a clean fork.**
`orchard_verifier_deployed_opening_of_forked` specialised to `SWPoint Vesta.curve`: same
hypotheses as the abstract theorem; the `Fp`-module comes from the pinned Vesta point-count result.
The clean-accept hypothesis is what DLR hardness forces
(`NontrivialRelation.ofUnopenedForkVesta`); for `hcirc`'s unsatisfiable shape see the section note in
`Soundness.Main`. -/
theorem orchard_verifier_vesta_opening_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hcirc : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) circuitSat a → S) :
    S :=
  orchard_verifier_deployed_opening_of_forked urs hk vk instanceCommitment ps ch fs hclean hcirc
    hencodes

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel
(`hgood`). The `Fp`-module comes from the pinned Vesta point-count result. `hquot`/`hgood` share
`hcirc`'s unsatisfiable shape (see the section note in `Soundness.Main`). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hquot : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk instanceCommitment ps ch fixedCols
    decodeAdvice decodeInstance y gates hpoly deg x fs hclean hquot hgood hencodes

/-- The powers evaluation vector has leading entry `1` (`evalVector k x 0 = x⁰ = 1`), discharging the IPA's
`hb0` structural fact at the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- The IPA witness after folding in the value term and synthetic blinder. -/
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
/-- Legacy propositional opening from high acceptance of a bridged prover strategy. -/
noncomputable def legacy_orchard_verifier_vesta_forking_opening [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind pU pW : Fp) (s aMulti : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w
          - multiopenValue vk instanceCommitment ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (3 * urs.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval)
        (multiopenValue vk instanceCommitment ps ch - ξ * innerProduct s (evalVector urs.k xEval)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hbr : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
      (commit urs (adjustedWitness aMulti s (multiopenValue vk instanceCommitment ps ch) ξ)
        + (z * 0) • urs.u + blind • urs.w) χ := by
    intro χ
    rw [commit_adjustedWitness, hcommit]
    exact hbridge χ
  have h := legacy_deployed_forking_soundness_of_bridge urs (evalVector urs.k xEval)
    (multiopenValue vk instanceCommitment ps ch) ξ z
    blind aMulti (adjustedWitness aMulti s (multiopenValue vk instanceCommitment ps ch) ξ) s Q accepts hz
    (evalVector_zero urs.k xEval) (commit_adjustedWitness urs aMulti s (multiopenValue vk instanceCommitment ps ch) ξ)
    hbr (by rw [kerr_div_card]; exact hprob)
  rwa [hcommit] at h

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the legacy constraint conclusion to the propositional opening. -/
noncomputable def legacy_orchard_verifier_vesta_forking_constraint [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind pU pW : Fp) (s aMulti : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hξ : ξ * innerProduct s (evalVector urs.k xEval) = 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w
          - multiopenValue vk instanceCommitment ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k xEval) (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (3 * urs.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases legacy_orchard_verifier_vesta_forking_opening urs hk vk instanceCommitment ps ch xEval ξ z blind pU pW s aMulti Q
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
/-- Legacy propositional opening for one fixed proof over all round challenges. -/
noncomputable def legacy_orchard_verifier_vesta_forking_opening_deployed [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3)
        (multiopenValue vk instanceCommitment ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine legacy_orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk instanceCommitment ps ch ch.x3 ch.xi ch.z
    (pW + ch.xi * sW) pU pW s aMulti
    (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF)
    (fun χ => DeployedIpaVerifierEq gg ww uu vk instanceCommitment ps {ch with ipaRound := χ}) hz hcommit ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept]
  have hs' : commit ⟨shape.k, gg, ww, uu⟩ s = ps.ipaS - sU • uu - sW • ww := hs
  have hpU : pU = -(ch.xi * sU) := by linear_combination hU
  have hPwhole :
      (multiopenCommitment gg ww uu vk instanceCommitment ps {ch with ipaRound := χ}
          + (∑ i, ([-(multiopenValue vk instanceCommitment ps {ch with ipaRound := χ})].getD i.val 0) • gg i)
          + ({ch with ipaRound := χ} : Challenges shape.k Fp).xi • ps.ipaS)
        = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk instanceCommitment ps ch - pU • uu - pW • ww
            - multiopenValue vk instanceCommitment ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
            + (ch.z * 0) • uu + (pW + ch.xi * sW) • ww) := by
    have e1 : multiopenValue vk instanceCommitment ps {ch with ipaRound := χ} = multiopenValue vk instanceCommitment ps ch := rfl
    have e2 : multiopenCommitment gg ww uu vk instanceCommitment ps {ch with ipaRound := χ}
        = multiopenCommitment gg ww uu vk instanceCommitment ps ch := rfl
    have e3 : ({ch with ipaRound := χ} : Challenges shape.k Fp).xi = ch.xi := rfl
    rw [e1, e2, e3, sum_getD_single gg (multiopenValue vk instanceCommitment ps ch), hs', hpU]
    simp only [deployedCommitment]
    module
  rw [hPwhole]

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the legacy constraint conclusion for one fixed proof. -/
noncomputable def legacy_orchard_verifier_vesta_forking_constraint_deployed [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases legacy_orchard_verifier_vesta_forking_opening_deployed urs hk vk instanceCommitment ps ch s aMulti pU pW sU sW hz hU
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
/-- Legacy propositional opening for a prefix-respecting prover strategy. -/
noncomputable def legacy_orchard_verifier_vesta_forking_opening_adaptive [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3)
        (multiopenValue vk instanceCommitment ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine legacy_orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk instanceCommitment ps ch ch.x3 ch.xi ch.z
    (pW + ch.xi * sW) pU pW s
    aMulti P (fun χ => DeployedIpaVerifierEq gg ww uu vk instanceCommitment
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ})
    hz hcommit ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept_adaptive]
  have hs' : commit ⟨shape.k, gg, ww, uu⟩ s = ps.ipaS - sU • uu - sW • ww := hs
  have hpU : pU = -(ch.xi * sU) := by linear_combination hU
  have hPwhole : (multiopenCommitment gg ww uu vk instanceCommitment ps ch
        + (∑ i, ([-(multiopenValue vk instanceCommitment ps ch)].getD i.val 0) • gg i) + ch.xi • ps.ipaS)
      = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk instanceCommitment ps ch - pU • uu - pW • ww
          - multiopenValue vk instanceCommitment ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
          + (ch.z * 0) • uu + (pW + ch.xi * sW) • ww) := by
    rw [sum_getD_single gg (multiopenValue vk instanceCommitment ps ch), hs', hpU]
    simp only [deployedCommitment]
    module
  rw [hPwhole]

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the legacy constraint conclusion for a prefix-respecting strategy. -/
noncomputable def legacy_orchard_verifier_vesta_forking_constraint_adaptive
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases legacy_orchard_verifier_vesta_forking_opening_adaptive urs hk vk instanceCommitment ps ch s aMulti pU pW sU sW P hz hU
    hcommit hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

/-! ## Legacy propositional forking capstones

These noncomputable compatibility wrappers cover fixed and prefix-respecting proofs under oracle
reprogramming. The executable arbitrary-query path is in `Forking.Adversary.Algebraic`. -/

open scoped ENNReal in
open Classical in
/-- Legacy fixed-proof opening under oracle reprogramming. -/
noncomputable def legacy_orchard_verifier_vesta_forking_opening_rewind [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    (∃ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_orchard_verifier_vesta_forking_opening_deployed urs hk vk instanceCommitment ps (roChallenges O init ps)
    s aMulti pU pW sU sW hz hU hcommit hs ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the legacy fixed-proof constraint conclusion under reprogramming. -/
noncomputable def legacy_orchard_verifier_vesta_forking_constraint_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk instanceCommitment ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_orchard_verifier_vesta_forking_constraint_deployed urs hk vk instanceCommitment ps (roChallenges O init ps)
    s aMulti pU pW sU sW fixedCols decodeAdvice decodeInstance y gates hpoly deg x hz hU hcommit hs hξ
    hquot hgood hencodes ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open scoped ENNReal in
open Classical in
/-- Legacy prefix-respecting opening under oracle reprogramming. -/
noncomputable def legacy_orchard_verifier_vesta_forking_opening_adaptive_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    (∃ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_orchard_verifier_vesta_forking_opening_adaptive urs hk vk instanceCommitment ps (roChallenges O init ps)
    s aMulti pU pW sU sW P hz hU hcommit hs ?_
  simpa only [roChallenges_reprogramRounds, roChallenges_spliceIpa_pre] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- Add the legacy prefix-respecting constraint conclusion under reprogramming. -/
noncomputable def legacy_orchard_verifier_vesta_forking_constraint_adaptive_rewind
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0)
    (hU : pU + (roChallenges O init ps).xi * sU = 0)
    (hcommit : commit urs aMulti
      = deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk instanceCommitment ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs
        (deployedCommitment urs hk vk instanceCommitment ps (roChallenges O init ps) - pU • urs.u - pW • urs.w)
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk instanceCommitment ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (3 * shape.k : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases legacy_orchard_verifier_vesta_forking_opening_adaptive_rewind urs hk vk instanceCommitment ps O init s aMulti
    pU pW sU sW P hz hU hcommit hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel


open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed decoded constraint, per fork, batch produced by `x₄` rewinding.** The circuit is
checked on columns decoded from the opened `x₄` batch over the deployed aggregates, not through
free decode functions; the batch is derived from the fork's clean transcript and the `x₄` accept
measure (`openedX4Rewind_of_x4Prob_forked`). `hquot`/`hgood` are stated once, for the canonical
decode at the transcript's own extracted witness — the satisfiable shape (quantifying over every
opening is vacuous at a nontrivial kernel; see `Multiopen.Decode`'s scope section). -/
theorem orchard_verifier_vesta_decoded_constraint_of_forked_x4 [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {numAdvice numInstance : ℕ}
    (adviceIndex : Fin numAdvice → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (instanceIndex : Fin numInstance → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hprob4 : ((deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk instanceCommitment ps ch b)))
    (hquot : quotientCheck
        (combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs fs.openedCommitment b (multiopenValue vk instanceCommitment ps ch)
        (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex
        fixedCols y gates hpoly deg fs.pU fs.pW a cols → S) :
    S :=
  opened_constraint_of_relation_and_batch (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex fixedCols y gates hpoly deg x
    (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2
    (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)
    hquot hgood hencodes

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed decoded constraint capstone, through the opened commitment, with the
mismatch-to-DLR split.** *Either* the SNARK relation holds with the circuit checked on columns
decoded from the deployed `x₄` aggregates, *or* a nontrivial `(g, u, w)` relation exists. The
statement is the opened commitment `deployedCommitment − pU•u − pW•w`; the batch is designated
data produced upstream at the extracted witness, its opening derived; `hprob` spends the
round-forking floor and enforces the witness tie — the produced opening agrees with the designated
one, or the two collide and the relation is computed.

Named assumptions: `hU`/`hcommit`/`hs` declare the witness representations; `hξ` kills the
synthetic-blinder value shift; `pbatch`/`hξcur` designate the batch; `hquot`/`hgood` state the gate
check once, for the canonical decode; `hencodes` consumes the decoded SNARK relation. -/
theorem orchard_verifier_vesta_forking_constraint_deployed_x4 [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (s aMulti : Fin (2 ^ urs.k) → Fp) (pU pW sU sW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceIndex : Fin numAdvice → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (instanceIndex : Fin numInstance → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0)
    (hU : pU + ch.xi * sU = 0)
    (hcommit : commit urs aMulti = deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (hs : commit urs s = ps.ipaS - sU • urs.u - sW • urs.w)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hquot : quotientCheck
        (combineGates fixedCols
          (selectedPolys (openedDecodedCols pbatch) adviceIndex)
          (selectedPolys (openedDecodedCols pbatch) instanceIndex)
          y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
          (selectedPolys (openedDecodedCols pbatch) adviceIndex)
          (selectedPolys (openedDecodedCols pbatch) instanceIndex)
          y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
          (selectedPolys (openedDecodedCols pbatch) adviceIndex)
          (selectedPolys (openedDecodedCols pbatch) instanceIndex)
          y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
        (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex
        fixedCols y gates hpoly deg pU pW a cols → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps
              {ch with ipaRound := χ}))) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hrel₀ := pbatch.ipaRelation_of_x4Current hξcur
  rcases legacy_orchard_verifier_vesta_forking_opening_deployed urs hk vk instanceCommitment ps ch s aMulti pU pW
      sU sW hz hU hcommit hs (by rw [← kerr_div_card]; exact hprob) with hopen | hrel
  · rw [hξ, sub_zero] at hopen
    obtain ⟨a, hrel'⟩ := hopen
    by_cases hae : a = a₀
    · exact Or.inl (opened_constraint_of_relation_and_batch (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex fixedCols y gates hpoly deg x hrel₀
        pbatch hquot hgood hencodes)
    · exact Or.inr (hasNontrivialRelation_of_two_openings urs hae (hrel'.1.trans hrel₀.1.symm))
  · exact Or.inr (HasNontrivialRelation.of_nontrivialRelation hrel)


open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed member-column constraint capstone: the gate check on the real circuit columns.**
*Either* the SNARK relation holds with the circuit checked on the decoded *member* columns — the
actual queried column commitments' openings — *or* a nontrivial `(g, u, w)` relation exists. The
member decodes are produced per point set by spending the `x₁` accept measure
(`openedMemberDecode_of_x1Prob`); the honest opening is the designated batch itself. `hquot`/`hgood`
state the gate check once, on the produced member polynomials; deriving them from the verifier's
accepted `assemble.eval = 0` is the remaining constraint-side work. Measures carry the usual
random-oracle uniformity axiom. -/
theorem orchard_verifier_vesta_member_constraint_deployed_x4 [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  -- The honest opening is the *given* `pbatch` (`ipaRelation_of_x4Current`); the member constraint
  -- `S` follows from it and the gate hypotheses directly. There is no free augmented `(u, w)`
  -- decomposition to assume here (`hcommit`/`hs`/`hU`/`hξ` and the second `x`-round fork are gone):
  -- the vanish-or-DLR dichotomy on those components is discharged *upstream*, where `pbatch` itself
  -- is produced from acceptance (`openedX4Rewind_of_x4Prob` and the `x₄`/`x₁` forks) — re-forking
  -- them here only re-introduced the free components the audit flagged. The `HasNontrivialRelation`
  -- disjunct is retained so the composition can surface that upstream branch unchanged.
  Or.inl (member_constraint_of_relation_and_batch urs hk vk instanceCommitment ps ch adviceSet hadviceSet
    adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg x
    (pbatch.ipaRelation_of_x4Current hξcur) pbatch
    (fun i hi => openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch i hi (hlen i hi)
      (hprob1 i hi) hacc0)
    hquot hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes)

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Terminal deployed member capstone: `hquot` derived, not assumed.** From the per-column
claimed evaluations and the gate-fold identity `hfold`, `quotientCheck_of_claimed` produces
`hquot`, threaded into the member capstone — the multiopen value check closed into the gate check.
Once the claimed evaluations are derived, the residual trust surface is the gate structure
`gates = subProofExpressions`: the equivalence fingerprint, on the same footing as the
RO-uniformity axiom. -/
theorem orchard_verifier_vesta_member_constraint_deployed_terminal [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp)
    (hfixed : ∀ i, (fixedCols i).eval x = fixedClaimed i)
    (hadvice : ∀ i, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))) i).eval x = adviceClaimed i)
    (hinstance : ∀ i, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))) i).eval x = instanceClaimed i)
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval x * (x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hquot := quotientCheck_of_claimed fixedCols
    (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
    (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))))
    y gates hpoly deg x fixedClaimed adviceClaimed instanceClaimed hfixed hadvice hinstance hfold
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk instanceCommitment ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg x pbatch
    hξcur hlen hprob1 hacc0 hquot hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Derived deployed member capstone: the claimed evaluations produced from the floors.** The
gate check runs at `ch.x` on the decoded member columns, whose claimed evaluations are *derived*:
each in-range layout entry is a deployed opening query, its rotated point a point of the member's
set, and the member node binding pins the decoded column's value there
(`deployed_member_node_binding_at_point`), on pain of a computed `(g, U, W)` relation. `hfold` is
stated at exactly those deployed claimed evaluations (the expression-fold fingerprint surface), and
`hgood`'s production surface is `hgood_of_xProb`. The residual premises are the forking floors,
sample avoidance, and the layout/eval range facts — no per-column value hypothesis remains. -/
theorem orchard_verifier_vesta_member_constraint_derived [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    {ξ₀ : Fp} (hξ₀p : OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch ξ₀)
    (hprob1p : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch)))
    (hx2 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp), ∃ (b₂ : Fin (2 ^ urs.k) → Fp) (ζ₀ : Fp),
      OpenedX2Accept urs hk vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) b₂ ζ₀ ∧
      ((deployedX4PairCount vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX2Accept urs hk vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) b₂)))
    (hprob3 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp) (r₂ : X2Run shape VestaG) (ζv : Fp),
      ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (fun χv => OpenedX3Accept urs hk vk instanceCommitment (r₂.spliced (r₁.spliced ps))
              (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv)))
    (hprob4 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp) (r₂ : X2Run shape VestaG) (ζv χv : Fp)
        (r₃ : X3Run shape VestaG),
      (deployedX4PairCount vk instanceCommitment (r₃.spliced (r₂.spliced (r₁.spliced ps)))
          (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk instanceCommitment (r₃.spliced (r₂.spliced (r₁.spliced ps)))
              (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv)
              (evalVector urs.k χv))))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval (fun n => (fixedCols n).eval ch.x)
          (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval ch.x * (ch.x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  -- derive `hadvice`: the rotated advice feed's value at `ch.x` is the deployed claimed eval
  have hadvice : ∀ n, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
          (adviceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout n := by
    intro n
    by_cases h : n < numAdvice
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := advice_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hadvLen ⟨n, h⟩).1 (hadvLen ⟨n, h⟩).2
      have hltm : ((adviceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (adviceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).getD ((adviceMem ⟨n, h⟩ : ℕ))
          CommitmentId.vanishingH = q.commId := (hadviceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point urs hk vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)
        (hadviceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet ⟨n, h⟩)
          (hadviceSet ⟨n, h⟩) (hlen _ (hadviceSet ⟨n, h⟩)) (hprob1 _ (hadviceSet ⟨n, h⟩)) hacc0)
        hξ₀p (hprob1p _ (hadviceSet ⟨n, h⟩)) hx2 hprob3 hprob4 hpt
        (adviceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- derive `hinstance` symmetrically
  have hinstance : ∀ n, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout n := by
    intro n
    by_cases h : n < numInstance
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := instance_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hinstLen ⟨n, h⟩).1 (hinstLen ⟨n, h⟩).2
      have hltm : ((instanceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (instanceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).getD
          ((instanceMem ⟨n, h⟩ : ℕ)) CommitmentId.vanishingH = q.commId :=
        (hinstanceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point urs hk vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)
        (hinstanceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet ⟨n, h⟩)
          (hinstanceSet ⟨n, h⟩) (hlen _ (hinstanceSet ⟨n, h⟩)) (hprob1 _ (hinstanceSet ⟨n, h⟩))
          hacc0)
        hξ₀p (hprob1p _ (hinstanceSet ⟨n, h⟩)) hx2 hprob3 hprob4 hpt
        (instanceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- the gate check at the deployed opening challenge, from the derived claimed evaluations
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk instanceCommitment ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg ch.x
    pbatch hξcur hlen hprob1 hacc0
    (quotientCheck_of_claimed fixedCols _ _ y gates hpoly deg ch.x
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout)
      (fun _ => rfl) hadvice hinstance hfold)
    hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

end Zcash.Snark
