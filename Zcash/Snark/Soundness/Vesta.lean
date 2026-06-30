import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking
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

* **Hasse bound** (`Fact (HasseBound Vesta.curve)`) — the only remaining curve assumption. The Vesta
  group order is *derived* from it, not assumed (`vestaOrder_of_hasse`): given the Hasse bound,
  CompElliptic's `Pasta.Vesta.card_eq` proves `Nat.card VestaG = scalarFieldOrder`, whence every point
  is annihilated by the group order. Carried as a `Fact`, like the field modulus
  `Fact (Nat.Prime scalarFieldOrder)`; supplied as a hypothesis, never globally, so the development
  stays axiom-free. Mathlib lacks Hasse's theorem, so it is the irreducible gap (see CompElliptic's
  `CurveOrder`).
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition: every Vesta point is `p`-torsion, i.e. the group order
divides `p = scalarFieldOrder`. Derived from the Hasse bound by `vestaOrder_of_hasse` (via
CompElliptic's `Pasta.Vesta.card_eq`), not assumed; carried as a `Fact` so `vestaFpModule` can
consume it, with the supplied `Fact` being `Fact (HasseBound Vesta.curve)`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- The Vesta group order, derived from the Hasse bound rather than assumed: given the Hasse bound,
CompElliptic's `Pasta.Vesta.card_eq` gives `Nat.card VestaG = scalarFieldOrder`, and a finite group is
annihilated by its order. -/
theorem vestaOrder_of_hasse (hHasse : HasseBound Vesta.curve) : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq hHasse
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- With the Hasse bound in scope, the Vesta order `Fact` — hence the `Fp`-module — is supplied
automatically. Conditional like `vestaFpModule`: it fires only when the Hasse `Fact` is a hypothesis,
never globally, so the development stays axiom-free. -/
instance factVestaOrder_of_hasse [Fact (HasseBound Vesta.curve)] : Fact VestaOrder :=
  ⟨vestaOrder_of_hasse Fact.out⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module: `AddCommGroup.zmodModule`
on the `p`-torsion. A conditional instance — it fires only when the order `Fact` is in scope, so it adds
no axiom (the `Fact` is supplied as a hypothesis, never globally). -/
noncomputable instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- The conditional soundness composition over the concrete Vesta curve:
`orchard_verifier_sound_conditional` with the abstract `Fp`-module specialised to `SWPoint Vesta.curve`,
the abstract-curve assumption replaced by `Fact (HasseBound Vesta.curve)` (the order follows). It
inherits the conditional status of `orchard_verifier_sound_conditional` (assumed extraction + constraint
identity; `accepts` not tied to the fingerprint); see that docstring. The deployed Vesta capstones are
`orchard_verifier_vesta_opening_reduction`/`_constraint` below. -/
theorem orchard_verifier_sound_vesta_conditional [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (hbind : CommitmentBinding (F := Fp) urs)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional urs hbind haccepts hextract hencodes

/-- The deployed Orchard verifier opening over Vesta, as a binding **reduction**, with `P`/`v` pinned to the
proof. `orchard_verifier_deployed_opening_reduction` specialised to `SWPoint Vesta.curve`: from an accepting
fingerprint — proven to entail the explicit `DeployedIpaVerifierEq` form (`deployedAccepts_verifierEq`) — and
the forking bridge (`hFS`), either the SNARK relation holds for the pinned
`deployedCommitment`/`multiopenValue`, or the augmented Vesta generators `(g, U, W)` admit a nontrivial
discrete-log relation. The `U`/`W` separation is derived (`deployed_to_acceptV`), not bundled. Caveat: a
relation always *exists* in Vesta's prime-order group, so this `∨ HasNontrivialRelation` statement is
propositionally `True` (vacuous at the curve); the force is the out-of-Lean DLR/AGM layer — no feasible
adversary can *find* the relation. Named assumptions:
the residual bridge (`hFS`, issue #11), `z ≠ 0`, the circuit side (`hcirc`), the Hasse bound (`Fact (HasseBound Vesta.curve)`), and VK-correctness
(`hencodes`). `hcirc` quantifies over every mathematical opening of the pinned `(P, b, v)` and is
unsatisfiable at Vesta for any `circuitSat` that genuinely reads the witness — see the caveat on
`orchard_verifier_deployed_opening_reduction`, and issue #18 for the restatement over the extracted
witness. -/
theorem orchard_verifier_vesta_opening_reduction [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hcirc : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  orchard_verifier_deployed_opening_reduction urs hk vk ps ch hz haccepts hFS hcirc hencodes

open Polynomial in
/-- The deployed Orchard verifier opening and constraint over Vesta, as a binding **reduction**, with
`P`/`v` pinned to the proof. `orchard_verifier_deployed_constraint_reduction` specialised to
`SWPoint Vesta.curve`: `IpaRelation` (for the pinned `deployedCommitment`/`multiopenValue`) from the peeled
deployed tree reached through the *proven* `deployedAccepts_verifierEq`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel (`hgood`). The
conclusion is `S ∨ HasNontrivialRelation g U W` — a relation always *exists* in Vesta's prime-order group,
so this statement is propositionally `True` (vacuous at the curve); the force is the out-of-Lean DLR/AGM
layer (no feasible adversary can *find* one), not the proposition. Named
assumptions: the residual bridge (`hFS`, issue #11), `z ≠ 0`, the gate check (`hquot`), the SZ good challenge
(`hgood`), the Hasse bound (`Fact (HasseBound Vesta.curve)`), and VK-correctness (`hencodes`).
`hquot`/`hgood` quantify over every mathematical opening of the pinned `(P, b, v)` and are unsatisfiable
at Vesta for any decode that genuinely reads columns out of the witness — see the caveat on
`orchard_verifier_deployed_constraint_reduction`, and issue #18 for the restatement over the extracted
witness. -/
theorem orchard_verifier_vesta_constraint_reduction [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp) (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  orchard_verifier_deployed_constraint_reduction urs hk vk ps ch fixedCols decodeAdvice decodeInstance y gates
    hpoly deg x hz haccepts hFS hquot hgood hencodes

/-- The powers evaluation vector's leading entry is `1` (`b 0 = x⁰ = 1`), discharging the IPA's `hb0`
structural fact for the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- halo2's adjusted IPA witness: `aMulti` with its `g₀`-coefficient shifted by the claimed value and the
synthetic blinder `ξ·s` folded in, so its commitment is the adjusted commitment `⟨aMulti,G⟩ − [v]g₀ + [ξ]S`.
Making it a *definition* (rather than positing an `aDep` with a relation `hP`) discharges `hP` by the linearity
of `commit`. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) : Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment — `hP` holds by linearity, not by assumption. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G] (urs : URS G)
    (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) = commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp, commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'; simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

/-- **The deployed commitment lies in the `g`-span (discharging `hcommit`).** At Vesta's prime order a nonzero
generator `urs.g 0` generates the whole group: `c ↦ c • g 0` is injective over the field `Fp` (a nonzero
scalar is invertible) and `Fp` and `VestaG` have equal cardinality (`scalarFieldOrder`), so it is surjective —
every group element, in particular `deployedCommitment`, is the `g`-commitment of some witness. So the
`hcommit` tie is always satisfiable: it is the prime-order/`g`-span fact, the witness being the discrete log of
`P` base `g 0` (existing but not feasibly constructible — the same DLR-side status as the
`∨ HasNontrivialRelation` disjunct). -/
theorem commit_surjective [Fact (HasseBound Vesta.curve)] (urs : URS VestaG) (hg0 : urs.g 0 ≠ 0)
    (P : VestaG) : ∃ aMulti : Fin (2 ^ urs.k) → Fp, commit urs aMulti = P := by
  have hinj : Function.Injective (fun c : Fp => c • urs.g 0) := by
    intro c c' h
    have h' : c • urs.g 0 = c' • urs.g 0 := h
    rcases eq_or_ne c c' with hcc | hcc
    · exact hcc
    · refine absurd ?_ hg0
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
      have h0 : (c - c') • urs.g 0 = 0 := by rw [sub_smul, h', sub_self]
      rw [← one_smul Fp (urs.g 0), ← inv_mul_cancel₀ hd, mul_smul, h0, smul_zero]
  haveI : Fintype VestaG := Fintype.ofFinite VestaG
  have hcardeq : Fintype.card Fp = Fintype.card VestaG := by
    rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq Fact.out]
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcardeq⟩).surjective P
  exact ⟨Pi.single 0 c, by rw [commit_single]; exact hc⟩

open scoped ENNReal in
/-- **The ξ-randomization budget behind the constraint capstone's value recovery.** A malicious blinder with
`⟨s,b⟩ = δ ≠ 0` satisfies the value-recovery premise `ξ·⟨s,b⟩ = 0` — which pins the opened value back to the
claimed `multiopenValue` — only at `ξ = 0`, a set of uniform random-oracle measure `≤ 1/p`. So the `hξ`
hypothesis of `orchard_verifier_vesta_forking_constraint` is, for a nonzero blinder, satisfiable only on a
`1/p`-measure set of post-`S` challenges: the Schwartz–Zippel `ξ`-exclusion (`blinder_shift_badSet_measure`)
made explicit for the constraint side. -/
theorem blinder_value_recovery_badSet {k : ℕ} (s : Fin (2 ^ k) → Fp) (xEval : Fp)
    (hδ : innerProduct s (evalVector k xEval) ≠ 0) :
    uniformChallenge.toOuterMeasure
        (Finset.univ.filter (fun ξ : Fp => ξ * innerProduct s (evalVector k xEval) = 0))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) :=
  blinder_shift_badSet_measure (innerProduct s (evalVector k xEval)) 0 hδ

open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening over Vesta, via the forking refinements (no `FiatShamirTree`), with the
structural facts discharged.** Routes the forking development to the concrete deployed instance. The multiopen
evaluation vector is the concrete powers vector `b = evalVector urs.k xEval` (so `b 0 = 1` is *proved* by
`evalVector_zero`, not assumed); the multiopen witness `aMulti` is *recovered* from the `g`-span
(`commit_surjective`, from the nonzero generator `hg0`), so the `g`-span tie `hcommit` is **discharged** rather
than assumed; and the adjusted witness is *constructed*, so halo2's adjusted-commitment relation `hP` holds by
linearity (`commit_adjustedWitness`). The synthetic blinder is stripped *unconditionally*: the conclusion is
the **true** opened value `multiopenValue − ξ·⟨s,b⟩`, with no `⟨s,b⟩ = 0` assumed — covering a malicious blinder
(the honest case `⟨s,b⟩ = 0` recovers the claimed value). What remains is the explicit prover-as-oracle bridge
`hbridge` (the irreducible random-oracle floor), plus the antecedents `z ≠ 0`, the nonzero generator `hg0`, and
the accept probability `hprob` beating the knowledge error `kerr/Nᵏ`. The `∨ HasNontrivialRelation` caveat is
unchanged — vacuous at Vesta's prime order, the force in the out-of-Lean DLR/AGM layer. -/
theorem orchard_verifier_vesta_forking_opening [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind : Fp) (s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0) (hg0 : urs.g 0 ≠ 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch - ξ * innerProduct s (evalVector urs.k xEval)) a)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨aMulti, hcommit⟩ := commit_surjective urs hg0 (deployedCommitment urs hk vk ps ch)
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
/-- **The deployed Orchard opening *and constraint* over Vesta, via the forking refinements (no
`FiatShamirTree`), with the structural facts discharged.** The constraint-side companion of
`orchard_verifier_vesta_forking_opening`: same concrete instance (`b = evalVector urs.k xEval`, so `b 0 = 1` is
*proved*; `aMulti` recovered from the `g`-span so `hcommit` is discharged; the adjusted witness *constructed*
so `hP` holds by linearity) and the same gate seam as `orchard_verifier_vesta_constraint_reduction`
(`hquot`/`hgood` → `circuitSatViaGates`, `hencodes`). Unlike the opening, the circuit is checked at the
*claimed* value `multiopenValue`, so the minimal value-recovery hypothesis `hξ : ξ·⟨s,b⟩ = 0` is retained — it
pins the true opened value `multiopenValue − ξ·⟨s,b⟩` from the forking opening back to `multiopenValue`. `hξ`
generalises honest blinding (`⟨s,b⟩ = 0`); for a *malicious* blinder (`⟨s,b⟩ ≠ 0`) it holds only on a
`1/p`-measure set of post-`S` challenges `ξ` (`blinder_value_recovery_badSet`, the `ξ`-randomization budget).
The deployed-curve residual is the explicit prover-as-oracle bridge `hbridge` (and the nonzero generator
`hg0`); both the opening and the constraint side now route through it with `b 0 = 1`, `hcommit`, and `hP`
discharged. The original `FiatShamirTree` reductions
(`orchard_verifier_vesta_opening_reduction`/`_constraint`) remain as the coarser legacy endpoints. The
`∨ HasNontrivialRelation` caveat is unchanged — vacuous at Vesta's prime order, the force in the out-of-Lean
DLR/AGM layer. -/
theorem orchard_verifier_vesta_forking_constraint [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind : Fp) (s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0) (hg0 : urs.g 0 ≠ 0)
    (hξ : ξ * innerProduct s (evalVector urs.k xEval) = 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening urs hk vk ps ch xEval ξ z blind s Q accepts
      hz hg0 hbridge hprob with ⟨a, hrel'⟩ | hrel
  · rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact Or.inl (hencodes a ⟨hrel', hsat⟩)
  · exact Or.inr hrel

/-! ## The forking capstones as terminal results

`orchard_verifier_vesta_forking_opening` and `orchard_verifier_vesta_forking_constraint` are **terminal** —
the soundness deliverables of this development — so nothing consumes them upward; the opening is wired in only
here, by the constraint capstone, which calls it. Like the legacy
`orchard_verifier_vesta_opening_reduction`/`_constraint`, they are compiled and checked as part of the library
but are not building blocks for a higher theorem. This is by design: they are the top-level statements a reader
takes as the deployed-curve soundness results. -/

end Zcash.Snark
