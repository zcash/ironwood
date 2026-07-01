import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.RandomOracle
import Zcash.Snark.Soundness.ForkingExtractor

/-!
# The deployed verifier at the random-oracle-derived challenges (Fiat-Shamir forking, residual)

`Soundness/Main` proves the deployed soundness reductions over a `Challenges` value taken as a *free* input
(the interactive verifier's coins). This module instantiates them at the **non-interactive** challenges the
proof actually induces under a random oracle `O` — `deriveChallenges (ofOracle O) …` — so the statements
are about the deployed verifier's own Fiat-Shamir coins rather than arbitrary ones.

What this discharges of issue #11: the challenge derivation is now under the random-oracle model
(`RandomOracle`), the transcript is faithful to halo2 (`Verifier.FiatShamir`), the soundness reductions are
stated at the RO-derived challenges, and the **tree assembly is proven** — `fiatShamirTree_of_forking`
(`Soundness.Main`, via `ForkingAssembly.forkAccept_to_acceptV`) turns the forking *output* into the deployed
transcript tree. So the residual is no longer "the verifier equation yields the whole tree" but the narrower
forking *output* `FiatShamirForking` at the RO-derived challenges: that rewinding produces the
distinct-challenge accepting transcripts (with each round point's value/blinding decomposition). The
rewinding primitive it abstracts is `RandomOracle.reprogram`; producing those transcripts by rewinding, and
the probabilistic success bound (`uniformChallenge_badSet`'s `d/p` budget), are the out-of-Lean floor — the
same honest boundary as the DLR/AGM layer for binding.

This both narrows the residual to the proof's *own* RO-derived challenges and shrinks it from the full
tree-assembly handwave to the rewinding alone, with the deterministic assembly now a theorem.

A further, *probabilistic* layer (`deployed_forking_soundness`, `…_flat`, `…_of_bridge`, and the Vesta-level
`orchard_verifier_vesta_forking_opening`) goes one step further: it replaces even the `FiatShamirForking`
output by an accept-*probability* over the uniform random-oracle challenge beating the knowledge error `3k/N`,
plus an **explicit** prover-as-oracle bridge `hbridge` (the proof realized as a strategy whose per-path
`flatAccept` is the verifier's accept). That layer is stated over an abstract strategy; `hbridge` is the
named, irreducible prover-as-oracle/Blake2b floor, not a hidden assumption. See those theorems for the exact
granular residual.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A random-oracle-backed Fiat-Shamir instance: the squeeze *is* the oracle `O`. -/
def ofOracle (O : List (TranscriptElt Fp G) → Fp) : FiatShamir Fp G := ⟨O⟩

/-- The non-interactive challenges a proof induces under random oracle `O` (the deployed verifier's own
Fiat-Shamir coins): `deriveChallenges` through `ofOracle O`. -/
def roChallenges {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) : Challenges shape.k Fp :=
  deriveChallenges (ofOracle O) init ps

/-- The deployed opening reduction at the **random-oracle-derived** challenges. Identical to
`orchard_verifier_deployed_opening_reduction` but with the free `Challenges` replaced by the proof's own
`roChallenges O init ps`, so the statement is about the deployed (non-interactive) verifier. The residual is
now the Fiat-Shamir forking *output* `hForking` (`FiatShamirForking`: rewinding yields the distinct-challenge
accepting transcripts), taken at those RO-derived challenges; the tree assembly downstream of it is proven
(`fiatShamirTree_of_forking`), so what stays out of Lean is the rewinding itself (`RandomOracle.reprogram`)
and its probabilistic success bound (issue #11). Conclusion and reduction framing are unchanged:
`S ∨ HasNontrivialRelation g U W`, vacuous as a statement at a prime-order curve, force in the DLR/AGM layer.
`hcirc` retains the ∀-openings shape — unsatisfiable for the intended instantiation (see the caveat on
`orchard_verifier_deployed_opening_reduction`; the restatement over the extracted witness is issue #18). -/
theorem orchard_verifier_deployed_opening_reduction_ro [DecidableEq G] [Inhabited G] {shape : Shape}
    (O : List (TranscriptElt Fp G) → Fp) (init : List (TranscriptElt Fp G))
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps (roChallenges O init ps))
    (hForking : FiatShamirForking urs hk vk ps (roChallenges O init ps) b z blind)
    (hcirc : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps)) b
      (multiopenValue vk ps (roChallenges O init ps)) a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
      b (multiopenValue vk ps (roChallenges O init ps)) circuitSat a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  orchard_verifier_deployed_opening_reduction urs hk vk ps (roChallenges O init ps) hz haccepts
    (fiatShamirTree_of_forking urs hk vk ps (roChallenges O init ps) b z blind hForking) hcirc hencodes

open Polynomial in
/-- The deployed opening-and-constraint reduction at the **random-oracle-derived** challenges. As
`orchard_verifier_deployed_constraint_reduction`, with the free `Challenges` replaced by the proof's own
`roChallenges O init ps`. The forking-output residual `hForking` (the tree assembly downstream is proven,
`fiatShamirTree_of_forking`) and the Schwartz–Zippel good-challenge condition (`hquot`/`hgood`) are taken at
the RO-derived challenges; under the random-oracle model the SZ exclusion is the `d/p` budget of
`uniformChallenge_badSet`, whose discharge into `hgood` is part of the out-of-Lean floor (issue #11/#12).
`hquot`/`hgood` retain the ∀-openings shape — unsatisfiable for any decode that genuinely reads the witness
(see the caveat on `orchard_verifier_deployed_constraint_reduction`; issue #18). -/
theorem orchard_verifier_deployed_constraint_reduction_ro [DecidableEq G] [Inhabited G] {shape : Shape}
    (O : List (TranscriptElt Fp G) → Fp) (init : List (TranscriptElt Fp G))
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp) (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps (roChallenges O init ps))
    (hForking : FiatShamirForking urs hk vk ps (roChallenges O init ps) b z blind)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps)) b
        (multiopenValue vk ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps)) b
        (multiopenValue vk ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps)) b
      (multiopenValue vk ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  orchard_verifier_deployed_constraint_reduction urs hk vk ps (roChallenges O init ps) fixedCols
    decodeAdvice decodeInstance y gates hpoly deg x hz haccepts
    (fiatShamirTree_of_forking urs hk vk ps (roChallenges O init ps) b z blind hForking) hquot hgood hencodes

/-! ## The flat forking residual: no posited decomposition

`FiatShamirForking` bundles the rewinding *with* each round point's value/blinding decomposition (the
`Lv/Rv/Lw/Rw` in its `ForkAccept` tree). `FiatShamirForkingFlat` drops the decomposition: it supplies only
the rewound transcripts' round points and final openings (`DForkCert`) and asserts the deployed
commitment-*whole* folds by them to the flat verifier leaf equation (`DeployedForkValid`). The decomposition
is then *recovered* (`produceDeployed`) and the root pinned to the deployed commitment (`deployed_forking_tree`,
via `fold_inj` + `separate_or_relation`). So this residual is strictly weaker — the decomposition is no longer
assumed, only the rewinding (and `∃ aDep, P = ⟨aDep,g⟩`, the structural fact that the multiopen commitment is
a generator commitment). -/

/-- The **flat** Fiat–Shamir forking residual: the rewinding supplies the deployed-folded transcripts
(`DeployedForkValid`) with *no* posited value/blinding decomposition — just the round points and final
openings in `DForkCert`. The deployed commitment is taken in its generator-commitment form `⟨aDep, g⟩` (the
multiopen commitment is such), and the threaded whole is `⟨aDep,g⟩ + [z·v]U + [blind]W`. -/
def FiatShamirForkingFlat [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Prop :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    ∃ (aDep : Fin (2 ^ urs.k) → Fp) (cert : DForkCert Fp G urs.k),
      deployedCommitment urs hk vk ps ch = commitGen urs.g aDep ∧
      DeployedForkValid urs.g b urs.u urs.w z
        (commitGen urs.g aDep + (z * multiopenValue vk ps ch) • urs.u + blind • urs.w) cert

/-- **The deployed opening reduction from the flat forking residual.** As
`orchard_verifier_deployed_opening_reduction`, but resting on `FiatShamirForkingFlat` (no posited
decomposition) instead of `FiatShamirForking`/`FiatShamirTree`. The decomposition is recovered and the root
pinned to `deployedCommitment` by `deployed_forking_tree`; its `∨ HasNontrivialRelation` is absorbed into the
reduction's own relation branch (binding). So the residual carries only the rewinding, not the
`L`/`R`↦value/blinding split — the special-soundness extraction that the split used to assume is now proven.
`hcirc` retains the ∀-openings shape — unsatisfiable for the intended instantiation (see the caveat on
`orchard_verifier_deployed_opening_reduction`; issue #18). -/
theorem orchard_verifier_deployed_opening_reduction_flat [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hforkflat : FiatShamirForkingFlat urs hk vk ps ch b z blind)
    (hcirc : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨aDep, cert, hgspan, hvalid⟩ := hforkflat (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_forking_tree hz urs.g b aDep (multiopenValue vk ps ch) blind cert hvalid
    with ⟨blind', t, ht⟩ | hrel
  · rw [← hgspan] at ht
    rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
      blind' t ht with hclean | hrel
    · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
        (multiopenValue vk ps ch) (projTree t) hclean
      exact Or.inl (hencodes a ⟨hrel', hcirc a hrel'⟩)
    · exact Or.inr hrel
  · exact Or.inr hrel

/-! ## The deployed forking opening: the value-placement composed end to end

This closes the deterministic chain. From the flat forking output threading halo2's *adjusted* commitment
`P' = ⟨aDep,G⟩ = multiopen − [v]g₀ + [ξ]⟨s,G⟩` (the verifier's `add_constant_term(-v)` plus the synthetic
blinding `[ξ]S`), `deployed_forking_tree` extracts an opening of `P'` to inner product `0`, and the
adjusted-commitment theorem (`ipaRelation_unshift` on `b₀ = 1`, then `ipaRelation_unblind_value`
*unconditionally*) lifts it to an opening of the *multiopen* commitment `⟨aMulti,G⟩` to its **true** value
`v − ξ·⟨s,b⟩`. So every step from the rewinding output to the deployed inner-product relation is a theorem;
the residual is `DeployedForkValid` (the rewinding itself), the `g`-span/adjusted form, `b₀ = 1`, and
Blake2b-as-random-oracle. -/

/-- **The deployed forking opening.** A flat forking output (`DeployedForkValid`, no posited decomposition)
threading halo2's adjusted commitment `⟨aDep,G⟩ = ⟨aMulti,G⟩ − [v]g₀ + [ξ]⟨s,G⟩` yields an inner-product
opening of the multiopen commitment `⟨aMulti,G⟩` to the **true** value `v − ξ·⟨s,b⟩` — or a nontrivial
relation. The extraction (`deployed_forking_tree`) opens `⟨aDep,G⟩` to inner product `0`; `ipaRelation_unshift`
(keyed on `b₀ = 1`) restores the value, and `ipaRelation_unblind_value` strips the synthetic blinding
*unconditionally* — reporting the true opened value whatever the prover's blinder `s` is (no `⟨s,b⟩ = 0`
assumed; the honest case `⟨s,b⟩ = 0` recovers the claimed `v`). Every deterministic tie from rewinding to the
opening is now proven. -/
theorem deployed_forking_relation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : DForkCert Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases deployed_forking_tree hz urs.g b aDep 0 blind cert hvalid with ⟨blind', t, ht⟩ | hrel
  · rcases deployed_to_acceptV hz urs.g b (commit urs aDep) 0 blind' t ht with hclean | hrel
    · obtain ⟨a, ha⟩ := ipaRelation_of_acceptV urs b (commit urs aDep) 0 (projTree t) hclean
      have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
        (by rw [add_sub_cancel_right]; exact ha)
      have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
        rw [hP]; abel
      rw [h2] at h1
      exact Or.inl ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _ h1⟩
    · exact Or.inr hrel
  · exact Or.inr hrel

/-! ## Closing the rewinding gap: the forked transcripts are *produced* by the probability

`deployed_forking_relation` still took `DeployedForkValid` (the forked transcripts) as a hypothesis. This
discharges it. In the random-oracle model the challenge vector is uniform, so the prover's accept event is a
finite set whose measure is its accept *probability*. When that probability exceeds the knowledge error
`kerr/Nᵏ = 3k/N`, `extractable_of_prob` — the averaging argument that *is* the multi-round forking lemma —
forces a full `(3,…,3)` forking tree to exist, and `proverAccept_forkValid` reads off the `DeployedForkValid`
certificate. So the rewinding output is no longer assumed: it is produced by the accept probability beating
the knowledge error, in the ideal RO model. The residual is exactly Blake2b-as-random-oracle (what makes the
challenge uniform), the prover-as-strategy `P`, and the standard structural/honest-prover facts. -/

open scoped ENNReal in
open Classical in
/-- **Challenge inversion is measure-preserving.** Componentwise inversion `χ ↦ (·⁻¹) ∘ χ` is an involution
on `Fin d → Fp` — a field satisfies `a⁻¹⁻¹ = a` for *every* `a` (including `0`, since `0⁻¹ = 0`) — hence a
bijection of the uniform random-oracle sample space onto itself. So relabelling the challenge vector by
inversion leaves any accept event's probability unchanged. This is the probabilistic half of the
consistency bridge: the deployed verifier folds generators by `foldGens g u⁻¹` (`foldAll`) while the
extraction tree folds by `foldGens g u`, and the two accept events differ by exactly this inversion — so they
have the same accept probability, and the soundness hypothesis on the tree predicate is the deployed
verifier's accept probability. -/
theorem uniformOfFintype_measure_inv {d : ℕ} (acc : (Fin d → Fp) → Prop) :
    (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ : Fin d → Fp => acc (fun i => (χ i)⁻¹)))
      = (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure (Finset.univ.filter acc) := by
  rw [PMF.toOuterMeasure_apply_finset, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  refine Finset.card_bij' (fun χ _ => (fun i => (χ i)⁻¹)) (fun χ _ => (fun i => (χ i)⁻¹))
    ?hi ?hj ?li ?ri
  case hi =>
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact hχ
  case hj =>
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    have hχχ : (fun i => ((χ i)⁻¹)⁻¹) = χ := by funext i; rw [inv_inv]
    rw [hχχ]; exact hχ
  case li => intro χ _; funext i; simp only [inv_inv]
  case ri => intro χ _; funext i; simp only [inv_inv]

open scoped ENNReal in
/-- **The synthetic blinder's soundness budget (ξ-randomization).** A malicious IPA blinder `S = ⟨s,G⟩` with
`⟨s,b⟩ = δ ≠ 0` shifts the opened value of the multiopen commitment by `−ξδ` (`ipaRelation_unblind_value`):
the plain commitment opens to `v − ξδ` rather than the claimed `v`. Because the verifier squeezes `ξ` *after*
the prover has committed `S` (`deriveChallenges`), `δ` is fixed before `ξ`, so the shifted value `v − ξδ`
hits any fixed target `c` for at most one challenge `ξ = (v−c)/δ` — a set of uniform random-oracle measure
`≤ 1/p`. This is the `1/p` soundness role of `[ξ]S`: it replaces the honest-prover assumption `⟨s,b⟩ = 0`
(the `hs` of `ipaRelation_unblind`) by a Schwartz–Zippel exclusion over `ξ`. -/
theorem blinder_shift_badSet_measure (δ c : Fp) (hδ : δ ≠ 0) :
    uniformChallenge.toOuterMeasure (Finset.univ.filter (fun ξ : Fp => ξ * δ = c))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  have hcard : (Finset.univ.filter (fun ξ : Fp => ξ * δ = c)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro ξ₁ h₁ ξ₂ h₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact mul_right_cancel₀ hδ (h₁.trans h₂.symm)
  gcongr
  exact_mod_cast hcard

/-- The deployed accept condition along one challenge path, in the **flat verifier's** IPA fold convention:
generators (and eval vector) fold by `foldGens · u⁻¹` — exactly halo2's `foldAll`/`computeS` direction — rather
than the extraction tree's `foldGens · u` (`proverAccept`). Everything else (the commitment fold `[u⁻¹]L + [u]R`,
the leaf check) is identical. Its `CF`-fold is intended to match `DeployedIpaVerifierEq` — `deployedVerifierEq_cf`
identifies the verifier equation with `CF = 0`, and the per-path identification is supplied as the explicit
`hbridge` of `deployed_forking_soundness_of_bridge`, not proved here. -/
def flatAccept : {d : ℕ} → Prover Fp G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → Fp) → (U W : G) → (z : Fp) →
    G → (Fin d → Fp) → Prop
  | 0, .leaf c f, g, b, U, W, z, Pwhole, _ =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, .node L R cont, g, b, U, W, z, Pwhole, χ =>
      flatAccept (cont (χ 0)) (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹) U W z
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-- The prover strategy re-indexed for the flat convention: swap each round's `(L, R)` and feed every
continuation the inverted challenge. The involution that, together with challenge inversion, turns the
extraction tree's fold convention into the flat verifier's. -/
def invProver : {d : ℕ} → Prover Fp G d → Prover Fp G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node R L (fun u => invProver (cont u⁻¹))

/-- `invProver` is an involution. -/
theorem invProver_invProver : {d : ℕ} → (P : Prover Fp G d) → invProver (invProver P) = P
  | 0, .leaf _ _ => rfl
  | _ + 1, .node L R cont => by
      simp only [invProver]
      congr 1
      funext u
      rw [inv_inv, invProver_invProver (cont u)]

/-- **The convention bridge (pointwise).** The extraction tree's accept predicate `proverAccept` (folding
generators by `foldGens g u`) at challenge vector `χ` is *exactly* the flat verifier predicate `flatAccept`
(folding by `foldGens g u⁻¹`) for the re-indexed prover `invProver P` at the inverted challenges `χ⁻¹`. The two
IPA fold conventions differ only by this challenge inversion and an `L`/`R` swap — both discharged here by
structural induction (`inv_inv`, `Fin.tail` of an inverted vector, and commutativity of the commitment fold).
No correctness gap: the tree predicate *is* the flat verifier predicate, relabelled. -/
theorem proverAccept_iff_flatAccept {U W : G} {z : Fp} : {d : ℕ} → (P : Prover Fp G d) →
    (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) → (Pwhole : G) → (χ : Fin d → Fp) →
    (proverAccept P g b U W z Pwhole χ ↔
      flatAccept (invProver P) g b U W z Pwhole (fun i => (χ i)⁻¹))
  | 0, .leaf _ _, _, _, _, _ => Iff.rfl
  | d + 1, .node L R cont, g, b, Pwhole, χ => by
      rw [proverAccept, proverAccept_iff_flatAccept (cont (χ 0)) (foldGens g (χ 0)) (foldGens b (χ 0))
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ), invProver, flatAccept]
      simp only [inv_inv]
      have htail : (Fin.tail fun i => (χ i)⁻¹) = (fun i => ((Fin.tail χ) i)⁻¹) := by
        funext i; rfl
      rw [htail, show Pwhole + (χ 0) • R + (χ 0)⁻¹ • L = Pwhole + (χ 0)⁻¹ • L + (χ 0) • R from by abel]

open scoped ENNReal in
open Classical in
/-- **The convention bridge (probabilistic) — the consistency gap, closed.** The extraction tree's accept
predicate (`proverAccept`, fold `foldGens g u`) and the flat verifier predicate (`flatAccept`, fold
`foldGens g u⁻¹` — halo2's actual `foldAll`/`computeS` direction) have *equal* accept probability under the
uniform random oracle. Pointwise they are the same event up to challenge inversion
(`proverAccept_iff_flatAccept`), and inversion is measure-preserving (`uniformOfFintype_measure_inv`). So the
`u`-vs-`u⁻¹` IPA fold convention is not a correctness gap: the tree predicate and the flat-convention
predicate share an accept probability. (Identifying `flatAccept` itself with the deployed verifier's *actual*
accept event is the separate prover-as-oracle bridge, `deployed_forking_soundness_of_bridge`.) -/
theorem proverAccept_measure_eq_flatAccept {d : ℕ} {U W : G} {z : Fp} (P : Prover Fp G d)
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → Fp) (Pwhole : G) :
    (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (proverAccept P g b U W z Pwhole))
      = (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (flatAccept (invProver P) g b U W z Pwhole)) := by
  have hset : (Finset.univ.filter (proverAccept P g b U W z Pwhole))
      = Finset.univ.filter
          (fun χ : Fin d → Fp => flatAccept (invProver P) g b U W z Pwhole (fun i => (χ i)⁻¹)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact proverAccept_iff_flatAccept P g b Pwhole χ
  rw [hset, uniformOfFintype_measure_inv]

open scoped ENNReal in
/-- **The forking soundness for an abstract prover strategy.** For a strategy tree `P`, if its accept event
`proverAccept P …` has probability exceeding the knowledge error `kerr (card Fp) k / (card Fp)ᵏ` (`= 3k/N`)
over the uniform challenge vector, then the multiopen commitment `⟨aMulti,G⟩` opens to its **true** value
`v − ξ·⟨s,b⟩` — or a nontrivial relation. `extractable_of_prob` (the averaging argument) turns the probability
into a forking tree, `proverAccept_forkValid` into a `DeployedForkValid` certificate, and
`deployed_forking_relation` into the opening. This is the **abstract** layer: `P` is an arbitrary strategy and
the challenge vector is taken uniform. Tying it to the deployed verifier — that the actual proof realizes such
a `P` whose accept event is `DeployedIpaVerifierEq`, over the random-oracle-derived challenge — is the explicit
bridge of `deployed_forking_soundness_of_bridge`. The residual is that bridge (the prover-as-oracle / Blake2b
floor) together with the structural facts (`b₀ = 1`, the adjusted/`g`-span form `hP`); the synthetic blinder is
stripped unconditionally (no `s(x) = 0` assumed). -/
theorem deployed_forking_soundness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (P : Prover Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    [DecidablePred (proverAccept P urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w))]
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure
            (Finset.univ.filter (proverAccept P urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w)))) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨cert, hvalid⟩ := proverAccept_forkValid P urs.g b
    (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (extractable_of_prob _ hprob)
  exact deployed_forking_relation urs b v ξ z blind aMulti aDep s cert hz hb0 hP hvalid

open scoped ENNReal in
open Classical in
/-- **The deployed forking soundness, in the verifier's own fold convention.** Identical to
`deployed_forking_soundness`, but the accept-probability hypothesis is stated with `flatAccept` — the flat
verifier predicate folding generators by `foldGens g u⁻¹`, exactly halo2's `foldAll`/`computeS` direction —
rather than the extraction tree's `proverAccept` (`foldGens g u`). The two have equal accept probability
(`proverAccept_measure_eq_flatAccept`, via the measure-preserving challenge inversion), so this is a faithful
restatement in the verifier's own `u⁻¹` fold convention, with the `u`-vs-`u⁻¹` consistency gap discharged by
theorem. The hypothesis is still the *strategy* predicate `flatAccept Q`; identifying `Q` with the deployed
proof is the explicit bridge of `deployed_forking_soundness_of_bridge`. -/
theorem deployed_forking_soundness_flat [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure
            (Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w)))) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine deployed_forking_soundness urs b v ξ z blind aMulti aDep s (invProver Q) hz hb0 hP ?_
  rw [proverAccept_measure_eq_flatAccept (invProver Q) urs.g b
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w), invProver_invProver Q]
  exact hprob

/-! ## Discharging the deterministic half of the prover-as-oracle bridge `hbridge`

`hbridge` bundles a deterministic algebra half — the deployed verifier equation folds, along each challenge
path, to the flat tree predicate `flatAccept` of the proof read as a `Prover` — with the irreducible
random-oracle half (the accept *probability* is over uniform rewindable challenges). This section discharges
the **algebra half**: `deployedVerifierEq_iff_flatAccept` proves halo2's actual `DeployedIpaVerifierEq` is
`flatAccept (proverOfRounds …)` at the challenge vector, so `hbridge` is a *theorem* for the deployed verifier,
not an assumption. The residual is then only the random-oracle uniformity axiom (`RandomOracle`). -/

/-- The prover-strategy tree the deployed non-interactive proof realises: at each IPA round it commits the
proof's **fixed** round points `(Lⱼ, Rⱼ)` (they are written in the proof string, so the continuation ignores
the challenge), and the leaf carries the final folded opening scalar `c` and blinding `f`. This is the concrete
`Prover` object that `hbridge` posits abstractly — here built explicitly from the proof string. -/
def proverOfRounds : {d : ℕ} → (Fin d → G × G) → Fp → Fp → Prover Fp G d
  | 0, _, c, f => .leaf c f
  | _ + 1, R, c, f => .node (R 0).1 (R 0).2 (fun _ => proverOfRounds (Fin.tail R) c f)

/-- `foldGens` commutes with reindexing the generators along a `Fin.cast` (`loHalf`/`hiHalf` read only the
index value, which `Fin.cast` preserves). The bookkeeping lemma letting the `flatAccept` fold — indexed by the
round count `d` — meet the closed-form `CF` fold, indexed by the challenge-*list* length `(List.ofFn χ).length`
(propositionally, not definitionally, `d`). -/
theorem foldGens_comp_cast {m n : ℕ} (h : n = m) (g : Fin (2 ^ (m + 1)) → G) (u : Fp) :
    foldGens (fun j : Fin (2 ^ (n + 1)) => g (Fin.cast (by rw [h]) j)) u
      = fun i : Fin (2 ^ n) => foldGens g u (Fin.cast (by rw [h]) i) := by
  subst h; rfl

/-- Fin-indexed generator fold: fold `g` by `foldGens · (χ j)⁻¹` down all `d` rounds to a single generator.
The cast-free counterpart of the deployed list fold `foldAll (List.ofFn χ) …`, matching `flatAccept`'s
per-round generator fold exactly, so the identity's induction stays cast-free. -/
def foldAllFin : {d : ℕ} → (Fin d → Fp) → (Fin (2 ^ d) → G) → G
  | 0, _, g => g 0
  | _ + 1, χ, g => foldAllFin (Fin.tail χ) (foldGens g (χ 0)⁻¹)

/-- `foldAll` reindexed along a list equality: rewrites the list and the generators' `Fin.cast` together (via
`subst`), the tool that peels `foldAll (List.ofFn χ)` past the dependent cast that blocks a bare `rw`. -/
theorem foldAll_congr_cast {u u' : List Fp} (h : u = u') (g : Fin (2 ^ u.length) → G) :
    foldAll u g = foldAll u' (fun j => g (Fin.cast (by rw [h]) j)) := by
  subst h; rfl

/-- **The Fin↔list generator-fold bridge.** The cast-free `foldAllFin χ g` equals the deployed list fold
`foldAll (List.ofFn χ) (g ∘ cast) 0`. Peels one round on each side (`foldAllFin` by definition, `foldAll` via
`foldAll_congr_cast` past the dependent cast) and reconciles the folded generators by `foldGens_comp_cast`. -/
theorem foldAllFin_eq : {d : ℕ} → (χ : Fin d → Fp) → (g : Fin (2 ^ d) → G) →
    foldAllFin χ g = foldAll (List.ofFn χ) (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0
  | 0, _, g => by simp only [foldAllFin]; rfl
  | d + 1, χ, g => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      rw [foldAllFin, foldAllFin_eq (Fin.tail χ) (foldGens g (χ 0)⁻¹), foldAll_congr_cast hchal, foldAll]
      simp only [Fin.cast_cast]
      exact congrArg (fun gen => foldAll (List.ofFn (Fin.tail χ)) gen 0)
        (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-- `CF` reindexed along a challenge-list equality: rewrites the challenge list and the generators' `Fin.cast`
together (via `subst`). -/
theorem CF_congr_chal {u u' : List Fp} (h : u = u') (rounds : List (G × G))
    (g : Fin (2 ^ u.length) → G) (P : G) (c Uc Wc : Fp) (U W : G) :
    CF rounds u g P c Uc U Wc W
      = CF rounds u' (fun j => g (Fin.cast (by rw [h]) j)) P c Uc U Wc W := by
  subst h; rfl

/-- **The verifier-fold ↔ tree-fold identity — the deterministic core of `hbridge`.** For the concrete prover
tree `proverOfRounds R c f` built from a proof's fixed round points, the flat verifier predicate `flatAccept`
along challenge path `χ` is *exactly* the closed-form verifier equation `CF … = 0` over the round list
`List.ofFn R` and challenge list `List.ofFn χ`. Proven by induction on the round count: the leaf reconciles the
final opening (base), and each round folds one `(Lⱼ, Rⱼ)` into the commitment (`CF_cons`, the round point
undecomposed) while the value coefficient tracks the eval-vector fold `foldAllFin χ b`. No `sorry`/`axiom`. -/
theorem flatAccept_proverOfRounds :
    {d : ℕ} → (R : Fin d → G × G) → (c f : Fp) → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) →
    (U W : G) → (z : Fp) → (P : G) → (χ : Fin d → Fp) →
    (flatAccept (proverOfRounds R c f) g b U W z P χ ↔
      CF (List.ofFn R) (List.ofFn χ)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) P c
          (-(z * c * foldAllFin χ b)) U (-f) W = 0)
  | 0, R, c, f, g, b, U, W, z, P, χ => by
      rw [proverOfRounds, flatAccept]
      simp only [CF, gPart]
      rw [← foldAllFin_eq]
      have hg : commitGen g (fun _ : Fin (2 ^ 0) => c) = c • g 0 := by simp [commitGen]
      have hb : commitGen b (fun _ : Fin (2 ^ 0) => c) = c * b 0 := by simp [commitGen]
      simp only [roundSum, List.ofFn_zero, List.zip_nil_right, List.map_nil, List.sum_nil, add_zero,
        foldAllFin, hg, hb]
      constructor
      · intro h; rw [h]; module
      · intro h; linear_combination (norm := module) h
  | d + 1, R, c, f, g, b, U, W, z, P, χ => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      have hround : List.ofFn R = ((R 0).1, (R 0).2) :: List.ofFn (Fin.tail R) := by
        rw [List.ofFn_succ]; rfl
      rw [proverOfRounds, flatAccept,
          flatAccept_proverOfRounds (Fin.tail R) c f (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹) U W z
            (P + (χ 0)⁻¹ • (R 0).1 + (χ 0) • (R 0).2) (Fin.tail χ)]
      rw [hround, CF_congr_chal hchal]
      rw [show (((R 0).1, (R 0).2) : G × G)
            = ((R 0).1 + (0 : Fp) • U + (0 : Fp) • W, (R 0).2 + (0 : Fp) • U + (0 : Fp) • W) by simp]
      rw [CF_cons]
      simp only [mul_zero, add_zero, Fin.cast_cast]
      refine iff_of_eq (congrArg (· = (0 : G)) ?_)
      congr 1
      exact (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-- The Fin-indexed eval-vector fold is the flat `computeB` (the `b`-value bridge, Fin form): folds the powers
vector `evalVector d x` down `χ` to `computeB x (List.ofFn χ)`. `foldAllFin_eq` moves to the list fold and
`foldAll_evalVector` telescopes it. -/
theorem foldAllFin_evalVector {d : ℕ} (χ : Fin d → Fp) (x : Fp) :
    foldAllFin χ (evalVector d x) = computeB x (List.ofFn χ) := by
  rw [foldAllFin_eq]
  have hev : (fun j => evalVector d x (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
      = evalVector (List.ofFn χ).length x := by
    funext j; simp only [evalVector, Fin.val_cast]
  rw [hev]
  exact foldAll_evalVector x (List.ofFn χ)

/-- **`hbridge`, discharged for the deployed verifier (the algebra half).** halo2's actual verifier equation
`DeployedIpaVerifierEq` at any IPA challenge vector `ch.ipaRound` is *exactly* the flat verifier predicate
`flatAccept` of the concrete prover tree `proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF` read off the proof —
with the eval vector `evalVector shape.k ch.x3` and the adjusted commitment `multiopen + [-v]g₀ + [ξ]S`. This is
the deterministic content of the prover-as-oracle bridge, now a **theorem**, not an assumption: chaining
`deployedVerifierEq_cf` (the verifier equation is `CF = 0`), `flatAccept_proverOfRounds` (`flatAccept` of the
tree is that same `CF = 0`), and `foldAllFin_evalVector` (the `U`-coefficient is `computeB`). The only residual
is the random-oracle uniformity axiom on the accept *measure* (`RandomOracle`). -/
theorem deployedVerifierEq_iff_flatAccept {shape : Shape} [DecidableEq Fp] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    DeployedIpaVerifierEq g w u vk ps ch ↔
      flatAccept (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF) g (evalVector shape.k ch.x3) u w ch.z
        (multiopenCommitment g w u vk ps ch
          + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS)
        ch.ipaRound := by
  rw [deployedVerifierEq_cf, flatAccept_proverOfRounds, foldAllFin_evalVector,
    show (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z)
      = -(ch.z * ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound)) from by ring]

/-! ## The deterministic content of the prover-as-oracle bridge `hbridge` is proven

`hbridge` (the hypothesis of `deployed_forking_soundness_of_bridge` below) says: the deployed verifier's accept
event, as a function of the challenge vector, is the flat predicate `flatAccept Q` of a prefix-respecting prover
strategy `Q`. This is a **pointwise** (deterministic) identification — it carries no probability.

Its deterministic content is now **proven**: `deployedVerifierEq_iff_flatAccept` (above) proves halo2's actual
verifier equation `DeployedIpaVerifierEq` *is* `flatAccept (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF)` at the
challenge vector. The earlier "needs a separate round-by-round transcript-semantics layer" is done inside the
model: the tree is `proverOfRounds` (its round points fixed by the proof string, its leaf the final opening —
the Fiat-Shamir prefix-determination), and each path's `flatAccept` matches the verifier equation by
`flatAccept_proverOfRounds` (`flatAccept` ↔ `CF = 0`) composed with `deployedVerifierEq_cf` (`CF = 0` ↔ the
verifier equation).

**Status.** `hbridge` is *discharged* in the deployed opening capstone
`orchard_verifier_vesta_forking_opening_deployed` (`Soundness.Vesta`): that theorem takes halo2's **actual**
verifier accept `DeployedIpaVerifierEq` (no abstract `hbridge`) and proves the bridge internally via
`deployedVerifierEq_iff_flatAccept`, at the cost of the honest `S`-opening fact `commit urs s = ps.ipaS` (and
the `shape.k`↔`urs.k` transport, discharged by `subst`). The abstract theorems —
`deployed_forking_soundness_of_bridge` below, and `orchard_verifier_vesta_forking_opening`/`_constraint` —
retain `hbridge` as a *modular* hypothesis (they are stated over an abstract `accepts`/`Q`), now a theorem for
the deployed verifier rather than an irreducible assumption. The one irreducible floor, once `hbridge` is
discharged, is the random-oracle uniformity axiom on the accept *probability* (the uniform measure of `hprob`,
`RandomOracle`) — that the challenges are uniform, independent, rewindable random-oracle draws. -/

open scoped ENNReal in
open Classical in
/-- **The deployed forking soundness from an explicit prover-as-oracle bridge.** This is the honest top of the
forking chain. It takes the deployed verifier's *actual* accept event `accepts χ` — the verifier on the proof
at challenge vector `χ`, the proof being a function of `χ` is the Fiat-Shamir/random-oracle model — together
with the **explicit** faithfulness bridge `hbridge` identifying that event with the strategy predicate
`flatAccept Q`, and concludes the deployed opening from the accept *probability*.

`flatAccept` folds generators by `foldGens g u⁻¹`, exactly halo2's `compute_s` direction, so the verifier
equation `DeployedIpaVerifierEq` — which `deployedVerifierEq_cf` identifies with the closed form `CF = 0` —
folds along each challenge path to `flatAccept Q`. The deterministic content of `hbridge` is **proven** by
`deployedVerifierEq_iff_flatAccept` (the proof string read as the prefix-respecting `Prover`
`proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF`, whose per-path `flatAccept` *is* the verifier's accept), so
`hbridge` is *dischargeable* — but this theorem still takes it as an explicit hypothesis (it has not been
rewired to consume that identity; doing so also needs the `S`-opening fact `commit urs s = ps.ipaS`). With
`hbridge` supplied, the residual is *only* the random-oracle uniformity axiom on the accept probability — every
other link (extraction, root-consistency, value placement, the `u`-vs-`u⁻¹` convention) is a theorem. This is
the granular replacement for the monolithic `FiatShamirTree`. -/
theorem deployed_forking_soundness_of_bridge [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine deployed_forking_soundness_flat urs b v ξ z blind aMulti aDep s Q hz hb0 hP ?_
  have hset : Finset.univ.filter accepts
      = Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
          (commit urs aDep + (z * 0) • urs.u + blind • urs.w)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbridge χ
  rwa [hset] at hprob

end Zcash.Snark
