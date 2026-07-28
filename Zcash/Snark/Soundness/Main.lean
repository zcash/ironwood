import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Forking.Assembly

/-!
# Conditional soundness and deployed acceptance

Soundness here starts from `DeployedAccepts`: `assemble?` succeeds and the resulting MSM evaluates
to zero. An earlier layer took an opaque `accepts : Prop` together with an assumed extraction
interface; both are retired, since the computed route now derives what they assumed.

## The deployed route

The deployed route pins the IPA commitment and value to the proof's `multiopenCommitment` and
`multiopenValue`:

1. `deployedAccepts_verifierEq` derives halo2's explicit IPA verifier equation.
2. The legacy `FiatShamirTree` supplies forks; `Soundness.Forking.Adversary` computes them from a
   bounded-query machine and charges query loss.
3. A fork either yields a clean IPA opening or computes a nontrivial `(g, U, W)` relation.

## The reduction form

In a prime-order group, a nontrivial relation exists mathematically. The security break is computing
its coefficients. `NontrivialRelation` therefore carries those coefficients as data, and the
reductions return it explicitly instead of asserting that one exists.

The computed route is in `Forking.Adversary.Algebraic`; `KnowledgeSoundness` records its
computational boundary.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Tracked semantic-adequacy gap: `S` is a free `Prop` and `hencodes` an assumed hypothesis, so
-- the chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never
-- reaches "…therefore a valid Orchard action" (note well-formed, value balanced, nullifier
-- correctly derived, spend authorized). Closing it means instantiating `S` to the concrete
-- Orchard statement and proving `hencodes` — the output-side dual of the input-side
-- VK-correctness gap (see `Verifier/Assemble.lean`). Large; not started.
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- Transport MSM evaluation across the equality `shape.k = urs.k`. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Deployed acceptance implies halo2's explicit IPA verifier equation. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts urs hk vk instanceCommitment ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk instanceCommitment ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk instanceCommitment ps ch hm
      -- `deployed_verification_eq` is generic in the grouping, so its statement is in raw
      -- `assembleOpening` terms; expand the adjusted commitment to meet it.
      unfold DeployedIpaVerifierEq deployedIpaCommitment multiopenCommitment multiopenValue
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)), ← hmeq]
      exact h

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`ipa_soundV` derives both opening equations from an accepting IPA tree. The bridge therefore does
not assume `IpaRelation`.
-/

/-- An accepting IPA tree has a witness satisfying `IpaRelation`. -/
theorem ipaRelation_of_acceptV (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    ∃ a, IpaRelation urs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV urs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- Compute the `IpaRelation` witness instead of hiding it behind an existential proposition. -/
def ipaRelation_extract (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    Σ' a, IpaRelation urs P b v a :=
  let s := ipa_extractV urs.g b P v t h
  ⟨s.1, s.2.1, by
    have hib : innerProduct s.1 b = commitGen b s.1 := by simp only [innerProduct, commitGen, smul_eq_mul]
    rw [hib]; exact s.2.2⟩

/-- The proof's deployed multiopen commitment over the supplied URS. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch

/-! ## The tree opens the commitment up to declared `U`/`W` components

Real commitments include a `W` blinding component, while an IPA leaf opens a point in the `g` span.
The forked transcript therefore declares `U` and `W` components and opens the adjusted commitment
`deployedCommitment − [pU]u − [pW]w`.
-/

/-- A forked accepting IPA tree opening the deployed commitment after removing declared components. -/
structure ForkedTranscript [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) where
  tree : DeployedIpaTreeV Fp G urs.k
  /-- The declared `U`-component of the pinned commitment (honest value: `0`). -/
  pU : Fp
  /-- The declared `W`-component of the pinned commitment (honest value: the aggregate blind). -/
  pW : Fp
  accepts : DeployedIpaAcceptV urs.g b urs.u urs.w z
    (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (multiopenValue vk instanceCommitment ps ch) blind tree

/-- The deployed commitment after removing the transcript's declared `U` and `W` components. -/
abbrev ForkedTranscript.openedCommitment [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp} {b : Fin (2 ^ urs.k) → Fp}
    {z blind : Fp} (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind) : G :=
  deployedCommitment urs hk vk instanceCommitment ps ch - fs.pU • urs.u - fs.pW • urs.w

/-- Build a forked transcript from a blinded opening of the deployed commitment. -/
theorem ForkedTranscript.nonempty_of_opening [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (u₁ u₂ u₃ : Fp) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
    (hP : deployedCommitment urs hk vk instanceCommitment ps ch = commitGen urs.g a + pU • urs.u + pW • urs.w)
    (hv : multiopenValue vk instanceCommitment ps ch = commitGen b a) :
    Nonempty (ForkedTranscript urs hk vk instanceCommitment ps ch b z blind) := by
  obtain ⟨t, ht⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
    urs.g b urs.u urs.w z blind a
  refine ⟨⟨t, pU, pW, ?_⟩⟩
  have hcancel : deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w
      = commitGen urs.g a := by rw [hP]; abel
  rw [hcancel, hv]
  exact ht

/-- Legacy interface from the deployed verifier equation to a forked transcript.

It bundles random-oracle rewinding, round-point representations, leaf data, and declared commitment
components. The live forking path proves the deterministic extraction pieces separately. -/
def FiatShamirTree [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch →
    ForkedTranscript urs hk vk instanceCommitment ps ch b z blind

/-- Apply the legacy fork bridge to a deployed accepting proof. -/
def ForkedTranscript.ofAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hFS : FiatShamirTree urs hk vk instanceCommitment ps ch b z blind) :
    ForkedTranscript urs hk vk instanceCommitment ps ch b z blind :=
  hFS (deployedAccepts_verifierEq urs hk vk instanceCommitment ps ch haccepts)

/-- Random-oracle forking output: declared commitment components and a ternary accepting tree. -/
def FiatShamirForking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch →
    Σ' (pU pW : Fp) (t : DeployedIpaTreeV Fp G urs.k),
      ForkAccept urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w) (multiopenValue vk instanceCommitment ps ch) blind t

/-- Convert explicit forking output into the legacy `FiatShamirTree` interface. -/
def fiatShamirTree_of_forking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    (hForking : FiatShamirForking urs hk vk instanceCommitment ps ch b z blind) :
    FiatShamirTree urs hk vk instanceCommitment ps ch b z blind := by
  intro hEq
  obtain ⟨pU, pW, t, hFork⟩ := hForking hEq
  exact ⟨t, pU, pW, forkAccept_to_acceptV _ _ _ _ _ t hFork⟩

/-! ## The constraint-side hypotheses are unsatisfiable at a prime-order curve

The constraint variants quantify over every mathematical opening, not only the extracted witness.
At a prime-order curve that premise is too strong for a circuit predicate that reads the witness.
These theorems therefore do not yet establish deployed gate soundness; they must be restated over the
extracted witness and multiopen decode.
-/

/-- Compute a nontrivial relation when a forked transcript does not project to a clean IPA tree. -/
def NontrivialRelation.ofUnopenedFork [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofDeployedTree hz urs.g b fs.openedCommitment
    (multiopenValue vk instanceCommitment ps ch) blind fs.tree fs.accepts hne

/-- Derive `S` from a clean fork, an all-openings circuit premise, and `hencodes`. -/
theorem orchard_verifier_deployed_opening_of_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hcirc : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) circuitSat a → S) :
    S := by
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b fs.openedCommitment
    (multiopenValue vk instanceCommitment ps ch) (projTree fs.tree) hclean
  exact hencodes a ⟨hrel, hcirc a hrel⟩

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

`circuitSatViaGates_of_check` lifts the verifier's point check to a polynomial identity when the
challenge avoids the Schwartz–Zippel bad set.
-/

open Polynomial in
/-- Add the gate-check conclusion to `orchard_verifier_deployed_opening_of_forked`. -/
theorem orchard_verifier_deployed_constraint_of_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
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
    S := by
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b fs.openedCommitment
    (multiopenValue vk instanceCommitment ps ch) (projTree fs.tree) hclean
  have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
      (hquot a hrel) (hgood a hrel)
  exact hencodes a ⟨hrel, hsat⟩

end Zcash.Snark
