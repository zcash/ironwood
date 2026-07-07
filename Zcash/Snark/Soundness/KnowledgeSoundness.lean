import Mathlib
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Zcash.Snark.Soundness.Ipa.Extraction
import Zcash.Snark.Soundness.Constraints.Vanishing
import Zcash.Snark.Soundness.Ipa.CommitFold

/-!
# Knowledge soundness, end to end

The capstone: an accepting proof demonstrates knowledge of a witness satisfying the SNARK relation. It
composes the proven pieces of the soundness layer —

* `extract_correct` — the IPA extractor recovers the witness from an accepting transcript tree;
* `commitGen_round` + `ipaRelation_unique` — folding preserves the commitment and the opening is unique
  under binding (so an accepting transcript yields a consistent tree);
* `quotientCheck_sound` + `Expr.eval_toPoly` — the verifier's gate check, via Schwartz–Zippel, forces the
  committed polynomials to satisfy the circuit's constraint identity (off a `≤ d/p` bad set).

`SnarkRelation` is the relation the SNARK proves (the witness opens the commitment and the committed
polynomials satisfy the constraint identity); `knowledge_sound` assembles the proven lemmas into "the
extractor recovers the unique witness satisfying the relation"; `soundness_error` is the residual
`≤ d/p` Schwartz–Zippel error.

## Assumptions

This layer is sound relative to the following, each kept explicit rather than hidden:

* **DLR hardness** (discrete-log relations on the Vesta generators) — the binding hypothesis
  `CommitmentBinding`. Modeled as a reduction: `relation_of_collision` proves a binding violation yields
  a nontrivial relation, and `commitmentBinding_iff_no_relation` proves binding is exactly DLR hardness
  (the reduction is proven; only the hardness is claimed).
* **Fiat–Shamir / Blake2b** as a random oracle — challenges are treated as uniform and unpredictable; the
  hash and the random-oracle reduction are not modeled. The capstone's current assumption
  (`ExtractableFromAcceptance`) is in fact stronger — it bundles the IPA knowledge-soundness conclusion,
  not just Fiat–Shamir; narrowing it to "uniform challenges" is open extraction-side work.
* **Hasse bound** — the abstract development runs over any `Fp`-module `G`, but `Zcash.Snark.Soundness.Vesta`
  pins it to the concrete Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`), whose group law is proven
  (mathlib's elliptic-curve group law, via `WeierstrassCurve.Affine.Point`). The one residual assumption
  about the group is Hasse's bound (`Fact (HasseBound Vesta.curve)`); from it the order is *derived*, not
  assumed (`vestaOrder_of_hasse`, via CompElliptic's `Pasta.Vesta.card_eq` giving `Nat.card VestaG = p`,
  whence every point is `p`-torsion), carried like the field modulus `Fact (Nat.Prime p)`. Mathlib lacks
  Hasse's theorem, so it is the irreducible gap — but axiom-free, as a `Fact` hypothesis.
* **VK-correctness** (Daira's flow) — that the VK's gates encode the intended high-level relation (note
  ownership, value balance, nullifiers) is a separate workstream; this layer proves the verifier sound
  relative to the given VK, ending at "the witness satisfies the VK's constraint system."

## For human review
Check that `SnarkRelation` is the intended relation, that the four assumptions above are the right ones
and acceptably standard, and that the captured fingerprint match (`Zcash.Snark.Fixture`) is for the
intended Orchard Action circuit.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The relation the SNARK proves: the witness `a` opens the commitment `P` to the value `v`
(`IpaRelation`) and satisfies the circuit (`circuitSat a`). Both conjuncts are about the same extracted
witness `a` (fixing the earlier flaw where the constraint was on free, unrelated polynomials).
`circuitSat` is the circuit-satisfaction predicate — its intended instantiation is `circuitSatViaGates`
("the witness's decoded columns satisfy the `y`-combined gates"). This raw relation is intentionally
generic; the deployed decoded-column capstone in `Soundness.Multiopen.Decode` /
`orchard_verifier_deployed_decoded_constraint_reduction` pins the decode to the extracted witness via
`batch_open_soundV`.

Sharper statement of the legacy gap: the two conjuncts share only the symbol `a`. If the decode that feeds
`circuitSatViaGates` is left as a free function, `circuitSat a` may be instantiated independently of `a`,
so it need not constrain the extracted witness at all. -/
structure SnarkRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (a : Fin (2 ^ urs.k) → Fp) : Prop where
  opens : IpaRelation urs P b v a
  satisfiesCircuit : circuitSat a

/-- The intended concrete instantiation of `SnarkRelation.circuitSat`: the witness's decoded columns
satisfy the `y`-combined gates' quotient identity. `decodeAdvice`/`decodeInstance` map the IPA witness to
the circuit's column polynomials (the multiopen decode — abstract until the assembly is modeled), and
`combineGates` is the `y`-combination of the gate `Expr`s (`eval_combineGates`). So
`circuitSat := circuitSatViaGates …` reads "the extracted witness satisfies the circuit's gate constraints",
and `constraint_identity_of_accept` is what discharges it once the caller supplies a non-free decode. -/
def circuitSatViaGates {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) : Prop :=
  combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates = hpoly * (X ^ deg - 1)

/-- `circuitSat`, derived from the deployed constraint check (not assumed). With the numerator the gate
combination `combineGates …`, an accepting quotient check at the challenge `x` plus a good challenge
(`x` not a root of the constraint difference — its complement the `≤ deg/p` Schwartz–Zippel bad set) gives
`circuitSatViaGates …`: the witness's decoded columns satisfy the gates. So the circuit gate-satisfaction
conjunct of `SnarkRelation` is discharged from acceptance via `constraint_identity_of_accept`, modulo only
the multiopen decode. -/
theorem circuitSatViaGates_of_check {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) (x : Fp)
    (hcheck : quotientCheck
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0) :
    circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
  constraint_identity_of_accept _ hpoly deg x hcheck hgood

/-- Knowledge soundness (modulo its hypotheses and current modelling gaps). Given a consistent transcript tree `t` for `a`
(`hcons`), the opening (`hopen`), and circuit-satisfaction of `a` (`hsat`), the extractor recovers the
unique witness satisfying `SnarkRelation`. Composes `extract_correct` (extraction) and
`ipaRelation_unique` (uniqueness under DLR hardness).

The hypotheses `hcons` and `hsat` are assumed here, not derived from acceptance — deriving them
(via `accepting_fold_eq` + `commitGen_round`, and `constraint_identity_of_accept` off the `d/p` bad set)
is the open composition work for this raw theorem. The deployed decoded-column reduction handles the
multiopen witness-to-columns bridge separately. -/
theorem knowledge_sound (urs : URS G) (hbind : CommitmentBinding (F := Fp) urs)
    {t : Tree Fp urs.k} {a : Fin (2 ^ urs.k) → Fp} (hcons : Consistent t a)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} (hopen : IpaRelation urs P b v a)
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hsat : circuitSat a) :
    extract t = a ∧ SnarkRelation urs P b v circuitSat a
      ∧ ∀ a', IpaRelation urs P b v a' → a' = a :=
  ⟨extract_correct t a hcons, ⟨hopen, hsat⟩, fun _ h' => ipaRelation_unique hbind h' hopen⟩

/-- The residual soundness error of the constraint layer (re-export of `quotientCheck_sound`): a
committed-polynomial set that violates the constraint identity is accepted for at most a `deg / |F|`
fraction of the challenges (`|F| = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem soundness_error (numerator h : Polynomial Fp) (n : ℕ) (hne : numerator ≠ h * (X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) :=
  quotientCheck_sound numerator h n hne

end Zcash.Snark
