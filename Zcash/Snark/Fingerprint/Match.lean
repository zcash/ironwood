import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Arithmetic.Msm
import Zcash.Snark.Fingerprint.SchwartzZippel
import Zcash.Snark.Verifier.Assemble

/-!
# The fingerprint match

The cross-check that validates the Lean assembly against the deployed Rust verifier (in place of a
line-by-line translation proof): run the deployed verifier on a proof, capturing its assembled MSM and
the challenges it drew; run the Lean `assemble` on the same proof string and challenges; and compare
the two MSMs. A match means the two assembled MSMs agree coefficient-for-coefficient on this proof —
not merely as evaluated group elements.

This module provides the match's logical content:

* `MsmMatch` — coefficient-for-coefficient equality, with the commitment term lists compared up
  to reordering; `msmMatch_eval` shows a match implies equal evaluations. Both sides use the
  captured proof's own commitments as bases, so the match is a comparison of `F_p` scalars.
* `fingerprint_match_random_eval_sound` — soundness of the cheaper random-evaluation match: a
  nonzero coefficient difference evades a uniformly random evaluation with probability `≤ d / p`
  (Schwartz–Zippel). Instantiated at `assemble`'s realized coefficients by the representation
  walk (`Fingerprint/Rational/`, priced in `Fingerprint/Epsilon.lean`): a competing coefficient
  family that differs from Lean's anywhere agrees at a uniform point with probability
  `≤ (D + B) / p`, with per-capture literals beside the random fixtures
  (`Fixtures/*/Random/Epsilon.lean`; ε ≈ 2⁻²⁴⁰). The `native_decide` fixture match is what
  establishes agreement, on each of the five captured proofs — three of them at random inputs.
* `gScalars_card` — the structural cross-check: the assembled MSM carries `2 ^ k` URS-generator
  coefficients, matching the captured Orchard fingerprint's `2 ^ 11 = 2048`.
* `perm_reindex_of_nodup_snd` / `msmMatch_other_reindex_of_nodup` — the `Perm`→positional
  bridge: a match against an MSM with duplicate-free `other` bases pins every term positionally
  through the base-matching re-indexing, a function of the base lists alone. Instantiated per
  random capture as `fingerprint_matches_positional` (`Fixtures/*/Random/Epsilon.lean`).

## The design target

The captured MSM, together with the captured challenge schedule that produced it, is the entire
checkable Rust↔Lean trust boundary. Everything else transcribed from halo2/orchard — the
`configure` port, keygen, query layouts, the Fiat–Shamir schedule model, the URS and VK dumps —
exists to make the Lean development writable and is checked rather than trusted: a transcription
error that admits a proof the deployed verifier accepts but the Lean model does not must break
some fingerprint-match theorem, except with probability `≤ ε` over the randomness of the captured
inputs and conditional on enumerated premises — premises that include the sampled-point
distribution behind that probability (the captures' proof scalars come from fixed public seeds),
recorded honestly in the enumeration below. ε is priced at `assemble`'s own coefficients: on a
good event of assignments every assembled coefficient is a rational function of the proof-string
scalars and challenges with enumerated challenge-only denominators (`assembleCoeffFamily`,
`Fingerprint/Rational/Capstone.lean`), and `competing_coefficient_family_agreement_le`
(`Fingerprint/Epsilon.lean`) makes ε = `(D + B) / p` a theorem about these functions — `D` the
coefficient-family degree budget, `B` the summed denominator-factor degrees, `p ≈ 2²⁵⁴`. The
uniformity premise behind "a uniformly random point" is carried formally by the
challenge-restricted variant `competing_coefficient_family_agreement_le_challengesOnly`, and the
per-capture headliners with their literal ε live beside the random fixtures
(`Fixtures/*/Random/Epsilon.lean`). Only that direction
(deployed-accepts ⊆ model-accepts) is soundness-relevant *here*, which scopes this comparison
rather than stating a position on completeness: completeness is a goal of the development,
pursued for the Lean model, where it yields witness existence. The
boundary artifact is per-proof: halo2's optional `BatchVerifier` — random-linear-combination
batching of separate proof blobs — sits outside the single-bundle verifier formalized here, and
any batching layer prices on top of the per-proof artifact without adding transcription surface.

## The boundary at the derived key

The statements of record are the `nonInteractiveFingerprint_matches_derived` theorems — one per
capture family, in the five `Fixtures/*/*/Boundary.lean` modules: the challenges
are derived by Lean's schedule model (`deriveChallenges`), and the verifying key is spelled as
`derivedVk` — its end-to-end derivation from the ported `configure`/keygen at the captured URS
(`Keygen/Certificate.lean`, transported to the other families by their
`VkCertificate.lean` modules). This ties the σ- and fixed-column polynomial content
into the boundary: the compared bases are deterministic URS commitments of Lean's own keygen
output, so a transcription error in that content moves a base point and fails the match — an
accidental error cannot produce a colliding commitment, and a deliberate one has to solve
discrete log. The dumped key record, the per-field checks in
`Fixtures/SingleAction/Honest/VkMatch.lean`, and the standalone schedule theorems stay as diagnostics
that name what broke; as trust elements the derived-form match subsumes them.

The two honest families (`SingleAction`, `MultiAction`) state the match on real accepting
proofs; the two match-only families (`{SingleAction,MultiAction}/Random`) state it on random proof strings, so the slots whose honest values are
recomputable from the key, publics, and challenges — `fixedEvals`, `permutationCommonEvals`,
`instanceEvals` — carry random values and a sourcing swap in `assemble` cannot pass. The random
families' keys are certified by transporting the single-action keygen certificate along the
cross-capture point equalities of `Fixtures/PostNu63Random.lean` (each family's
`VkCertificate.lean`).

## The URS dump

The dumped monomial URS and Lagrange prefix are inside the boundary: Lean's derived key and
instance commitments are computed against them, and the captured MSM's bases were produced by
the real verifier from its real URS, so a wrong dump mismatches — again up to a deliberate
discrete-log-solving collision. The random captures pin the same dump by cross-capture record
equality with the honest ones (`Fixtures/PostNu63Random.lean`). On the honest captures
`capturedMsm_eval_eq_zero` additionally evaluates the g-block to the identity against the dumped
points — non-vacuity corroboration that a real accepting run exists, not a boundary element.

## What remains external

The Rust capture APIs are released: `FingerprintStrategy`, `ChallengeRecorder`,
`MSM::fingerprint_terms`, and `dump_vesta_lean_fixture` shipped in `halo2_proofs` 0.3.4
([zcash/halo2#914](https://github.com/zcash/halo2/pull/914)), the match-only exporter mode and
`numInstanceColumns` shape emission in `halo2_proofs` 0.3.5
([zcash/halo2#924](https://github.com/zcash/halo2/pull/924)), and the capture tests in orchard
0.15.3 ([zcash/orchard#531](https://github.com/zcash/orchard/pull/531), instance-commitment
derivation capture added by [zcash/orchard#538](https://github.com/zcash/orchard/pull/538)) with
the fabricate→replay random-capture drivers in orchard 0.15.5
([zcash/orchard#541](https://github.com/zcash/orchard/pull/541)), all wired through orchard's
`verifier-fingerprint` feature
(`halo2_proofs/unstable-verifier-fingerprint`). Five captures are loaded under
`Zcash/Snark/Fixtures/`: two honest accepting runs (`SingleAction`, `MultiAction`, generated by
`dump_vesta_lean_fixture`) and two match-only runs (the two
`Random/` families, generated by the match-only exporter, each with its
raw proof bytes kept as a `proof-bytes.hex` sibling). Each family's
`fingerprint_matches` runs the decidable comparison
`MsmMatch (assemble vk derivedInstanceCommitment ps ch) capturedMsm` by `native_decide` over
actual Vesta points,
and the boundary statements above restate it at the derived key and schedule. The generator
emits every distinct affine coordinate, validates it on `Vesta.curve`, and supplies the complete
Halo2 URS. On the honest captures `capturedMsm_eval_eq_zero` computes the captured MSM to the
identity and `assembledMsm_eval_eq_zero` transfers that result to Lean's assembly — the
non-vacuity witness that no match-only capture can provide. All five fixtures regenerate
byte-for-byte from the pinned `zcash/orchard` 0.15.5 release via
`scripts/regenerate-fingerprint-fixtures.sh`, run in CI
(`.github/workflows/fixtures.yml`); pins, seeds, and rationale in
`Fixtures/PROVENANCE.md`.

What is trusted rather than checked stays enumerated here — seven premises no fixture design can
absorb, the obligation being to keep them enumerated, audited, and small:

* capture faithfulness — the exporter is the deployed strategy minus the final `eval()`, a
  few-line reviewed diff;
* rejection paths — the deployed accept path is straight-line in proof values post-decode
  (`Core/ProofString.lean`), corroborated by the random captures running to completion;
* byte→algebraic decode — deployed rejects non-canonical encodings, the safe direction;
* Fiat–Shamir bytes and Blake2b — the typed schedule is not a transcript-binding model;
* the pinned-point caveat — a published capture could be special-cased by a malicious edit,
  excluded by review and by seeds fixed before code;
* exporter determinism — the regenerate-and-diff pipeline above;
* compiler trust for the fixture checks — censused per declaration in each family's
  `TrustBoundary.lean`.

The comparison against Orchard's canonical Post-NU6.3 `PinnedVerificationKey` and Halo2's
pinned-key serialization/Blake2b derivation remain the fixture-generation boundary rather than
being reimplemented in Lean.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm scalarFieldOrder)

/-- Two MSMs match iff their `g`/`w`/`u` coefficients are equal and their `other` term lists agree
up to reordering (`List.Perm`) — term order is only a serialization artifact of how each assembler
appends, and the term sum is order-independent (`msmMatch_eval`). -/
def MsmMatch {k : ℕ} {F G : Type*} (m₁ m₂ : Msm k F G) : Prop :=
  m₁.gScalars = m₂.gScalars ∧ m₁.wScalar = m₂.wScalar ∧ m₁.uScalar = m₂.uScalar ∧ m₁.other.Perm m₂.other

/-- **The fingerprint match implies equal evaluations.** Matching MSMs denote the same group
element under any URS — the term sum is order-independent — so the deployed accept check
(`eval = identity`) transfers. -/
theorem msmMatch_eval {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G)
    {m₁ m₂ : Msm urs.k F G} (h : MsmMatch m₁ m₂) : m₁.eval urs = m₂.eval urs := by
  obtain ⟨hg, hw, hu, ho⟩ := h
  unfold Msm.eval
  rw [hg, hw, hu, (ho.map (fun t => t.1 • t.2)).sum_eq]

/-- Matching concrete `ZMod` MSMs have equal executable evaluations. Unlike `msmMatch_eval`, this
uses canonical-natural scalar multiplication and therefore needs no group-order or module
assumption; it is the transfer theorem used by the concrete Vesta fixtures. -/
theorem msmMatch_evalNat {p : ℕ} {G : Type*} [AddCommGroup G] (urs : URS G)
    {m₁ m₂ : Msm urs.k (ZMod p) G} (h : MsmMatch m₁ m₂) :
    m₁.evalNat urs = m₂.evalNat urs := by
  obtain ⟨hg, hw, hu, ho⟩ := h
  unfold Msm.evalNat
  rw [hg, hw, hu, (ho.map (fun t => t.1.val • t.2)).sum_eq]

/-- `MsmMatch` is decidable when the coefficients and terms are: this is the concrete check run against a
captured MSM (compare the `2 ^ k` g-scalars, the `w`/`u` scalars, and the term list). -/
instance {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G] (m₁ m₂ : Msm k F G) :
    Decidable (MsmMatch m₁ m₂) := by
  unfold MsmMatch; infer_instance

/-- A `Perm` of pair lists with duplicate-free second components is realized by the unique
base-matching index bijection: `σ` sends position `i` of `l₂` to the position of `l₂[i]`'s
second component among `l₁`'s. `σ` is computed from the `Prod.snd` lists alone (the stated
`idxOf` form), so where the second components are constants — the fixed commitment bases of a
captured MSM — `σ` does not depend on the first components. This is the `Perm`→positional
bridge consumed by `fingerprint_matches_positional` at the random captures
(`Fixtures/*/Random/Epsilon.lean`). -/
theorem perm_reindex_of_nodup_snd {α β : Type*} [DecidableEq β]
    {l₁ l₂ : List (α × β)} (hperm : l₁.Perm l₂) (hnd : (l₂.map Prod.snd).Nodup) :
    ∃ σ : Fin l₂.length ≃ Fin l₁.length, ∀ i : Fin l₂.length,
      (σ i : ℕ) = (l₁.map Prod.snd).idxOf l₂[i].2 ∧ l₁[(σ i : ℕ)] = l₂[i] := by
  have hnd₁ : (l₁.map Prod.snd).Nodup := (hperm.map Prod.snd).nodup_iff.mpr hnd
  -- the base-matching index is in range: every base of `l₂` occurs among `l₁`'s bases
  have hlt : ∀ i : Fin l₂.length, (l₁.map Prod.snd).idxOf l₂[i].2 < l₁.length := by
    intro i
    have hmem : l₂[i].2 ∈ l₁.map Prod.snd :=
      List.mem_map_of_mem (hperm.mem_iff.mpr (l₂.getElem_mem i.isLt))
    simpa using List.idxOf_lt_length_of_mem hmem
  let f : Fin l₂.length → Fin l₁.length := fun i => ⟨(l₁.map Prod.snd).idxOf l₂[i].2, hlt i⟩
  -- `l₂[i]` occurs somewhere in `l₁`; base-Nodup forces that position to be the matched index
  have hpair : ∀ i : Fin l₂.length, l₁[(f i : ℕ)] = l₂[i] := by
    intro i
    obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.mp (hperm.mem_iff.mpr (l₂.getElem_mem i.isLt))
    have hfj : (f i : ℕ) = j := by
      have hjb : (l₁.map Prod.snd)[j]'(by simpa using hj) = l₂[i].2 := by
        simpa using congrArg Prod.snd hj'
      show (l₁.map Prod.snd).idxOf l₂[i].2 = j
      rw [← hjb]
      exact hnd₁.idxOf_getElem j (by simpa using hj)
    exact (getElem_congr_idx hfj).trans hj'
  have hinj : Function.Injective f := by
    intro i i' hii
    have h2 : l₂[(i : ℕ)] = l₂[(i' : ℕ)] :=
      (hpair i).symm.trans ((getElem_congr_idx (congrArg Fin.val hii)).trans (hpair i'))
    exact Fin.ext (hnd.of_map.getElem_inj_iff.mp h2)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simp [hperm.length_eq]⟩),
    fun i => ⟨rfl, hpair i⟩⟩

/-- `perm_reindex_of_nodup_snd` at a passing `MsmMatch`: when the matched-against MSM's `other`
bases are duplicate-free, the match's `Perm` is realized by the base-matching index bijection,
positionally. -/
theorem msmMatch_other_reindex_of_nodup {k : ℕ} {F G : Type*} [DecidableEq G]
    {m₁ m₂ : Msm k F G} (h : MsmMatch m₁ m₂) (hnd : (m₂.other.map Prod.snd).Nodup) :
    ∃ σ : Fin m₂.other.length ≃ Fin m₁.other.length, ∀ j : Fin m₂.other.length,
      (σ j : ℕ) = (m₁.other.map Prod.snd).idxOf m₂.other[j].2
        ∧ m₁.other[(σ j : ℕ)] = m₂.other[j] :=
  perm_reindex_of_nodup_snd h.2.2.2 hnd

open MvPolynomial Finset Fintype in
/-- Soundness of the random-evaluation match (Schwartz–Zippel): if a coefficient of the assembled
MSM minus the captured one is a nonzero polynomial `p` in the proof scalars and challenges, a
uniformly random evaluation misses the mismatch with probability `≤ deg p / |F_p|`. `p` is left
abstract — *not* instantiated at `assemble`'s actual coefficients — so this is not yet a Lean link
from "one random proof" to assembly correctness (see the module note above). -/
theorem fingerprint_match_random_eval_sound {n : ℕ} {p : MvPolynomial (Fin n) Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder :=
  fingerprint_schwartz_zippel hp

/-- The assembled MSM carries `2 ^ k` URS-generator coefficients (`gScalars : Fin (2 ^ k) → F`),
matching the captured Orchard fingerprint's `2 ^ 11 = 2048` g-scalars (`k = 11`). -/
theorem gScalars_card (k : ℕ) : Fintype.card (Fin (2 ^ k)) = 2 ^ k := Fintype.card_fin _

/-- The captured Orchard domain size: `k = 11` gives `2 ^ 11 = 2048` g-scalars. -/
theorem orchard_gScalars : (2 : ℕ) ^ 11 = 2048 := by norm_num

end Zcash.Snark
