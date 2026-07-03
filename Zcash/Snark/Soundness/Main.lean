import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Forking.Assembly
import Zcash.Snark.Soundness.MultiopenDecode

/-!
# Soundness composition: conditional, and the deployed accept condition

This module formalizes the composition that turns IPA knowledge soundness into the SNARK relation, in
two layers: a `_conditional` family over an opaque `accepts : Prop`, and a `_deployed` family over the
concrete accept condition `DeployedAccepts` (the rejecting `assemble?` succeeds and its MSM — the §1
fingerprint — evaluates to the identity). The conditional
theorems are named with a `_conditional` suffix to avoid overclaiming: they are scaffolds, not finished
soundness. The deployed `_opening` / `_constraint` theorems below derive the IPA opening (via `ipa_soundV`,
after peeling the `U`/`W` apparatus) and the gate constraint from the accept, with `P`/`v` **pinned** to
the proof's `multiopenCommitment`/`multiopenValue`. The accept is **proven** to entail the explicit
closed-form `DeployedIpaVerifierEq` (`deployedAccepts_verifierEq`, via `Zcash.Snark.Soundness.Deployed.Verification`
— an implication, the direction soundness consumes; the accept also comprises the rejection guards);
fidelity of that closed form to halo2's Rust is the §1 transcription (`assembleFinalMsm`/`ipaFold`, checked
by the fingerprint), not re-proved here. The residual `FiatShamirTree` bridge is the Fiat–Shamir
forking **plus the special-soundness extraction content**: the node `L`/`R`↦value/blinding decomposition,
the leaf `g`-representation of the folded commitment, and the adjusted-commitment step
`P' = P − [v]g₀ + [ξ]S` (folding the value and `S`/`ξ` terms into the opened commitment — which needs a
representation of the adversary point `S`, so it is not a deterministic rewrite) — all discharged on the
live forking path (`Soundness.Forking.Rewind`, `Forking.Assembly`, `Forking.Extractor`); this legacy bridge keeps
them bundled.
Commitment binding is load-bearing *in the proof* (the `U`/`W` separation is derived from a discrete-log
relation reduction, `Zcash.Snark.Soundness.Deployed.IpaPeel`), so the deployed conclusion is
`SnarkRelation ∨ HasNontrivialRelation` — a *reduction*: it exhibits a discrete-log relation rather than
asserting soundness outright. A relation always *exists* in a prime-order group, so at the concrete curve this
disjunction is propositionally `True` and the *statement* is vacuous; the soundness force is the
computational DLR/AGM layer — no feasible adversary can *find* the relation — which is **not** formalized
in Lean: `Soundness.AGM.Adapter` records only its deterministic core (the fixed-slot relation-to-DL adapter, the
fixed-slot DL challenge game, and the finite hit-slot accounting) — not the proposition.

## Assumptions (the conditional family)

* **Opaque accept.** `accepts` is a free `Prop`, not instantiated to the deployed accept condition, so
  `orchard_verifier_sound_conditional` says nothing about the fingerprint. The `_deployed` variants fix
  this by taking `DeployedAccepts`.
* **Extraction bundled with Fiat–Shamir.** `ExtractableFromAcceptance` assumes the IPA
  knowledge-soundness conclusion (a consistent transcript tree + a valid opening), bundling Fiat–Shamir
  with the extraction that `accepting_fold_eq` / `extract_correct` prove — so those proven lemmas are
  off this path.
* **Circuit satisfaction assumed, not derived.** `ExtractableFromAcceptance` also supplies `circuitSat a`
  rather than deriving it from the deployed constraint check via `constraint_identity_of_accept` and the
  multiopen decode.
* **Binding inert.** `hbind` (DLR hardness) reaches `knowledge_sound` but only feeds its uniqueness
  conjunct, which this proof discards.

What is proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`, `commitGen_round`,
`quotientCheck_sound`, `ipaRelation_unique`, the binding reduction, `eval_combineGates`); the open work
is wiring them onto this path. `Zcash.Snark.Soundness.Vesta` instantiates these at the concrete Vesta curve. See
`Zcash.Snark.Soundness.KnowledgeSoundness` for the assumption list.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Assumed: acceptance yields the IPA extraction data, which is stronger than just Fiat–Shamir. Given
`accepts`, this hands over a consistent transcript tree and a valid opening — i.e. it assumes the IPA
knowledge-soundness *conclusion* that `accepting_fold_eq` / `extract_correct` produce, bundled with
Fiat–Shamir. Honest reading: assume IPA knowledge soundness + FS, not hand-wave only FS. Splitting this
into the genuine FS step (`accept → ∃ tree`) and the proven extraction — narrowing the residual to
"challenges are uniform and unpredictable" — is open. It also bundles `circuitSat a` (the extracted
witness satisfies the circuit); deriving that from the deployed constraint check is likewise open. -/
def ExtractableFromAcceptance (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp urs.k) (a : Fin (2 ^ urs.k) → Fp),
    Consistent t a ∧ IpaRelation urs P b v a ∧ circuitSat a

-- Tracked semantic-adequacy gap: `hencodes`/`S` below are the seam from circuit-satisfiability to the
-- high-level Orchard relation. `S` is a free `Prop` and `hencodes` is an assumed hypothesis, so the
-- chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never reaches
-- "…therefore a valid Orchard action" (note well-formed, value balances, nullifier correctly derived,
-- spend authorized). Closing it: instantiate `S` to the concrete Orchard statement and prove `hencodes`.
-- The composition reaches only `SnarkRelation`; this is the output-side dual of the input-side
-- VK-correctness gap (see `Verifier/Assemble.lean`). Large; not started.
/-- Conditional soundness composition (not completed soundness). From the assumed extraction data
(`hextract haccepts`, which also yields `circuitSat a`), conclude `S` via `hencodes`.

This assumes what §2 should prove: `accepts` is opaque (the `_deployed` variant fixes that); the
extraction + circuit-satisfaction are assumed (so `accepting_fold_eq` / `extract_correct` /
`constraint_identity_of_accept` are off-path); and `hbind`'s binding only feeds the discarded uniqueness
conjunct. The scaffold for the composition, not the composition — see the module docstring, and the
deployed `_opening` / `_constraint` theorems below. -/
theorem orchard_verifier_sound_conditional (urs : URS G) (hbind : CommitmentBinding (F := Fp) urs)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound urs hbind hcons hopen hsat).2.1

/-- The deployed verifier's accept condition as a concrete predicate: the rejecting assembled fingerprint
MSM `assemble? vk ps ch` (the §1 object) evaluates to the group identity against the URS. This is what
`accepts` should be — the formal object §1 and §2 share. Rejected typed proof data (duplicate
commitment/point queries, a `multiopenU` count that does not match the derived point sets, missing
non-last permutation last-evals, or zero inverse denominators) is `False`.
(`hk` aligns the circuit shape's `k` with the URS's `k`.) -/
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- The `urs.k`↔`shape.k` transport, isolated: evaluating the `hk`-transported MSM against `urs` is the same
as evaluating `m` against the URS rebuilt at `shape.k` with `urs`'s (transported) generators. With `urs`
free here, `cases urs` + `subst hk` collapses the cast to `rfl`. This lets `deployedAccepts_verifierEq` reach
the `⟨shape.k, …⟩`-indexed `deployed_verification_eq` without destructuring the URS in place (which would
tangle the accept hypothesis's own `hk`-cast). -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Structural faithfulness, **proven** (was assumed by the Fiat–Shamir bridge): the deployed accept
*entails* halo2's explicit IPA verifier equation. (An implication, not an `Iff` — the accept additionally
comprises the rejection guards; this is the direction soundness consumes.) From `DeployedAccepts` (the
rejecting fingerprint `assemble?` succeeds and
evaluates to the identity), `assemble?_eq_some` identifies the accepted MSM with the non-rejecting
`assembleFinalMsm`, and `deployed_verification_eq` rewrites its evaluation to the explicit equation — so
`DeployedIpaVerifierEq` holds for the proof's actual `(vk, ps, ch)`. This discharges the MSM↔equation
correspondence the bridge used to absorb; the residual bundle in `FiatShamirTree` is the forking and the
extraction-content data it supplies — the node decomposition, the leaf `g`-representation, and the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S` (all discharged on the live forking path; the legacy
bridge keeps them bundled). The `urs.k`↔`shape.k`
transport is `eval_cast`. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts urs hk vk ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk ps ch)), ← hmeq]
      exact h

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the full opening relation — `commit g a = P` and `⟨a,b⟩ = v` — from an
accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So the bridge no
longer assumes `IpaRelation`. Honest caveat for `FiatShamirTree` below: beyond the Fiat–Shamir rewinding it
still absorbs (i) the node-level `L`/`R`↦value/blinding decomposition, (ii) the leaf `g`-representation of
the folded commitment (`DeployedIpaAcceptV`'s `∃ aP` span condition), and (iii) the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S` (folding the value and `S`/`ξ` terms — this needs a
representation of the adversary point `S`, so it is rewinding- or AGM-content, not a deterministic
rewrite). (i)–(ii) are what the special-soundness extraction would *derive* from the forked flat equations
by Vandermonde over the augmented `(g, U, W)` basis; here they arrive as bridge-supplied tree data. The
MSM↔equation correspondence and the `P`/`v` pinning it used to also absorb are now discharged
(`deployedAccepts_verifierEq`); the cryptographic opening and the `g`/`U`/`W` separation are derived. -/

/-- `IpaAcceptV` over the URS generators derives `IpaRelation`: the witness `ipa_soundV` extracts opens
`P` (`commit urs a = commitGen urs.g a`) and gives the inner product (`commitGen b a = ⟨a,b⟩`). The IPA
opening is derived, not assumed. -/
theorem ipaRelation_of_acceptV (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    ∃ a, IpaRelation urs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV urs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- The deployed commitment the IPA verifier opens (`multiopenCommitment` with `urs`'s generators
transported to the proof's `shape.k`): the pinned `P`, read off `(vk, ps, ch)`. Reducible, so it is defeq to
its body for matching against `DeployedIpaVerifierEq`'s leading term. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk ps ch

/-- The forking bridge — the *residual* assumption. Its premise is halo2's explicit verifier equation
`DeployedIpaVerifierEq` (which `deployedAccepts_verifierEq` *proves* the deployed
accept entails), and its conclusion opens the pinned `deployedCommitment`/`multiopenValue` — the actual
`P`/`v` from `(vk, ps, ch)`, not free parameters. So what this assumes is: the verifier equation holding
yields a consistent deployed IPA transcript tree (`DeployedIpaAcceptV`, carrying the `U`/`W` apparatus).
That bundles the Fiat–Shamir **forking** — (a) the rewinding that produces three accepting continuations
per node at distinct nonzero challenges — with the special-soundness **extraction** content, knowledge the
forked transcripts would pin by Vandermonde over the augmented `(g, U, W)` basis but that here arrives as
bridge-supplied tree data: (b) the node-level `L`/`R`↦value/blinding **decomposition**
(`Lv`/`Rv`/`Lw`/`Rw` — each round point's `(g, U, W)`-representation, which must not depend on `z`);
(c) the leaf **`g`-representation** `∃ aP, P = ⟨aP, g⟩` of the folded commitment (the span condition
`DeployedIpaAcceptV`'s leaf demands); and (d) the **adjusted-commitment** step `P' = P − [v]g₀ + [ξ]S`,
which folds the value term `[-v]g₀` and the `S`/`ξ` blinding-poly `[ξ]S` (both present in
`DeployedIpaVerifierEq`) into the commitment the tree opens — this needs a representation of the adversary
point `S` (ξ-side rewinding or AGM), so it is not a deterministic rewrite of the equation. The
MSM↔equation correspondence is discharged separately
(`deployedAccepts_verifierEq`), not assumed here; the per-leaf `g`/`U`/`W` separation is *derived*
(`deployed_to_acceptV`) — but `S`/`ξ` is not peeled, it lives in (d). `b`/`z`/`blind` are bridge-mediated
(the protocol fixes `b = evalVector urs.k ch.x3` — whose per-round fold telescopes to the leaf
`b₀ = computeB ch.x3 ·` — and `z = ch.z`); only `P`/`v` are pinned. All of (a)–(d) are discharged on the
live forking path (`Soundness.Forking.Rewind` and the Vesta `_rewind`/`_adaptive_rewind` capstones); this legacy
bridge keeps them bundled, with the execution-semantics identification the remaining out-of-Lean floor. -/
def FiatShamirTree [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Prop :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    ∃ t : DeployedIpaTreeV Fp G urs.k,
      DeployedIpaAcceptV urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch) blind t

/-- The Fiat–Shamir **forking** hypothesis — the genuine residual (the random-oracle floor). On an accepting
deployed proof, rewinding the random oracle yields the 3-special-soundness forking *output*: a
`DeployedIpaTreeV` whose every node records three accepting continuations at distinct nonzero per-round
challenges and whose every leaf carries the flat closed-form verifier equation (`ForkAccept`). This is
exactly the rewinding content that cannot be discharged in Lean; it supplies the distinct-challenge
transcripts and, in the node decorations, each round point's value/blinding decomposition. Everything
downstream of having these transcripts is a theorem (`fiatShamirTree_of_forking`). -/
def FiatShamirForking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Prop :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    ∃ t : DeployedIpaTreeV Fp G urs.k,
      ForkAccept urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch) blind t

/-- **The tree-assembly discharge.** The forking output (`FiatShamirForking`) *proves* the `FiatShamirTree`
bridge: the forking supplies the distinct-challenge accepting transcripts, and the deterministic assembly
`forkAccept_to_acceptV` (threading the per-round fold to the leaves, reconciling each flat closed-form
equation to the reformulated leaf check) turns them into `DeployedIpaAcceptV`. So the residual narrows from
the handwave "an accepting verifier equation yields the whole 3-ary tree" to the genuine random-oracle floor
"the rewinding yields the forked transcripts": the tree assembly itself — the node `L`/`R`↦value/blinding
fold and the adjusted-commitment/leaf reconciliation — is now a theorem, `sorry`/`axiom`-free. -/
theorem fiatShamirTree_of_forking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    (hForking : FiatShamirForking urs hk vk ps ch b z blind) :
    FiatShamirTree urs hk vk ps ch b z blind := by
  intro hEq
  obtain ⟨t, hFork⟩ := hForking hEq
  exact ⟨t, forkAccept_to_acceptV _ _ _ _ _ t hFork⟩

/-- One multiopen-forking output: the deployed IPA transcript tree, halo2's accept for it, and the
`x₁`/`x₄` batch-rewinding data for that same tree. -/
structure MultiopenForkingOutput [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G)
    (columnEvals : Fin numColumns → Fp) where
  tree : DeployedIpaTreeV Fp G urs.k
  rewind : MultiopenRewindBatch urs (deployedCommitment urs hk vk ps ch) b
    (multiopenValue vk ps ch) columnCommitments columnEvals (projTree tree)
  accepts : DeployedIpaAcceptV urs.g b urs.u urs.w z
    (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch) blind tree

/-- The issue-18 residual as one explicit forking output, *data-producing*: from the deployed verifier
equation it returns the deployed IPA tree together with the multiopen batch-rewinding data for that same
tree. Compared with `FiatShamirTree`, this also carries the `x₁`/`x₄` multiopen rewinds needed to bind the
extracted witness to real decoded columns. It returns data (a structure, not an `∃`) so the decoded
capstone's `hquot`/`hgood` can be stated about the canonical decode of the returned batch — an existential
output would force quantifying them over every batch, which is unsatisfiable (see the `MultiopenDecode`
scope section). -/
def FiatShamirMultiopenForking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp) :
    Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    MultiopenForkingOutput urs hk vk ps ch b z blind columnCommitments columnEvals

/-- The deployed Orchard verifier opening, as a binding **reduction**, with `P`/`v` **pinned** to the proof
(`deployedCommitment`/`multiopenValue` from `(vk, ps, ch)`, not free parameters). From the deployed accept,
`deployedAccepts_verifierEq` *proves* the explicit `DeployedIpaVerifierEq` form; the forking
bridge `hFS` turns that equation into the deployed transcript tree opening the pinned commitment (via the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S`); `deployed_to_acceptV` peels the `U`/`W` apparatus onto the
clean `IpaAcceptV` (deriving the per-leaf separation from binding); and `ipa_soundV` extracts the opening.

The conclusion is `S ∨ HasNontrivialRelation g U W` — a reduction (it exhibits a discrete-log relation
rather than asserting soundness outright). A relation always *exists* in a prime-order group, so at the
concrete curve this disjunction is propositionally `True`
and the theorem is vacuous *as a statement* (provable as `Or.inr` without the hypotheses); its content is
the constructive extraction plus the computational DLR/AGM assumption that no efficient adversary can
*find* the relation — not formalized in Lean; `Soundness.AGM.Adapter` records only the deterministic fixed-slot
relation-to-DL core and its augmented `(g,U,W)` specialization. Commitment
binding is load-bearing in the *proof structure*, not the Vesta statement.
Named assumptions: the residual bridge (`hFS`, superseded by the forking path), `z ≠ 0`, the circuit side (`hcirc`), and
VK-correctness (`hencodes`).

Caveat on `hcirc`'s shape: it quantifies over *every* mathematical opening `a` of the pinned `(P, b, v)`.
At a prime-order curve those openings form an affine subspace of dimension `≥ 2^k − 2` (two linear
conditions on `2^k` coordinates), so any `circuitSat` that genuinely reads the witness fails on almost
all of it — the hypothesis is unsatisfiable for the intended instantiation (the ∀-openings failure
mode the `MultiopenDecode` scope section records) in hypothesis position. `circuitSatViaGates_of_check` does not discharge it: that lemma
derives `circuitSat` for *one* `a` from that `a`'s own point-check, never the quantified premise.
The decoded-column capstone below restates the constraint side as a derived fact about columns recovered
from the batched openings that contain the extracted witness. -/
theorem orchard_verifier_deployed_opening_reduction [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hcirc : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind t ht with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree t) hclean
    exact Or.inl (hencodes a ⟨hrel', hcirc a hrel'⟩)
  · exact Or.inr hrel

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors the opening side. The verifier checks the gate identity only at the challenge
`x` — a point check (`quotientCheck`, `numerator.eval x = h.eval x · (xⁿ−1)`). `circuitSatViaGates_of_check`
lifts that point check to the polynomial identity `circuitSatViaGates` (the witness's decoded columns
satisfy the gates) provided `x` avoids the Schwartz–Zippel bad set (`hgood`). So `circuitSat`, instantiated
to the concrete `circuitSatViaGates`, is derived from the verifier's actual gate check rather than taken as
an opaque hypothesis. -/

open Polynomial in
/-- The deployed Orchard verifier opening and constraint, as a binding **reduction**, with `P`/`v` **pinned**
to the proof (`deployedCommitment`/`multiopenValue`). As `orchard_verifier_deployed_opening_reduction`, with
the circuit side derived too: `circuitSat` — instantiated to
`circuitSatViaGates` — from the verifier's quotient/gate point check `hquot` at the challenge `x`, lifted to
the polynomial identity by Schwartz–Zippel (`hgood`), via `circuitSatViaGates_of_check`. The deployed accept
reaches the forking bridge through the *proven* `deployedAccepts_verifierEq`. The conclusion is
`S ∨ HasNontrivialRelation g U W` — a reduction (it exhibits a discrete-log relation, not soundness
outright); a relation always *exists* at a prime-order curve, so this disjunction is propositionally `True`
and the theorem is vacuous as a *statement*, the force being the computational DLR/AGM layer (not
formalized in Lean) that no adversary can *find* one; `Soundness.AGM.Adapter` records only its deterministic
fixed-slot relation-to-DL core.

Named assumptions: the residual bridge (`hFS`, superseded by the forking path), `z ≠ 0`, the gate point-check (`hquot`), the SZ good
challenge (`hgood`), and VK-correctness (`hencodes`).

Caveat on the `hquot`/`hgood` shape (as for `hcirc` above): both quantify over *every* mathematical
opening `a` of the pinned `(P, b, v)` — an affine subspace of dimension `≥ 2^k − 2` at a prime-order
curve — so for any decode that genuinely reads columns out of `a` they are unsatisfiable, not merely
undischarged: the verifier's actual gate check constrains the *claimed* evaluations, not every
opening's decode. The decoded-column capstone below restates them over columns recovered from batched
openings via `batch_open_soundV`. -/
theorem orchard_verifier_deployed_constraint_reduction [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
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
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind t ht with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree t) hclean
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact Or.inl (hencodes a ⟨hrel', hsat⟩)
  · exact Or.inr hrel

/-- Two distinct openings of the same commitment exhibit a nontrivial `(g, U, W)` relation: their
difference is a nonzero kernel vector of `commit`. Lets the decoded capstones identify a supplied batch
witness with the transcript's own extracted witness, or fall into the relation branch. -/
theorem hasNontrivialRelation_of_two_openings (urs : URS G) {a a' : Fin (2 ^ urs.k) → Fp}
    (hne : a ≠ a') (hcollision : commit urs a = commit urs a') :
    HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine ⟨a - a', 0, 0, Or.inl (sub_ne_zero.mpr hne), ?_⟩
  have hsub : commitGen (F := Fp) urs.g (a - a') = commit urs a - commit urs a' := by
    simp only [commit, commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [hsub, hcollision]
  simp

open Polynomial in
/-- The deployed Orchard verifier opening and constraint, with the multiopen witness decoded into real
columns before the gate check is applied.

Compared with `orchard_verifier_deployed_constraint_reduction`, `hquot`/`hgood` are no longer quantified
over every mathematical opening of the pinned IPA relation. Instead, after the deployed accept peels to a
clean accepting IPA transcript, `hbatch` supplies the multiopen-rewinding output for that transcript: a
current IPA witness plus enough rewound batched openings containing it. `decodedColumnFamily_of_batch_openings`
then recovers the individual columns by `batch_open_soundV`. The gate check is stated over those recovered
columns, selected into the advice/instance slots the gate expressions read.

This discharges the witness-to-real-columns half of the constraint-side bridge once the multiopen rewinding
output is supplied. The remaining hypothesis shape is deliberately explicit: `hbatch` is the `x₁`/`x₄`
rewinding output for the accepted transcript, and `hquot` is still the separate
quotient-check-from-deployed-assembly fact — stated for the canonical decode of the supplied batch
(`decodedCols`), the family this proof constructs (the ∀-families form is jointly unsatisfiable; see the
`MultiopenDecode` scope section). The batch's `witness` is identified with the transcript's own extracted
witness: on mismatch the two openings of the pinned `(P, b, v)` collide on `commit` and the theorem
returns the relation branch, so `hencodes` only ever receives the extracted witness. -/
theorem orchard_verifier_deployed_decoded_constraint_reduction [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hbatch : ∀ t, IpaAcceptV urs.g b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) t →
      MultiopenRewindBatch urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch)
        columnCommitments columnEvals t)
    (hquot : ∀ t (hacc : IpaAcceptV urs.g b (deployedCommitment urs hk vk ps ch)
        (multiopenValue vk ps ch) t),
      quotientCheck
        (combineGates fixedCols
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) adviceIndex)
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) instanceIndex) y gates)
        hpoly deg x)
    (hgood : ∀ t (hacc : IpaAcceptV urs.g b (deployedCommitment urs hk vk ps ch)
        (multiopenValue vk ps ch) t),
      combineGates fixedCols
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) adviceIndex)
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) adviceIndex)
          (selectedPolys (decodedCols (hbatch t hacc).batchOpenings) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs (deployedCommitment urs hk vk ps ch) b
        (multiopenValue vk ps ch) columnCommitments columnEvals adviceIndex instanceIndex fixedCols
        y gates hpoly deg a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind t ht with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree t) hclean
    by_cases hw : (hbatch (projTree t) hclean).witness = a
    · subst hw
      have hsat : circuitSatViaGates fixedCols
          (selectedPolysDecode (k := urs.k)
            (decodedCols (hbatch (projTree t) hclean).batchOpenings) adviceIndex)
          (selectedPolysDecode (k := urs.k)
            (decodedCols (hbatch (projTree t) hclean).batchOpenings) instanceIndex)
          y gates hpoly deg (hbatch (projTree t) hclean).witness :=
        circuitSatViaGates_of_check fixedCols
          (selectedPolysDecode (k := urs.k)
            (decodedCols (hbatch (projTree t) hclean).batchOpenings) adviceIndex)
          (selectedPolysDecode (k := urs.k)
            (decodedCols (hbatch (projTree t) hclean).batchOpenings) instanceIndex)
          y gates hpoly deg (hbatch (projTree t) hclean).witness x
          (hquot (projTree t) hclean) (hgood (projTree t) hclean)
      exact Or.inl (hencodes (hbatch (projTree t) hclean).witness
        (decodedCols (hbatch (projTree t) hclean).batchOpenings)
        { opens := hrel'
          batchOpenings := (hbatch (projTree t) hclean).batchOpenings
          decodedColumns := decodedCols_spec (hbatch (projTree t) hclean).batchOpenings
          satisfiesCircuit := hsat })
    · exact Or.inr (hasNontrivialRelation_of_two_openings urs hw
        ((hbatch (projTree t) hclean).opens.1.trans hrel'.1.symm))
  · exact Or.inr hrel

open Polynomial in
/-- The decoded-column deployed capstone consuming one multiopen-forking output. This is the tighter
closure surface for the witness-to-columns bridge: the caller supplies the deployed IPA tree, halo2's
accept for it, and the batch openings for that same tree as one object — obtained from the forking
bridge as `hForkBatch (deployedAccepts_verifierEq …)` with
`hForkBatch : FiatShamirMultiopenForking …` — instead of a separate witness-indexed decode function.
The output's batch `witness` is identified with the transcript's own extracted witness (a mismatch
collides on `commit` and yields the relation branch), and `hquot`/`hgood` are stated for the canonical
decode of the output's batch. -/
theorem orchard_verifier_deployed_decoded_constraint_reduction_of_multiopen_forking
    [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0)
    (out : MultiopenForkingOutput urs hk vk ps ch b z blind columnCommitments columnEvals)
    (hquot : quotientCheck
      (combineGates fixedCols
        (selectedPolys (decodedCols out.rewind.batchOpenings) adviceIndex)
        (selectedPolys (decodedCols out.rewind.batchOpenings) instanceIndex) y gates)
      hpoly deg x)
    (hgood : combineGates fixedCols
          (selectedPolys (decodedCols out.rewind.batchOpenings) adviceIndex)
          (selectedPolys (decodedCols out.rewind.batchOpenings) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
          (selectedPolys (decodedCols out.rewind.batchOpenings) adviceIndex)
          (selectedPolys (decodedCols out.rewind.batchOpenings) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs (deployedCommitment urs hk vk ps ch) b
        (multiopenValue vk ps ch) columnCommitments columnEvals adviceIndex instanceIndex fixedCols
        y gates hpoly deg a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind out.tree out.accepts with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree out.tree) hclean
    by_cases hw : out.rewind.witness = a
    · subst hw
      have hsat : circuitSatViaGates fixedCols
          (selectedPolysDecode (k := urs.k) (decodedCols out.rewind.batchOpenings) adviceIndex)
          (selectedPolysDecode (k := urs.k) (decodedCols out.rewind.batchOpenings) instanceIndex)
          y gates hpoly deg out.rewind.witness :=
        circuitSatViaGates_of_check fixedCols
          (selectedPolysDecode (k := urs.k) (decodedCols out.rewind.batchOpenings) adviceIndex)
          (selectedPolysDecode (k := urs.k) (decodedCols out.rewind.batchOpenings) instanceIndex)
          y gates hpoly deg out.rewind.witness x hquot hgood
      exact Or.inl (hencodes out.rewind.witness (decodedCols out.rewind.batchOpenings)
        { opens := hrel'
          batchOpenings := out.rewind.batchOpenings
          decodedColumns := decodedCols_spec out.rewind.batchOpenings
          satisfiesCircuit := hsat })
    · exact Or.inr (hasNontrivialRelation_of_two_openings urs hw
        (out.rewind.opens.1.trans hrel'.1.symm))
  · exact Or.inr hrel

end Zcash.Snark
