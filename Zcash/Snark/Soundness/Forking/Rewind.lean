import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.Forking.Ordering

/-!
# Random-oracle rewinding for the deployed verifier

`ofOracle` and `roChallenges` run the deployed schedule with a random oracle. `reprogramRounds` shows
that changing the oracle at the IPA round prefixes is the same as replacing the round-challenge
vector.

This file covers fixed and staged provers. `Soundness.Forking.Adversary` handles arbitrary queries
and query loss. Identifying Blake2b with the modeled random oracle remains an assumption.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A random-oracle-backed Fiat–Shamir instance: the squeeze *is* the oracle `O`. -/
def ofOracle (O : List (TranscriptElt Fp G) → Fp) : FiatShamir Fp G := ⟨O⟩

/-- Run the deployed challenge schedule with oracle `O`. -/
def roChallenges {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) : Challenges shape.k Fp :=
  deriveChallenges (ofOracle O) init ps

/-! ## Redrawing the round vector *is* reprogramming the deployed oracle

The forking proof replaces the IPA challenge vector. The random-oracle experiment instead changes the
oracle at each round prefix and reruns the schedule. `roChallenges_reprogramRounds` proves these are
the same operation. Distinct, longer round prefixes ensure that earlier challenges are unchanged.
-/

open Classical in
/-- Change the oracle answer at every IPA round prefix to the corresponding value in `χ`. -/
noncomputable def reprogramRounds {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if h : ∃ j : Fin shape.k,
      t = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j
    then χ h.choose else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the round-`j` prefix, the reprogrammed oracle answers `χ j`. -/
theorem reprogramRounds_apply_round {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    (j : Fin shape.k) :
    reprogramRounds O init ps χ
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) = χ j := by
  have hex : ∃ j' : Fin shape.k,
      roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j
        = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j' := ⟨j, rfl⟩
  simp only [reprogramRounds]
  rw [dif_pos hex]
  exact (congrArg χ (roundTranscriptFin_injective _ _ hex.choose_spec)).symm

omit [AddCommGroup G] [Module Fp G] in
/-- Off the round prefixes, the reprogrammed oracle is `O`. -/
theorem reprogramRounds_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    {t : List (TranscriptElt Fp G)}
    (ht : ∀ j : Fin shape.k, t ≠ roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) :
    reprogramRounds O init ps χ t = O t := by
  simp only [reprogramRounds]
  rw [dif_neg]
  rintro ⟨j, hj⟩
  exact ht j hj

omit [AddCommGroup G] [Module Fp G] in
/-- Reprogramming leaves every transcript no longer than the pre-IPA prefix unchanged. -/
theorem reprogramRounds_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≤ (preIpaTranscript init ps).length) :
    reprogramRounds O init ps χ t = O t :=
  reprogramRounds_apply_ne O init ps χ (fun j h => by
    have hlen := congrArg List.length h
    rw [roundTranscriptFin_length] at hlen
    omega)

private theorem Challenges.ext' {k : ℕ} {F : Type*} {c₁ c₂ : Challenges k F}
    (hθ : c₁.theta = c₂.theta) (hβ : c₁.beta = c₂.beta) (hγ : c₁.gamma = c₂.gamma)
    (hy : c₁.y = c₂.y) (hx : c₁.x = c₂.x) (h1 : c₁.x1 = c₂.x1) (h2 : c₁.x2 = c₂.x2)
    (h3 : c₁.x3 = c₂.x3) (h4 : c₁.x4 = c₂.x4) (hξ : c₁.xi = c₂.xi) (hz : c₁.z = c₂.z)
    (hu : c₁.ipaRound = c₂.ipaRound) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

omit [AddCommGroup G] [Module Fp G] in
/-- Rerunning the deployed schedule with `reprogramRounds` replaces only its IPA round vector. -/
theorem roChallenges_reprogramRounds {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp) :
    roChallenges (reprogramRounds O init ps χ) init ps
      = { roChallenges O init ps with ipaRound := χ } := by
  refine Challenges.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
      | (funext j
         show (deriveChallenges (ofOracle (reprogramRounds O init ps χ)) init ps).ipaRound j = χ j
         rw [deriveChallenges_ipaRound_eq]
         exact reprogramRounds_apply_round O init ps χ j)
      | exact reprogramRounds_apply_short O init ps χ (by
          simp only [preIpaTranscript, List.length_append, List.length_cons, List.length_nil]
          omega)

/-! ## Challenge-vector uniformity

For a fixed proof, distinct round prefixes yield a uniform challenge vector. Computed adversaries
instead use the full query experiment in `Soundness.Forking.Adversary`. -/

omit [AddCommGroup G] [Module Fp G] in
/-- Each deployed IPA round challenge is the oracle answer at its round prefix. -/
theorem roChallenges_ipaRound_apply {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (j : Fin shape.k) :
    (roChallenges O init ps).ipaRound j
      = O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) :=
  deriveChallenges_ipaRound_eq (ofOracle O) init ps j

omit [AddCommGroup G] [Module Fp G] in
/-- A uniform random oracle gives a uniform IPA challenge vector at the distinct round prefixes. -/
theorem roChallenges_ipaRound_uniform [DecidableEq G] {shape : Shape}
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) :
    (PMF.uniformOfFintype
        (↥(Set.range (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds)) → Fp)).map
        (fun O j => O (Equiv.ofInjective _
          (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds) j))
      = PMF.uniformOfFintype (Fin shape.k → Fp) :=
  uniformOfFintype_map_eval_injective _
    (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds)

/-! ## Redrawing the batching challenge is reprogramming at the `x₄` squeeze

The multiopen rewinding (`Soundness.Multiopen.Decode`) forks on the batching
challenge: redraw `x₄`, re-run, and collect accepting runs at distinct values. `reprogramX4` is the
one-point analogue of `reprogramRounds` at the sealed `x₄` prefix (`preX4Transcript`,
`deriveChallenges_x4_eq`), and its pointwise apply lemmas (`reprogramX4_apply_x4`/`_short`/`_long`)
give the identification field by field: re-running the deployed schedule under it is exactly the
honest run with `x₄` replaced — every other squeeze input has a different length, so nothing else
moves. Both halves of what the `{ch with x4 := ξ}` runs then owe the terminal capstones are theorems
(`Soundness.Multiopen.Deployed`): the flat-batch power form of the deployed statement in `x₄` is proven
over the fingerprinted grouping's aggregates (`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`),
and the accept-probability step is the single-squeeze counting floor
(`exists_injective_accepting_of_measure`) — the same
seam shape the round-forking ladder carries, extending the IPA-round ordering treatment to the
multiopen squeeze points. -/

open Classical in
/-- Reprogram the oracle at the `x₄` squeeze prefix of the fixed proof string, answering `ξ` there
and `O` elsewhere. -/
noncomputable def reprogramX4 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX4Transcript init ps then ξ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₄` prefix the reprogrammed oracle answers `ξ`. -/
theorem reprogramX4_apply_x4 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp) :
    reprogramX4 O init ps ξ (preX4Transcript init ps) = ξ := by
  simp [reprogramX4]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₄` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX4_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX4Transcript init ps) :
    reprogramX4 O init ps ξ t = O t := by
  simp [reprogramX4, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₄` prefix — every other squeeze input of the deployed
schedule — is untouched by the `x₄` reprogramming. -/
theorem reprogramX4_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX4Transcript init ps).length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_ne O init ps ξ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₄` prefix is untouched (the pre-`x₄` squeeze inputs). -/
theorem reprogramX4_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX4Transcript init ps).length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_length O init ps ξ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₄` prefix is untouched (the `ξ`/`z` and IPA-round inputs). -/
theorem reprogramX4_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX4Transcript init ps).length < t.length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_length O init ps ξ ht.ne'

/-! **From the pointwise reprogramming to the challenge-level identity.** The
lemmas above pin `reprogramX4`'s behaviour at every squeeze input: it answers `ξ` at the `x₄` prefix
(`reprogramX4_apply_x4`) and leaves every other input at `O` (`reprogramX4_apply_short`/`_long`,
since the pre-`x₄` squeeze inputs are strictly shorter than the `x₄` prefix and the `ξ`/`z`/IPA-round
inputs strictly longer — `preIpaTranscript_length_eq_preX4`, `roundTranscriptFin_length`). Composed with
the squeeze seals `deriveChallenges_x{3,4}_eq`, these give, field by field, that running the deployed
schedule under `reprogramX4` reproduces the honest run with `x₄` replaced by `ξ` — i.e. the
`{ch with x4 := ξ}` events the multiopen rewinding ranges over are oracle-reprogramming events, the
multiopen-squeeze analogue of `roChallenges_reprogramRounds` for the IPA rounds.

Packaging this as a single `Challenges`-record equality (as `roChallenges_reprogramRounds` does) is
left implicit: each field projection forces whnf of the entire `deriveChallenges` record, and unlike
the round case the batching challenge's inlined `x₄` prefix makes that packaging prohibitively
expensive to elaborate. Downstream consumers take the per-run accept
facts, not the record identity, so the pointwise lemmas above are the operative form. -/

/-! ## Redrawing the compression challenge is reprogramming at the `x₁` squeeze

The within-set rewinding (`Soundness.Multiopen.Deployed`, the member-column decode) forks one squeeze
earlier: redraw `x₁`, and the rewound prover re-sends the post-`x₁` proof fields — `q′`, `u`, and the
IPA opening (`spliceMultiopen`) — so `x₃`/`x₄`/`ξ`/`z` and the round challenges re-randomize through
their squeeze inputs (which absorb the fresh `q′`/`u`), while everything absorbed before `x₁` — the
column commitments, every claimed evaluation (`adviceEvals_mem_preX1Transcript` and companions), hence
the whole query list and the fingerprinted grouping — is shared across runs. `reprogramX1` is the
one-point reprogramming at the sealed `x₁` prefix (`preX1Transcript`, `deriveChallenges_x1_eq`); as
with `reprogramX4`, the pointwise apply lemmas are the operative form, and the run events the member
decode ranges over are `x1RunChallenges`/`spliceMultiopen` records (`Soundness.Multiopen.Deployed`). -/

open Classical in
/-- Reprogram the oracle at the `x₁` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX1 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX1Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₁` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX1_apply_x1 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX1 O init ps χ (preX1Transcript init ps) = χ := by
  simp [reprogramX1]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₁` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX1_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX1Transcript init ps) :
    reprogramX1 O init ps χ t = O t := by
  simp [reprogramX1, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₁` prefix — every other squeeze input of the deployed
schedule (`preX2Transcript_length_eq` and the chain onward) — is untouched by the `x₁`
reprogramming. -/
theorem reprogramX1_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX1Transcript init ps).length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₁` prefix is untouched (the pre-`x₁` squeeze inputs). -/
theorem reprogramX1_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX1Transcript init ps).length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₁` prefix is untouched (the `x₂`/`x₃`/`x₄`/`ξ`/`z` and
IPA-round inputs — on the rewound run these absorb the spliced post-`x₁` fields, and their lengths
stay strictly beyond the `x₁` prefix). -/
theorem reprogramX1_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX1Transcript init ps).length < t.length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_length O init ps χ ht.ne'

/-! ## Redrawing the interpolation and set-separation challenges: reprogramming at `x₃` and `x₂`

The r-polynomial layer (the claimed-evaluation binding) forks one and two squeezes above the `x₄`
collapse: redraw `x₃` and the rewound prover re-sends the post-`x₃` fields (`u`, the IPA opening) —
the quotient commitment `q′` and the point-set aggregates are absorbed before `x₃`
(`qPrime_mem_preX3Transcript`, the pre-`x₁` commitments), so they are shared across runs while the
claimed set evaluations re-randomize; redraw `x₂` and additionally the interpolation point
re-randomizes, separating the per-set contributions by `x₂`-powers. `reprogramX3`/`reprogramX2` are
the one-point reprogrammings at the sealed prefixes (`preX3Transcript`/`preX2Transcript`,
`deriveChallenges_x3_eq`/`_x2_eq`); as with `reprogramX4`, the pointwise apply lemmas are the
operative form. -/

open Classical in
/-- Reprogram the oracle at the `x₃` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX3 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX3Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₃` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX3_apply_x3 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX3 O init ps χ (preX3Transcript init ps) = χ := by
  simp [reprogramX3]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₃` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX3_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX3Transcript init ps) :
    reprogramX3 O init ps χ t = O t := by
  simp [reprogramX3, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₃` prefix is untouched by the `x₃` reprogramming. -/
theorem reprogramX3_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX3Transcript init ps).length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₃` prefix is untouched (the pre-`x₃` squeeze inputs). -/
theorem reprogramX3_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX3Transcript init ps).length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₃` prefix is untouched (the `x₄`/`ξ`/`z` and IPA-round
inputs). -/
theorem reprogramX3_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX3Transcript init ps).length < t.length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_length O init ps χ ht.ne'

open Classical in
/-- Reprogram the oracle at the `x₂` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX2 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX2Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₂` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX2_apply_x2 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX2 O init ps χ (preX2Transcript init ps) = χ := by
  simp [reprogramX2]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₂` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX2_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX2Transcript init ps) :
    reprogramX2 O init ps χ t = O t := by
  simp [reprogramX2, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₂` prefix is untouched by the `x₂` reprogramming. -/
theorem reprogramX2_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX2Transcript init ps).length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₂` prefix is untouched (the pre-`x₂` squeeze inputs,
`preX2Transcript_length_eq` placing `x₁` immediately below). -/
theorem reprogramX2_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX2Transcript init ps).length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₂` prefix is untouched (the `x₃`/`x₄`/`ξ`/`z` and IPA-round
inputs — `preX3Transcript_length_eq` and the chain onward). -/
theorem reprogramX2_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX2Transcript init ps).length < t.length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_length O init ps χ ht.ne'

/-! ## Redrawing the gate-check challenge is reprogramming at the `x` squeeze

The good-challenge derivation (`Soundness.GoodChallenge` and the `_xgood` capstone rungs)
spends an accept measure over the vanishing-check challenge `x`. The runs it ranges over are
reprogramming events at the sealed `x` prefix (`preXTranscript`, `deriveChallenges_x_eq` —
`Soundness.Forking.Ordering`): everything the Schwartz–Zippel difference polynomial is built from —
the column commitments (`adviceCommitments_mem_preXTranscript`) and the quotient pieces
(`hPieces_mem_preXTranscript`) — is absorbed before the `x` squeeze, so the polynomial is pinned
across the rewound runs while `x` alone resamples. As with `reprogramX4`/`reprogramX1`, the pointwise
apply lemmas are the operative form (the pre-`x` squeeze inputs are strictly shorter, the
post-`x` inputs strictly longer — `preXTranscript_length_lt_preX1Transcript` and the length chain
onward). -/

open Classical in
/-- Reprogram the oracle at the `x` squeeze prefix of the fixed proof string, answering `xv` there
and `O` elsewhere. -/
noncomputable def reprogramX {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preXTranscript init ps then xv else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x` prefix the reprogrammed oracle answers `xv`. -/
theorem reprogramX_apply_x {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp) :
    reprogramX O init ps xv (preXTranscript init ps) = xv := by
  simp [reprogramX]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preXTranscript init ps) :
    reprogramX O init ps xv t = O t := by
  simp [reprogramX, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x` prefix — every other squeeze input of the deployed
schedule — is untouched by the `x` reprogramming. -/
theorem reprogramX_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preXTranscript init ps).length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_ne O init ps xv (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x` prefix is untouched (the `θ`/`β`/`γ`/`y` squeeze
inputs). -/
theorem reprogramX_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preXTranscript init ps).length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_length O init ps xv ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x` prefix is untouched (the compression, multiopen, `ξ`/`z`,
and IPA-round inputs — `preXTranscript_length_lt_preX1Transcript` and the length chain onward). -/
theorem reprogramX_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preXTranscript init ps).length < t.length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_length O init ps xv ht.ne'

open scoped ENNReal in
open Classical in
/-- A lower bound on deployed acceptance also bounds the explicit verifier-equation event. -/
theorem kerr_lt_verifierEq_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (psf : (Fin shape.k → Fp) → ProofString shape Fp G)
    (chf : (Fin shape.k → Fp) → Challenges shape.k Fp) {ε : ℝ≥0∞}
    (h : ε < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ => DeployedAccepts urs hk vk instanceCommitment (psf χ) (chf χ)))) :
    ε < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ =>
          DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment (psf χ) (chf χ))) := by
  refine lt_of_lt_of_le h ((PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure.mono ?_)
  intro χ hχ
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
  exact deployedAccepts_verifierEq urs hk vk instanceCommitment (psf χ) (chf χ) hχ

/-! ## Deployed forking opening

Unshifting and unblinding convert the forked tree into the multiopen commitment opening. -/

/-- Compute an opening or relation, shifting the value by the declared `U` coefficient. -/
def deployed_forking_relation_shifted [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z vU blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : DForkCert Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
        (commit urs aDep + vU • urs.u + blind • urs.w) cert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v + z⁻¹ * vU - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  have hvalid' : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * (z⁻¹ * vU)) • urs.u + blind • urs.w) cert := by
    rwa [mul_inv_cancel_left₀ hz]
  match deployed_forking_tree hz urs.g b aDep (z⁻¹ * vU) blind cert hvalid' with
  | .inl ⟨blind', t, ht⟩ =>
      if hclean : IpaAcceptV urs.g b (commit urs aDep) (z⁻¹ * vU) (projTree t) then
        match ipaRelation_extract urs b (commit urs aDep) (z⁻¹ * vU) (projTree t) hclean with
        | ⟨a, ha⟩ =>
            PSum.inl ⟨_, by
              have h1 := ipaRelation_unshift_value urs (commit urs aDep + v • urs.g 0) b v
                (z⁻¹ * vU) a hb0 (by rw [add_sub_cancel_right]; exact ha)
              have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
                rw [hP]; abel
              rw [h2] at h1
              have h3 := ipaRelation_unblind_value urs (commit urs aMulti) b (z⁻¹ * vU + v) ξ s _ h1
              exact ⟨h3.1, h3.2.trans (by ring)⟩⟩
      else
        PSum.inr (NontrivialRelation.ofDeployedTree hz urs.g b (commit urs aDep) (z⁻¹ * vU)
          blind' t ht hclean)
  | .inr hrel => PSum.inr hrel

/-- Compute an opening or relation when the whole commitment has no `U` component. -/
def deployed_forking_relation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : DForkCert Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  match deployed_forking_relation_shifted urs b v ξ z (z * 0) blind aMulti aDep s cert
      hz hb0 hP hvalid with
  | .inl ⟨a, ha⟩ => PSum.inl ⟨a, ha.1, ha.2.trans (by ring)⟩
  | .inr hrel => PSum.inr hrel

/-! ## Propositional extraction

This legacy path turns high acceptance into a fork certificate. The executable adversary path is in
`Soundness.Forking.Adversary.Algebraic`. -/

open scoped ENNReal in
open Classical in
/-- Componentwise inversion preserves the uniform measure on challenge vectors. -/
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
/-- If a nonzero blinding shift is fixed before uniform `ξ`, it hits any target with probability at
most `1 / |Fp|`. -/
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

/-- The accept condition along one path using halo2's inverse-challenge generator fold. -/
def flatAccept : {d : ℕ} → Prover Fp G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → Fp) → (U W : G) → (z : Fp) →
    G → (Fin d → Fp) → Prop
  | 0, .leaf c f, g, b, U, W, z, Pwhole, _ =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, .node L R cont, g, b, U, W, z, Pwhole, χ =>
      flatAccept (cont (χ 0)) (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹) U W z
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-- Swap each round point and invert each challenge to change fold conventions. -/
def invProver : {d : ℕ} → Prover Fp G d → Prover Fp G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node R L (fun u => invProver (cont u⁻¹))

omit [AddCommGroup G] [Module Fp G] in
/-- `invProver` is an involution. -/
theorem invProver_invProver : {d : ℕ} → (P : Prover Fp G d) → invProver (invProver P) = P
  | 0, .leaf _ _ => rfl
  | _ + 1, .node L R cont => by
      simp only [invProver]
      congr 1
      funext u
      rw [inv_inv, invProver_invProver (cont u)]

/-- `proverAccept` equals `flatAccept` after swapping round points and inverting challenges. -/
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
/-- `proverAccept` and `flatAccept` have equal probability under uniform challenges. -/
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
/-- Legacy opening-or-relation result from high acceptance of an abstract prover strategy. -/
noncomputable def legacy_deployed_forking_soundness [DecidableEq G] [Inhabited G] (urs : URS G)
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
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  -- `proverAccept_forkValid` yields the certificate behind a `Prop` `∃`; naming it as data (`Classical.choose`)
  -- is what makes this composition `noncomputable` — the honest random-oracle floor (`Forking.Oracle`). The
  -- deterministic `deployed_forking_relation` it wraps is a genuine *computed* reduction returning the opening
  -- as data; here that data is forgotten to `∃` since the certificate itself is only classically obtained.
  have hpf := proverAccept_forkValid P urs.g b
    (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (extractable_of_prob _ hprob)
  rcases deployed_forking_relation urs b v ξ z blind aMulti aDep s hpf.choose hz hb0 hP hpf.choose_spec
    with ⟨a, ha⟩ | r
  · exact PSum.inl ⟨a, ha⟩
  · exact PSum.inr r

open scoped ENNReal in
open Classical in
/-- **Legacy propositional capstone.** State abstract forking soundness using the deployed verifier's
inverse-challenge fold convention. -/
noncomputable def legacy_deployed_forking_soundness_flat [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure
            (Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w)))) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_deployed_forking_soundness urs b v ξ z blind aMulti aDep s (invProver Q) hz hb0 hP ?_
  rw [proverAccept_measure_eq_flatAccept (invProver Q) urs.g b
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w), invProver_invProver Q]
  exact hprob

/-! ## The deterministic prover-to-verifier bridge

This section builds the constant prover strategy represented by a fixed proof and proves that its
`flatAccept` predicate is the deployed verifier equation. The random-oracle adversary experiment and
query loss remain separate.
-/

/-- Build the constant prover strategy encoded by a fixed proof's IPA fields. -/
def proverOfRounds : {d : ℕ} → (Fin d → G × G) → Fp → Fp → Prover Fp G d
  | 0, _, c, f => .leaf c f
  | _ + 1, R, c, f => .node (R 0).1 (R 0).2 (fun _ => proverOfRounds (Fin.tail R) c f)

omit [AddCommGroup G] [Module Fp G] in
/-- A fixed proof's strategy returns round point `R j` at depth `j` on every challenge path. -/
theorem proverRoundPoint_proverOfRounds : {d : ℕ} → (R : Fin d → G × G) → (c f : Fp) →
    (χ : Fin d → Fp) → (j : ℕ) → (hj : j < d) →
    proverRoundPoint (proverOfRounds R c f) χ j = some (R ⟨j, hj⟩)
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, R, _, _, _, 0, hj => by
      show some ((R 0).1, (R 0).2) = some (R ⟨0, hj⟩)
      exact congrArg some (congrArg R (Fin.ext (by simp)))
  | _ + 1, R, c, f, χ, j + 1, hj => by
      show proverRoundPoint (proverOfRounds (Fin.tail R) c f) (Fin.tail χ) j = _
      rw [proverRoundPoint_proverOfRounds (Fin.tail R) c f (Fin.tail χ) j (Nat.lt_of_succ_lt_succ hj)]
      rfl

/-- `foldGens` commutes with reindexing by `Fin.cast`. -/
theorem foldGens_comp_cast {m n : ℕ} (h : n = m) (g : Fin (2 ^ (m + 1)) → G) (u : Fp) :
    foldGens (fun j : Fin (2 ^ (n + 1)) => g (Fin.cast (by rw [h]) j)) u
      = fun i : Fin (2 ^ n) => foldGens g u (Fin.cast (by rw [h]) i) := by
  subst h; rfl

/-- Fold `g` through a `Fin`-indexed challenge vector without dependent casts. -/
def foldAllFin : {d : ℕ} → (Fin d → Fp) → (Fin (2 ^ d) → G) → G
  | 0, _, g => g 0
  | _ + 1, χ, g => foldAllFin (Fin.tail χ) (foldGens g (χ 0)⁻¹)

/-- Reindex `foldAll` along an equality of challenge lists. -/
theorem foldAll_congr_cast {u u' : List Fp} (h : u = u') (g : Fin (2 ^ u.length) → G) :
    foldAll u g = foldAll u' (fun j => g (Fin.cast (by rw [h]) j)) := by
  subst h; rfl

/-- `foldAllFin` equals the deployed list-based `foldAll`. -/
theorem foldAllFin_eq : {d : ℕ} → (χ : Fin d → Fp) → (g : Fin (2 ^ d) → G) →
    foldAllFin χ g = foldAll (List.ofFn χ) (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0
  | 0, _, g => by simp only [foldAllFin]; rfl
  | d + 1, χ, g => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      rw [foldAllFin, foldAllFin_eq (Fin.tail χ) (foldGens g (χ 0)⁻¹), foldAll_congr_cast hchal, foldAll]
      simp only [Fin.cast_cast]
      exact congrArg (fun gen => foldAll (List.ofFn (Fin.tail χ)) gen 0)
        (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-- Reindex `CF` along an equality of challenge lists. -/
theorem CF_congr_chal {u u' : List Fp} (h : u = u') (rounds : List (G × G))
    (g : Fin (2 ^ u.length) → G) (P : G) (c Uc Wc : Fp) (U W : G) :
    CF rounds u g P c Uc U Wc W
      = CF rounds u' (fun j => g (Fin.cast (by rw [h]) j)) P c Uc U Wc W := by
  subst h; rfl

/-- For a fixed proof tree, `flatAccept` is exactly the closed-form verifier equation `CF = 0`. -/
theorem flatAccept_proverOfRounds :
    {d : ℕ} → (R : Fin d → G × G) → (c f : Fp) → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) →
    (U W : G) → (z : Fp) → (P : G) → (χ : Fin d → Fp) →
    (flatAccept (proverOfRounds R c f) g b U W z P χ ↔
      CF (List.ofFn R) (List.ofFn χ)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) P c
          (-(z * c * foldAllFin χ b)) U (-f) W = 0)
  | 0, R, c, f, g, b, U, W, z, P, χ => by
      rw [proverOfRounds, flatAccept]
      simp only [CF]
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

/-- Folding a `Fin`-indexed eval vector gives the flat verifier's `computeB`. -/
theorem foldAllFin_evalVector {d : ℕ} (χ : Fin d → Fp) (x : Fp) :
    foldAllFin χ (evalVector d x) = computeB x (List.ofFn χ) := by
  rw [foldAllFin_eq]
  have hev : (fun j => evalVector d x (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
      = evalVector (List.ofFn χ).length x := by
    funext j; simp only [evalVector, Fin.val_cast]
  rw [hev]
  exact foldAll_evalVector x (List.ofFn χ)

/-- Halo2's deployed IPA verifier equation equals `flatAccept` for the proof's fixed IPA tree. -/
theorem deployedVerifierEq_iff_flatAccept {shape : Shape} [DecidableEq Fp] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    DeployedIpaVerifierEq g w u vk instanceCommitment ps ch ↔
      flatAccept (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF) g (evalVector shape.k ch.x3) u w ch.z
        (deployedIpaCommitment g w u vk instanceCommitment ps ch)
        ch.ipaRound := by
  rw [deployedVerifierEq_cf, flatAccept_proverOfRounds, foldAllFin_evalVector,
    show (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z)
      = -(ch.z * ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound)) from by ring]

/-! ## The staged (round-adaptive) adversary: `hbridge` discharged beyond the constant strategy

The fixed-tree theorem measures one proof over all challenges. A rewound adversary instead supplies
different IPA fields along different challenge paths. `pathData` reads one path, `spliceIpa` inserts
it into the fixed pre-IPA proof, and `deployedVerifierEq_iff_flatAccept_adaptive` proves the same bridge
for any prefix-respecting strategy.
-/

/-- The round points and final opening produced along one strategy path. -/
def pathData : {d : ℕ} → Prover Fp G d → (Fin d → Fp) → (Fin d → G × G) × Fp × Fp
  | 0, .leaf c f, _ => (Fin.elim0, c, f)
  | _ + 1, .node L R cont, χ =>
      (Fin.cons (L, R) (pathData (cont (χ 0)) (Fin.tail χ)).1, (pathData (cont (χ 0)) (Fin.tail χ)).2)

/-- Replace a proof's IPA fields while keeping its pre-IPA fields fixed. -/
def spliceIpa {shape : Shape} (ps : ProofString shape Fp G) (R : Fin shape.k → G × G) (c f : Fp) :
    ProofString shape Fp G :=
  { ps with ipaRounds := R, ipaC := c, ipaF := f }

omit [AddCommGroup G] [Module Fp G] in
/-- Splicing IPA fields leaves all pre-IPA Fiat–Shamir challenges unchanged. -/
theorem roChallenges_spliceIpa_pre {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (R : Fin shape.k → G × G)
    (c f : Fp) (χ : Fin shape.k → Fp) :
    { roChallenges O init (spliceIpa ps R c f) with ipaRound := χ }
      = { roChallenges O init ps with ipaRound := χ } := by
  refine Challenges.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

/-- Along `χ`, an adaptive strategy agrees with the fixed prover built from `pathData P χ`. -/
theorem flatAccept_pathData {U W : G} {z : Fp} : {d : ℕ} → (P : Prover Fp G d) →
    (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) → (Pwhole : G) → (χ : Fin d → Fp) →
    (flatAccept P g b U W z Pwhole χ ↔
      flatAccept (proverOfRounds (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
        g b U W z Pwhole χ)
  | 0, .leaf _ _, _, _, _, _ => Iff.rfl
  | d + 1, .node L R cont, g, b, Pwhole, χ => by
      rw [flatAccept, flatAccept_pathData (cont (χ 0)) (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹)
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ), pathData, proverOfRounds]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [flatAccept]

/-- Halo2's verifier equation on a path-spliced proof equals `flatAccept P` on that path. -/
theorem deployedVerifierEq_iff_flatAccept_adaptive {shape : Shape} [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (P : Prover Fp G shape.k) (χ : Fin shape.k → Fp) :
    DeployedIpaVerifierEq g w u vk instanceCommitment
        (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ} ↔
      flatAccept P g (evalVector shape.k ch.x3) u w ch.z
        (deployedIpaCommitment g w u vk instanceCommitment ps ch) χ := by
  rw [deployedVerifierEq_iff_flatAccept]
  -- Neither the splice nor the challenge update touches a field the adjusted commitment reads.
  have e : deployedIpaCommitment g w u vk instanceCommitment
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ}
      = deployedIpaCommitment g w u vk instanceCommitment ps ch := rfl
  rw [e]
  exact (flatAccept_pathData P g (evalVector shape.k ch.x3)
    (deployedIpaCommitment g w u vk instanceCommitment ps ch) χ).symm

/-! ## Prover-to-verifier bridge

`hbridge` identifies an accept event pointwise with `flatAccept Q`. The constant and adaptive bridge
theorems above establish this identity for the deployed verifier. The executable adversary path uses
the corresponding bridge in `Soundness.Forking.Adversary.Algebraic`.
-/

open scoped ENNReal in
open Classical in
/-- **Legacy propositional capstone.** Derive the deployed opening from a prover strategy, a pointwise
accept-event bridge, and acceptance above the knowledge error. -/
noncomputable def legacy_deployed_forking_soundness_of_bridge [DecidableEq G] [Inhabited G]
    (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_deployed_forking_soundness_flat urs b v ξ z blind aMulti aDep s Q hz hb0 hP ?_
  have hset : Finset.univ.filter accepts
      = Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
          (commit urs aDep + (z * 0) • urs.u + blind • urs.w)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbridge χ
  rwa [hset] at hprob

end Zcash.Snark
