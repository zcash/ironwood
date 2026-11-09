import Zcash.Snark.Soundness.Action.AdaptiveCountReduction
import Zcash.Snark.Soundness.Action.AdaptiveStatementEvent

/-!
# Statistical bad sets of the shared adaptive-count execution

`ComputedAdaptiveActionCountFSFamily` runs one adversary over a transcript domain large enough for
every permitted Action count, and the count is part of its output. On some samples the selected
count's reduction (`AdaptiveCountReduction`) returns no relation although the proof is accepted,
because a challenge of the selected run lands in one of four bad sets (the declaration names call
them surfaces): `z = 0`; a root of one IPA round quadratic; a root of one of the six multiopen and
IPA-shift polynomials; or one of the five Action semantic bad sets, the bad sets of the
statement-level challenges `θ`, `β`, `γ`, `y`, `x` at pre-IPA squeezes 0 to 4, as opposed to the
root bad sets of the six deployed root challenges at squeezes 5 to 10. For a fixed count, each is
priced by one `(Q + 1)` query factor over that family's own table (`AdaptiveStatementEvent`).

This module prices the same four bad sets over the shared table. The ingredients of the
fixed-count argument are reused as they are: the bad sets, their blindness to the answer being
priced, their pointwise bounds, and the query-time decoding of a transcript prefix. What changes
is the oracle domain. At a query point of the shared domain, the count is read off the length of
the transcript: for the Action shape every squeeze length is strictly increasing in the number of
Actions (`countPreIpaLen_injective`), so at most one count's decoder applies at any point, and the
shared bad set at a point is that count's fixed-count bad set over the table narrowed to the
count's own domain. The per-query union bound
(`LabeledOracleComp.finalBadWithoutRelation_measure_le`) then applies to the shared adversary
directly, with its own query budget `Q`. The count enters the bound only through the largest
shape: the root budgets are monotone in the number of Actions, so every count is priced at
`maxActions`, and the caller's semantic bounds are taken uniform over the counts.

`selectedStatisticalFailureEvent_prob_le` is the result. Under the uniform scalar basis and the
uniform shared table, the selected statistical failure event has probability at most

`(Q + 1) · (1/|Fp| + k·(2/|Fp|) + algebraicRootBudget (shape at maxActions) k + Σₙ ε_semantic n)`,

where `ε_semantic n` bounds the semantic bad set at squeeze `n` for every count.
-/

namespace Zcash.Snark

open Classical Halo2
open Zcash.Common
open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal
open ComputedAdaptiveActionStatementFSFamily (adaptiveActionSurfaceAtOf decodeStatementIpaPrefix?)

local instance adaptiveCountSurfacesVestaInhabited : Inhabited VestaG := ⟨0⟩

/-! ## Squeeze lengths decode the count -/

/-- The verifier shape at count `c`, which stands for `c + 1` Actions. -/
abbrev countShape {maxActions : ℕ} (c : Fin maxActions) : Shape :=
  AdaptiveActionStatementShape (adaptiveActionCountParams c)

/-- The verifier shape at the largest permitted count. -/
abbrev maxCountShape (maxActions : ℕ) : Shape :=
  AdaptiveActionStatementShape (actionProofParamsFor maxActions)

/-- The transcript length of pre-IPA squeeze `n` at count `c`. -/
abbrev countPreIpaLen {maxActions : ℕ} (c : Fin maxActions) (n : Fin 11) : ℕ :=
  preIpaLen (countShape c) (adaptiveStatementInitLength (countShape c)) n

/-- The transcript length of IPA round `j` at count `c`. -/
abbrev countIpaRoundLen {maxActions : ℕ} (c : Fin maxActions)
    (j : Fin actionCircuit.shape.k) : ℕ :=
  countPreIpaLen c 10 + 3 * (j.val + 1)

/-- Every pre-IPA squeeze length of the Action shape is strictly increasing in the number of
Actions: the first squeeze absorbs one instance commitment and ten advice commitments per Action,
and each later squeeze adds a nondecreasing amount. So a transcript's length determines the count
whose squeeze it can be. -/
theorem actionPreIpaLen_injective (n : Fin 11) {a b : ℕ}
    (h : preIpaLen (AdaptiveActionStatementShape (actionProofParamsFor a))
        (adaptiveStatementInitLength (AdaptiveActionStatementShape (actionProofParamsFor a))) n =
      preIpaLen (AdaptiveActionStatementShape (actionProofParamsFor b))
        (adaptiveStatementInitLength (AdaptiveActionStatementShape (actionProofParamsFor b))) n) :
    a = b := by
  simp only [AdaptiveActionStatementShape, actionShapeFor_eq_fixtureShape, preIpaLen,
    adaptiveStatementInitLength] at h
  fin_cases n <;> simp [Zcash.Snark.Fixture.shape] at h <;> omega

/-- `actionPreIpaLen_injective` for count indices. -/
theorem countPreIpaLen_injective {maxActions : ℕ} (n : Fin 11) {a b : Fin maxActions}
    (h : countPreIpaLen a n = countPreIpaLen b n) : a = b :=
  Fin.ext (Nat.succ_injective (actionPreIpaLen_injective n h))

/-- `actionPreIpaLen_injective` for the IPA round lengths, which add `3 (j + 1)` to the last
pre-IPA length. -/
theorem countIpaRoundLen_injective {maxActions : ℕ} (j : Fin actionCircuit.shape.k)
    {a b : Fin maxActions} (h : countIpaRoundLen a j = countIpaRoundLen b j) : a = b :=
  countPreIpaLen_injective 10 (Nat.add_right_cancel h)

/-- The pre-IPA squeeze lengths increase with the round, so the last one bounds them all. -/
theorem preIpaLen_le_ten (shape : Shape) (n₀ : ℕ) (n : Fin 11) :
    preIpaLen shape n₀ n ≤ preIpaLen shape n₀ 10 := by
  rcases Nat.lt_or_ge (n : ℕ) 10 with hlt | hge
  · exact le_of_lt (preIpaLen_lt_at shape n₀ (n := 10) hlt)
  · have : n = 10 := Fin.ext (by omega)
    subst this
    exact le_rfl

/-! ## Points of one count's domain inside the shared domain -/

/-- Widening never changes the transcript, so it is injective. -/
theorem widenAdaptiveActionCountTranscript_injective {maxActions : ℕ} (c : Fin maxActions) :
    Function.Injective (widenAdaptiveActionCountTranscript c) := fun s s' h =>
  Subtype.ext (by simpa only [widenAdaptiveActionCountTranscript_val] using congrArg Subtype.val h)

/-- A shared-domain transcript that fits count `c`'s bounded domain, as a point of that domain. -/
def narrowAtLimit {maxActions : ℕ} (c : Fin maxActions)
    (t : AdaptiveActionCountTranscript maxActions)
    (hlen : t.val.length ≤ adaptiveActionCountTranscriptLimit (c + 1)) :
    AdaptiveActionStatementTranscript (adaptiveActionCountParams c) :=
  ⟨t.val, by
    rw [adaptiveActionStatementTranscriptLimit_eq]
    exact hlen⟩

/-- Every pre-IPA squeeze of count `c` fits count `c`'s bounded domain. -/
theorem countPreIpaLen_le_limit {maxActions : ℕ} (c : Fin maxActions) (n : Fin 11) :
    countPreIpaLen c n ≤ adaptiveActionCountTranscriptLimit (c + 1) := by
  rw [← adaptiveActionStatementTranscriptLimit_eq]
  exact le_trans (preIpaLen_le_ten _ _ n) (Nat.le_add_right _ _)

/-- Every IPA round squeeze of count `c` fits count `c`'s bounded domain. -/
theorem countIpaRoundLen_le_limit {maxActions : ℕ} (c : Fin maxActions)
    (j : Fin actionCircuit.shape.k) :
    countIpaRoundLen c j ≤ adaptiveActionCountTranscriptLimit (c + 1) := by
  rw [← adaptiveActionStatementTranscriptLimit_eq]
  have hj := j.isLt
  simp only [countIpaRoundLen, countPreIpaLen, countShape, adaptiveActionCountParams,
    AdaptiveActionStatementShape, Halo2.CircuitShape.withProofParams_k] at hj ⊢
  omega

/-- A shared-domain transcript with the length of pre-IPA squeeze `n` at count `c`, as a point of
count `c`'s domain. The fitting proof is the named lemma, not an inlined tactic term, so that
definitional comparisons through this point stay cheap. -/
def narrowAtPreIpaLen {maxActions : ℕ} (c : Fin maxActions) (n : Fin 11)
    (t : AdaptiveActionCountTranscript maxActions) (hlen : t.val.length = countPreIpaLen c n) :
    AdaptiveActionStatementTranscript (adaptiveActionCountParams c) :=
  narrowAtLimit c t (hlen ▸ countPreIpaLen_le_limit c n)

/-- A shared-domain transcript with the length of IPA round `j` at count `c`, as a point of count
`c`'s domain. -/
def narrowAtIpaRoundLen {maxActions : ℕ} (c : Fin maxActions) (j : Fin actionCircuit.shape.k)
    (t : AdaptiveActionCountTranscript maxActions) (hlen : t.val.length = countIpaRoundLen c j) :
    AdaptiveActionStatementTranscript (adaptiveActionCountParams c) :=
  narrowAtLimit c t (hlen ▸ countIpaRoundLen_le_limit c j)

@[simp] theorem widen_narrowAtLimit {maxActions : ℕ} (c : Fin maxActions)
    (t : AdaptiveActionCountTranscript maxActions)
    (hlen : t.val.length ≤ adaptiveActionCountTranscriptLimit (c + 1)) :
    widenAdaptiveActionCountTranscript c (narrowAtLimit c t hlen) = t :=
  Subtype.ext rfl

@[simp] theorem widen_narrowAtPreIpaLen {maxActions : ℕ} (c : Fin maxActions) (n : Fin 11)
    (t : AdaptiveActionCountTranscript maxActions) (hlen : t.val.length = countPreIpaLen c n) :
    widenAdaptiveActionCountTranscript c (narrowAtPreIpaLen c n t hlen) = t :=
  Subtype.ext rfl

@[simp] theorem widen_narrowAtIpaRoundLen {maxActions : ℕ} (c : Fin maxActions)
    (j : Fin actionCircuit.shape.k) (t : AdaptiveActionCountTranscript maxActions)
    (hlen : t.val.length = countIpaRoundLen c j) :
    widenAdaptiveActionCountTranscript c (narrowAtIpaRoundLen c j t hlen) = t :=
  Subtype.ext rfl

/-- Reprogramming the shared table at a point of count `c`'s domain reprograms the narrowed table
at that point. -/
theorem update_comp_widen {maxActions : ℕ} (c : Fin maxActions)
    (O : AdaptiveActionCountTranscript maxActions → Fp)
    (s : AdaptiveActionStatementTranscript (adaptiveActionCountParams c)) (v : Fp) :
    Function.update O (widenAdaptiveActionCountTranscript c s) v ∘
        widenAdaptiveActionCountTranscript c =
      Function.update (O ∘ widenAdaptiveActionCountTranscript c) s v := by
  funext s'
  simp only [Function.comp_apply, Function.update_apply]
  by_cases h : s' = s
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (widenAdaptiveActionCountTranscript_injective c h'))]

/-- `update_comp_widen` at a shared point known to be the widening of `s`. -/
theorem update_comp_widen_of_eq {maxActions : ℕ} (c : Fin maxActions)
    (O : AdaptiveActionCountTranscript maxActions → Fp)
    {t : AdaptiveActionCountTranscript maxActions}
    {s : AdaptiveActionStatementTranscript (adaptiveActionCountParams c)}
    (hs : widenAdaptiveActionCountTranscript c s = t) (v : Fp) :
    Function.update O t v ∘ widenAdaptiveActionCountTranscript c =
      Function.update (O ∘ widenAdaptiveActionCountTranscript c) s v := by
  subst hs
  exact update_comp_widen c O s v

/-- An annotation of a shared point, read as an annotation of the same transcript in a count's
own domain. -/
def narrowLabel {maxActions : ℕ} {basis : AdaptiveActionCountBasis} {c : Fin maxActions}
    {t : AdaptiveActionCountTranscript maxActions}
    (s : AdaptiveActionStatementTranscript (adaptiveActionCountParams c)) (hs : s.val = t.val)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) :
    AlgebraicTranscriptQuery (F := Fp) basis s :=
  { representedPoints := label.representedPoints
    points_eq := by
      rw [hs]
      exact label.points_eq }

/-- Selecting representations through a narrowed annotation selects the same ones: the selection
reads only the represented points. -/
theorem narrowLabel_representationsFor {maxActions : ℕ} {basis : AdaptiveActionCountBasis}
    {c : Fin maxActions} {t : AdaptiveActionCountTranscript maxActions}
    (s : AdaptiveActionStatementTranscript (adaptiveActionCountParams c)) (hs : s.val = t.val)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (final : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints s.val)
    (hcovered' : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    (narrowLabel s hs label).representationsFor final hcovered =
      label.representationsFor final hcovered' := by
  induction final with
  | nil => rfl
  | cons ap rest ih =>
      simp only [AlgebraicTranscriptQuery.representationsFor]
      congr 1
      exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))
        (fun candidate hmem => hcovered' candidate (by simp [hmem]))

/-- Pinned data at a shared point is pinned data at the narrowed point. -/
theorem SelectedQueryRepresentationFixed.narrow {maxActions : ℕ} {basis : AdaptiveActionCountBasis}
    {c : Fin maxActions} {t : AdaptiveActionCountTranscript maxActions}
    {label : AlgebraicTranscriptQuery (F := Fp) basis t}
    {final : List (AlgebraicPoint (F := Fp) basis)}
    (fixed : SelectedQueryRepresentationFixed t label final)
    (s : AdaptiveActionStatementTranscript (adaptiveActionCountParams c)) (hs : s.val = t.val) :
    SelectedQueryRepresentationFixed s (narrowLabel s hs label) final :=
  ⟨fun ap hap => by
      rw [hs]
      exact fixed.covered ap hap,
    by
      rw [narrowLabel_representationsFor s hs label final _ fixed.covered]
      exact fixed.coefficients_eq⟩

/-! ## Unions over the counts -/

/-- A union over the counts of sets blind at the narrowed point is blind at the shared point. -/
theorem iUnion_narrow_update_self {maxActions : ℕ} {P : Fin maxActions → Prop}
    (t : AdaptiveActionCountTranscript maxActions)
    (narrow : (c : Fin maxActions) → P c →
      AdaptiveActionStatementTranscript (adaptiveActionCountParams c))
    (hnarrow : ∀ c h, widenAdaptiveActionCountTranscript c (narrow c h) = t)
    (S : (c : Fin maxActions) → P c →
      (AdaptiveActionStatementTranscript (adaptiveActionCountParams c) → Fp) → Set Fp)
    (hblind : ∀ c h table v, S c h (Function.update table (narrow c h) v) = S c h table)
    (O : AdaptiveActionCountTranscript maxActions → Fp) (v : Fp) :
    (⋃ c, ⋃ h, S c h (Function.update O t v ∘ widenAdaptiveActionCountTranscript c)) =
      ⋃ c, ⋃ h, S c h (O ∘ widenAdaptiveActionCountTranscript c) := by
  refine Set.iUnion_congr fun c => Set.iUnion_congr fun h => ?_
  rw [update_comp_widen_of_eq c O (hnarrow c h) v, hblind c h]

/-- A union over the counts, each member available only at its own squeeze length, has at most
one member, so its measure is at most the members' common bound. -/
theorem iUnion_length_measure_le {maxActions : ℕ} (len : Fin maxActions → ℕ)
    (hlen : ∀ {a b : Fin maxActions}, len a = len b → a = b) (L : ℕ)
    (S : (c : Fin maxActions) → L = len c → Set Fp) {ε_set : ENNReal}
    (hS : ∀ c h, uniformChallenge.toOuterMeasure (S c h) ≤ ε_set) :
    uniformChallenge.toOuterMeasure (⋃ c, ⋃ h, S c h) ≤ ε_set := by
  by_cases hex : ∃ c, L = len c
  · obtain ⟨c₀, h₀⟩ := hex
    refine le_trans (MeasureTheory.measure_mono fun x hx => ?_) (hS c₀ h₀)
    obtain ⟨c, h, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain rfl : c = c₀ := hlen (h.symm.trans h₀)
    exact hx
  · have hempty : (⋃ c, ⋃ h, S c h) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨c, h, _⟩ := Set.mem_iUnion₂.mp hx
      exact hex ⟨c, h⟩
    rw [hempty]
    simp

/-- A set available under one condition has the measure of that set, or is empty. -/
theorem iUnion_prop_measure_le {P : Prop} (S : P → Set Fp) {ε_set : ENNReal}
    (hS : ∀ h, uniformChallenge.toOuterMeasure (S h) ≤ ε_set) :
    uniformChallenge.toOuterMeasure (⋃ h, S h) ≤ ε_set := by
  by_cases h : P
  · exact le_trans (MeasureTheory.measure_mono (Set.iUnion_subset fun _ => subset_rfl)) (hS h)
  · have hempty : (⋃ h, S h) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨h', _⟩ := Set.mem_iUnion.mp hx
      exact h h'
    rw [hempty]
    simp

namespace ComputedAdaptiveActionCountFSFamily

variable {maxActions : ℕ} (family : ComputedAdaptiveActionCountFSFamily maxActions)
  (basis : AdaptiveActionCountBasis)

/-! ## The selected output and its own query points -/

/-- The output of the retained shared execution. -/
abbrev selectedOutput (O : family.Coins) :
    AdaptiveActionCountOutput maxActions family.components basis :=
  (family.cachedExecution basis O).1

/-- The output's own pre-IPA squeeze point at round `n`, in the shared domain. The selected run
reads its pre-IPA challenge `n` here (`selectedCachedRun`). -/
def selectedPreIpaPoint (out : AdaptiveActionCountOutput maxActions family.components basis)
    (n : Fin 11) : AdaptiveActionCountTranscript maxActions :=
  widenAdaptiveActionCountTranscript out.count
    ((family.components out.count).preIpaPoint basis n out.output)

/-- The output's own IPA round point at round `j`, in the shared domain. -/
def selectedIpaPoint (out : AdaptiveActionCountOutput maxActions family.components basis)
    (j : Fin actionCircuit.shape.k) : AdaptiveActionCountTranscript maxActions :=
  widenAdaptiveActionCountTranscript out.count
    ((family.components out.count).ipaPoint basis j out.output)

/-- The selected run's pre-IPA challenges are the shared table's answers at the output's own
pre-IPA points. -/
theorem selectedCachedRun_pre (O : family.Coins) :
    (family.selectedCachedRun basis O).pre =
      fun n => O (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) := rfl

/-- The selected run's IPA challenges are the shared table's answers at the output's own round
points. -/
theorem selectedCachedRun_rounds (O : family.Coins) :
    (family.selectedCachedRun basis O).rounds =
      fun j => O (family.selectedIpaPoint basis (family.selectedOutput basis O) j) := rfl

/-- The selected pre-IPA point has the squeeze length of its round at its count. -/
theorem selectedPreIpaPoint_length
    (out : AdaptiveActionCountOutput maxActions family.components basis) (n : Fin 11) :
    (family.selectedPreIpaPoint basis out n).val.length = countPreIpaLen out.count n := by
  simp only [selectedPreIpaPoint, widenAdaptiveActionCountTranscript_val,
    ComputedAdaptiveActionStatementFSFamily.preIpaPoint,
    AdaptiveActionStatementOutput.prefixesPre]
  simpa [adaptiveStatementInitLength] using
    (preIpaSqueezePoints_length_eq
      (out.output.init ((family.components out.count).vkTranscriptRepr basis))
      out.output.toAlgebraicWfProof.proof.1 out.output.toAlgebraicWfProof.proof.2 n)

/-- The selected IPA point has the round length of its round at its count. -/
theorem selectedIpaPoint_length
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (j : Fin actionCircuit.shape.k) :
    (family.selectedIpaPoint basis out j).val.length = countIpaRoundLen out.count j := by
  simp only [selectedIpaPoint, widenAdaptiveActionCountTranscript_val,
    ComputedAdaptiveActionStatementFSFamily.ipaPoint, AdaptiveActionStatementOutput.prefixes]
  simpa [adaptiveIpaRoundLen, adaptiveStatementInitLength] using
    (algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen
      (out.output.init ((family.components out.count).vkTranscriptRepr basis))
      out.output.toAlgebraicWfProof j)

/-! ## Budgets at the largest count -/

/-- Every count's query budget is at most the largest count's. -/
theorem queryBudget_countShape_le (c : Fin maxActions) :
    queryBudget (countShape c) ≤ queryBudget (maxCountShape maxActions) := by
  apply queryBudget_mono <;>
    simp only [countShape, maxCountShape, AdaptiveActionStatementShape,
      actionShapeFor_eq_fixtureShape, adaptiveActionCountParams]
  omega

/-- Every count's root budgets are at most the largest count's: the budgets grow with the query
budget and the point-set count, and the latter is the protocol constant five. -/
theorem deployedRootEventBudget_countShape_le (c : Fin maxActions) (i : Fin 6) :
    deployedRootEventBudget (countShape c) i ≤
      deployedRootEventBudget (maxCountShape maxActions) i := by
  have hqb := queryBudget_countShape_le c
  have hpts : (countShape c).numPointSets = (maxCountShape maxActions).numPointSets := rfl
  have hk : (countShape c).k = (maxCountShape maxActions).k := rfl
  unfold deployedRootEventBudget
  rw [hpts, hk]
  split_ifs <;> gcongr

/-! ## The per-query union bound for the shared adversary -/

/-- `LabeledOracleComp.finalBadWithoutRelation_measure_le` for the shared adversary, with the
output read from the retained execution (`selectedOutput`), which is the adversary's output. -/
theorem selectedFinalBadWithoutRelation_table_le {Relation : Type*}
    (xpt : AdaptiveActionCountOutput maxActions family.components basis →
      AdaptiveActionCountTranscript maxActions)
    (finalBad : AdaptiveActionCountOutput maxActions family.components basis →
      AdaptiveActionCountTranscript maxActions → family.Coins → Set Fp)
    (finder : family.Coins → Option Relation)
    (bad : (t : AdaptiveActionCountTranscript maxActions) →
      AlgebraicTranscriptQuery (F := Fp) basis t → family.Coins → Set Fp)
    (fallback : AdaptiveActionCountOutput maxActions family.components basis →
      AdaptiveActionCountTranscript maxActions → family.Coins → Set Fp)
    (hcover : ∀ O,
      let out := family.selectedOutput basis O
      O (xpt out) ∈ finalBad out (xpt out) O → finder O = none →
        O (xpt out) ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          bad fallback (xpt out) O)
    (hbadBlind : ∀ t label O v, bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ out t O v,
      fallback out t (Function.update O t v) = fallback out t O)
    {ε_bad : ENNReal}
    (hbad : ∀ t label O, (PMF.uniformOfFintype Fp).toOuterMeasure (bad t label O) ≤ ε_bad)
    (hfallback : ∀ out t O,
      (PMF.uniformOfFintype Fp).toOuterMeasure (fallback out t O) ≤ ε_bad) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | let out := family.selectedOutput basis O
        O (xpt out) ∈ finalBad out (xpt out) O ∧ finder O = none} ≤
      (family.Q + 1 : ℕ) * ε_bad := by
  have hset : {O : family.Coins | let out := family.selectedOutput basis O
      O (xpt out) ∈ finalBad out (xpt out) O ∧ finder O = none} =
      {O : family.Coins |
        O (xpt ((family.adversary basis).run O)) ∈
          finalBad ((family.adversary basis).run O) (xpt ((family.adversary basis).run O)) O ∧
          finder O = none} := by
    ext O
    simp only [Set.mem_setOf_eq, selectedOutput, cachedExecution_output_eq, runOutput]
  rw [hset]
  refine LabeledOracleComp.finalBadWithoutRelation_measure_le (family.adversary basis) xpt
    finalBad finder bad fallback ?_ hbadBlind hfallbackBlind hbad hfallback
    (family.queryBound basis)
  intro O hmem hnone
  have h := hcover O
    (by simpa only [selectedOutput, cachedExecution_output_eq, runOutput] using hmem) hnone
  simpa only [selectedOutput, cachedExecution_output_eq, runOutput] using h

/-! ## The four bad sets over the shared table -/

/-- The root bad set at a shared point. The count is read off the point's length, and the set is
that count's query-time root bad set (`queriedRootBad`) over the shared table narrowed to the
count's domain; at most one count has a given length (`countPreIpaLen_injective`). -/
noncomputable def sharedQueriedRootBad (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) : Set Fp :=
  ⋃ (c : Fin maxActions) (hlen : t.val.length = countPreIpaLen c n),
    (family.components c).queriedRootBad basis n h5n (narrowAtPreIpaLen c n t hlen)
      (narrowLabel (narrowAtPreIpaLen c n t hlen) rfl label)
      (O ∘ widenAdaptiveActionCountTranscript c)

/-- The root fallback at a shared point for the selected output: the selected count's
final-output root bad set (`outputRootBad`) over the narrowed table, when the point fits that
count's domain. -/
noncomputable def sharedOutputRootBad (n : Fin 11)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) : Set Fp :=
  ⋃ (hlen : t.val.length = countPreIpaLen out.count n),
    (family.components out.count).outputRootBad basis n out.output
      (narrowAtPreIpaLen out.count n t hlen) (O ∘ widenAdaptiveActionCountTranscript out.count)

/-- The semantic bad set at a shared point, by the count its length decodes to
(`queriedSemanticBad`). -/
noncomputable def sharedQueriedSemanticBad (n : Fin 5)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) : Set Fp :=
  ⋃ (c : Fin maxActions) (hlen : t.val.length = countPreIpaLen c (Fin.castLE (by omega) n)),
    (family.components c).queriedSemanticBad basis n
      (narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen)
      (narrowLabel (narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen) rfl label)
      (O ∘ widenAdaptiveActionCountTranscript c)

/-- The semantic fallback at a shared point for the selected output (`outputSemanticBad`). -/
noncomputable def sharedOutputSemanticBad (n : Fin 5)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) : Set Fp :=
  ⋃ (hlen : t.val.length = countPreIpaLen out.count (Fin.castLE (by omega) n)),
    (family.components out.count).outputSemanticBad basis n out.output
      (narrowAtPreIpaLen out.count (Fin.castLE (by omega) n) t hlen)
      (O ∘ widenAdaptiveActionCountTranscript out.count)

/-- The IPA round bad set at a shared point, by the count its length decodes to
(`queriedIpaBad`). -/
noncomputable def sharedQueriedIpaBad (j : Fin actionCircuit.shape.k)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) : Set Fp :=
  ⋃ (c : Fin maxActions) (hlen : t.val.length = countIpaRoundLen c j),
    (family.components c).queriedIpaBad basis j (narrowAtIpaRoundLen c j t hlen)
      (narrowLabel (narrowAtIpaRoundLen c j t hlen) rfl label)
      (O ∘ widenAdaptiveActionCountTranscript c)

/-- The IPA round fallback at a shared point for the selected output
(`outputIpaFallbackBad`). -/
noncomputable def sharedOutputIpaBad (j : Fin actionCircuit.shape.k)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) : Set Fp :=
  ⋃ (hlen : t.val.length = countIpaRoundLen out.count j),
    (family.components out.count).outputIpaFallbackBad basis j out.output
      (narrowAtIpaRoundLen out.count j t hlen) (O ∘ widenAdaptiveActionCountTranscript out.count)

/-! ### Blindness to the answer being priced -/

/-- The root bad set at a shared point does not depend on the table's answer at that point: each
count's set reads only strict earlier prefixes. -/
theorem sharedQueriedRootBad_update_self (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) (v : Fp) :
    family.sharedQueriedRootBad basis n h5n t label (Function.update O t v) =
      family.sharedQueriedRootBad basis n h5n t label O :=
  iUnion_narrow_update_self t (fun c hlen => narrowAtPreIpaLen c n t hlen)
    (fun c hlen => widen_narrowAtPreIpaLen c n t hlen)
    (fun c hlen table => (family.components c).queriedRootBad basis n h5n
      (narrowAtPreIpaLen c n t hlen) (narrowLabel (narrowAtPreIpaLen c n t hlen) rfl label) table)
    (fun c _ table v => (family.components c).queriedRootBad_update_self basis n h5n _ _ table v)
    O v

/-- The root fallback at a shared point does not depend on the table's answer at that point. -/
theorem sharedOutputRootBad_update_self (n : Fin 11)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) (v : Fp) :
    family.sharedOutputRootBad basis n out t (Function.update O t v) =
      family.sharedOutputRootBad basis n out t O := by
  unfold sharedOutputRootBad
  refine Set.iUnion_congr fun hlen => ?_
  rw [update_comp_widen_of_eq out.count O (widen_narrowAtPreIpaLen out.count n t hlen) v,
    (family.components out.count).outputRootBad_update_self]

/-- The semantic bad set at a shared point does not depend on the table's answer at that point. -/
theorem sharedQueriedSemanticBad_update_self (n : Fin 5)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) (v : Fp) :
    family.sharedQueriedSemanticBad basis n t label (Function.update O t v) =
      family.sharedQueriedSemanticBad basis n t label O :=
  iUnion_narrow_update_self t (fun c hlen => narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen)
    (fun c hlen => widen_narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen)
    (fun c hlen table => (family.components c).queriedSemanticBad basis n
      (narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen)
      (narrowLabel (narrowAtPreIpaLen c (Fin.castLE (by omega) n) t hlen) rfl label) table)
    (fun c _ table v =>
      (family.components c).queriedSemanticBad_update_self basis n _ _ table v)
    O v

/-- The semantic fallback at a shared point does not depend on the table's answer at that point. -/
theorem sharedOutputSemanticBad_update_self (n : Fin 5)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) (v : Fp) :
    family.sharedOutputSemanticBad basis n out t (Function.update O t v) =
      family.sharedOutputSemanticBad basis n out t O := by
  unfold sharedOutputSemanticBad
  refine Set.iUnion_congr fun hlen => ?_
  rw [update_comp_widen_of_eq out.count O
    (widen_narrowAtPreIpaLen out.count (Fin.castLE (by omega) n) t hlen) v,
    (family.components out.count).outputSemanticBad_update_self]

/-- The IPA round bad set at a shared point does not depend on the table's answer at that point. -/
theorem sharedQueriedIpaBad_update_self (j : Fin actionCircuit.shape.k)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) (v : Fp) :
    family.sharedQueriedIpaBad basis j t label (Function.update O t v) =
      family.sharedQueriedIpaBad basis j t label O :=
  iUnion_narrow_update_self t (fun c hlen => narrowAtIpaRoundLen c j t hlen)
    (fun c hlen => widen_narrowAtIpaRoundLen c j t hlen)
    (fun c hlen table => (family.components c).queriedIpaBad basis j
      (narrowAtIpaRoundLen c j t hlen)
      (narrowLabel (narrowAtIpaRoundLen c j t hlen) rfl label) table)
    (fun c _ table v => (family.components c).queriedIpaBad_update_self basis j _ _ table v)
    O v

/-- The IPA round fallback at a shared point does not depend on the table's answer at that
point. -/
theorem sharedOutputIpaBad_update_self (j : Fin actionCircuit.shape.k)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) (v : Fp) :
    family.sharedOutputIpaBad basis j out t (Function.update O t v) =
      family.sharedOutputIpaBad basis j out t O := by
  unfold sharedOutputIpaBad
  refine Set.iUnion_congr fun hlen => ?_
  rw [update_comp_widen_of_eq out.count O (widen_narrowAtIpaRoundLen out.count j t hlen) v,
    (family.components out.count).outputIpaFallbackBad_update_self]

/-! ### Pointwise bounds, at the largest count -/

/-- The root bad set at a shared point has measure at most the deployed root budget at the largest
count: at most one count contributes, and the budgets grow with the count. -/
theorem sharedQueriedRootBad_measure_le (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedQueriedRootBad basis n h5n t label O) ≤
      deployedRootEventBudget (maxCountShape maxActions) (adaptiveRootEventIndex n) :=
  iUnion_length_measure_le (fun c => countPreIpaLen c n) (fun h => countPreIpaLen_injective n h)
    t.val.length _ fun c _ =>
      le_trans ((family.components c).queriedRootBad_measure_le basis n h5n _ _ _)
        (deployedRootEventBudget_countShape_le c _)

/-- The root fallback at a shared point has measure at most the deployed root budget at the largest
count. -/
theorem sharedOutputRootBad_measure_le (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedOutputRootBad basis n out t O) ≤
      deployedRootEventBudget (maxCountShape maxActions) (adaptiveRootEventIndex n) :=
  iUnion_prop_measure_le _ fun _ =>
    le_trans ((family.components out.count).outputRootBad_measure_le basis n h5n _ _ _)
      (deployedRootEventBudget_countShape_le _ _)

/-- The semantic bad set at a shared point has measure at most `ε_semantic`, given that bound on
every count's semantic surface at the squeeze. -/
theorem sharedQueriedSemanticBad_measure_le (n : Fin 5) {ε_semantic : ENNReal}
    (hsurface : ∀ (c : Fin maxActions)
      (instanceCommitment : Fin (countShape c).numProofs → ℕ → VestaG)
      (ps : ProofString (countShape c) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin (n : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ ε_semantic)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedQueriedSemanticBad basis n t label O) ≤
      ε_semantic :=
  iUnion_length_measure_le (fun c => countPreIpaLen c (Fin.castLE (by omega) n))
    (fun h => countPreIpaLen_injective _ h) t.val.length _ fun c _ =>
      (family.components c).queriedSemanticBad_measure_le basis n _ _ _ (hsurface c)

/-- The semantic fallback at a shared point has measure at most `ε_semantic`, given that bound on
every count's semantic surface at the squeeze. -/
theorem sharedOutputSemanticBad_measure_le (n : Fin 5) {ε_semantic : ENNReal}
    (hsurface : ∀ (c : Fin maxActions)
      (instanceCommitment : Fin (countShape c).numProofs → ℕ → VestaG)
      (ps : ProofString (countShape c) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin (n : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ ε_semantic)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedOutputSemanticBad basis n out t O) ≤
      ε_semantic :=
  iUnion_prop_measure_le _ fun _ =>
    (family.components out.count).outputSemanticBad_measure_le basis n _ _ _ (hsurface out.count)

/-- The IPA round bad set at a shared point has measure at most `2 / |Fp|`, the Schwartz–Zippel
bound for the round's quadratic. -/
theorem sharedQueriedIpaBad_measure_le (j : Fin actionCircuit.shape.k)
    (t : AdaptiveActionCountTranscript maxActions)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedQueriedIpaBad basis j t label O) ≤
      2 / (Fintype.card Fp : ENNReal) :=
  iUnion_length_measure_le (fun c => countIpaRoundLen c j) (fun h => countIpaRoundLen_injective j h)
    t.val.length _ fun c _ => (family.components c).queriedIpaBad_measure_le basis j _ _ _

/-- The IPA round fallback at a shared point has measure at most `2 / |Fp|`. -/
theorem sharedOutputIpaBad_measure_le (j : Fin actionCircuit.shape.k)
    (out : AdaptiveActionCountOutput maxActions family.components basis)
    (t : AdaptiveActionCountTranscript maxActions) (O : family.Coins) :
    uniformChallenge.toOuterMeasure (family.sharedOutputIpaBad basis j out t O) ≤
      2 / (Fintype.card Fp : ENNReal) :=
  iUnion_prop_measure_le _ fun _ =>
    (family.components out.count).outputIpaFallbackBad_measure_le basis j _ _ _

/-! ### The finder pieces that an empty selected finder leaves empty -/

/-- No selected pre-IPA relation means the selected comparison at each root squeeze is empty. -/
theorem selectedPreIpaRepresentationRelationFinder_none_at (O : family.Coins)
    (hnone : family.selectedPreIpaRepresentationRelationFinder basis O = none)
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ)) :
    family.selectedPreIpaRepresentationRelationAt? basis O n h5n = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  simp only [List.mem_cons, forall_eq_or_imp] at hall
  rcases hall with ⟨h5, h6, h7, h8, h9, h10, -⟩
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · simpa using h5
  · simpa using h6
  · simpa using h7
  · simpa using h8
  · simpa using h9
  · simpa using h10

/-- No selected IPA relation means the selected comparison at each round is empty. -/
theorem selectedIpaRepresentationRelationFinder_none_at (O : family.Coins)
    (hnone : family.selectedIpaRepresentationRelationFinder basis O = none)
    (j : Fin actionCircuit.shape.k) :
    family.selectedIpaRepresentationRelationAt? basis O j = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  apply hall
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- No selected semantic relation means the selected comparison at each semantic squeeze is
empty. -/
theorem selectedSemanticRepresentationRelationFinder_none_at (O : family.Coins)
    (hnone : family.selectedSemanticRepresentationRelationFinder basis O = none) (n : Fin 5) :
    family.selectedSemanticRepresentationRelationAt? basis O n = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  apply hall
  exact List.mem_ofFn.mpr ⟨n, rfl⟩

/-! ### Covers at the selected output's own points -/

/-- At the selected output's own root point, the fallback event is covered by the first
annotation's bad set or the fresh fallback, when the pre-IPA provenance finder found no
relation: a first annotation whose coefficients disagree with the final ones would have been a
relation, so the annotation is pinned and decodes to the output's root surface. -/
theorem sharedRootBad_cover (n : Fin 11) (h5n : 5 ≤ (n : ℕ)) (O : family.Coins)
    (hbad : O (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) ∈
      family.sharedOutputRootBad basis n (family.selectedOutput basis O)
        (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) O)
    (hnone : family.selectedPreIpaRepresentationRelationFinder basis O = none) :
    O (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) ∈
      LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
        (family.sharedQueriedRootBad basis n h5n) (family.sharedOutputRootBad basis n)
        (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  cases hfind : (family.adversary basis).findLabel O
      (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) with
  | none =>
      change _ ∈ family.sharedOutputRootBad basis n (family.runOutput basis O) _ O
      rw [← family.cachedExecution_output_eq basis O]
      exact hbad
  | some label =>
      have hat := family.selectedPreIpaRepresentationRelationFinder_none_at basis O hnone n h5n
      unfold selectedPreIpaRepresentationRelationAt?
        selectedQueryRepresentationRelationFromSharedAnnotations? at hat
      dsimp only at hat
      rw [cachedExecution_annotations_eq,
        selectedQueryRepresentationRelationFromAnnotations?_eq] at hat
      rcases selectedQueryRepresentationRelation?_eq_none _ _ _ _ _ hat with hfresh | pinned
      · exact absurd (hfresh.symm.trans hfind).symm (Option.some_ne_none label)
      · obtain rfl : pinned.query = label := Option.some.inj (pinned.found.symm.trans hfind)
        obtain ⟨hlen, hbad'⟩ := Set.mem_iUnion.mp hbad
        refine Set.mem_iUnion₂.mpr ⟨(family.selectedOutput basis O).count, hlen, ?_⟩
        exact ComputedAdaptiveActionStatementFSFamily.mem_queriedRootBad_of_pinned
          (family.components (family.selectedOutput basis O).count) basis
          (family.selectedOutput basis O).output
          (O ∘ widenAdaptiveActionCountTranscript (family.selectedOutput basis O).count) n h5n
          (narrowLabel _ rfl pinned.query) (pinned.fixed.narrow _ rfl) hbad'

/-- `sharedRootBad_cover` for the semantic squeezes. -/
theorem sharedSemanticBad_cover (n : Fin 5) (O : family.Coins)
    (hbad : O (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
        (Fin.castLE (by omega) n)) ∈
      family.sharedOutputSemanticBad basis n (family.selectedOutput basis O)
        (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
          (Fin.castLE (by omega) n)) O)
    (hnone : family.selectedSemanticRepresentationRelationFinder basis O = none) :
    O (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
        (Fin.castLE (by omega) n)) ∈
      LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
        (family.sharedQueriedSemanticBad basis n) (family.sharedOutputSemanticBad basis n)
        (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
          (Fin.castLE (by omega) n)) O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  cases hfind : (family.adversary basis).findLabel O
      (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
        (Fin.castLE (by omega) n)) with
  | none =>
      change _ ∈ family.sharedOutputSemanticBad basis n (family.runOutput basis O) _ O
      rw [← family.cachedExecution_output_eq basis O]
      exact hbad
  | some label =>
      have hat := family.selectedSemanticRepresentationRelationFinder_none_at basis O hnone n
      unfold selectedSemanticRepresentationRelationAt?
        selectedQueryRepresentationRelationFromSharedAnnotations? at hat
      dsimp only at hat
      rw [cachedExecution_annotations_eq,
        selectedQueryRepresentationRelationFromAnnotations?_eq] at hat
      rcases selectedQueryRepresentationRelation?_eq_none _ _ _ _ _ hat with hfresh | pinned
      · exact absurd (hfresh.symm.trans hfind).symm (Option.some_ne_none label)
      · obtain rfl : pinned.query = label := Option.some.inj (pinned.found.symm.trans hfind)
        obtain ⟨hlen, hbad'⟩ := Set.mem_iUnion.mp hbad
        refine Set.mem_iUnion₂.mpr ⟨(family.selectedOutput basis O).count, hlen, ?_⟩
        exact ComputedAdaptiveActionStatementFSFamily.mem_queriedSemanticBad_of_pinned
          (family.components (family.selectedOutput basis O).count) basis
          (family.selectedOutput basis O).output
          (O ∘ widenAdaptiveActionCountTranscript (family.selectedOutput basis O).count) n
          (narrowLabel _ rfl pinned.query) (pinned.fixed.narrow _ rfl) hbad'

set_option linter.constructorNameAsVariable false in
/-- `sharedRootBad_cover` for the IPA rounds. -/
theorem sharedIpaBad_cover (j : Fin actionCircuit.shape.k) (O : family.Coins)
    (hbad : O (family.selectedIpaPoint basis (family.selectedOutput basis O) j) ∈
      family.sharedOutputIpaBad basis j (family.selectedOutput basis O)
        (family.selectedIpaPoint basis (family.selectedOutput basis O) j) O)
    (hnone : family.selectedIpaRepresentationRelationFinder basis O = none) :
    O (family.selectedIpaPoint basis (family.selectedOutput basis O) j) ∈
      LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
        (family.sharedQueriedIpaBad basis j) (family.sharedOutputIpaBad basis j)
        (family.selectedIpaPoint basis (family.selectedOutput basis O) j) O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  cases hfind : (family.adversary basis).findLabel O
      (family.selectedIpaPoint basis (family.selectedOutput basis O) j) with
  | none =>
      change _ ∈ family.sharedOutputIpaBad basis j (family.runOutput basis O) _ O
      rw [← family.cachedExecution_output_eq basis O]
      exact hbad
  | some label =>
      have hat := family.selectedIpaRepresentationRelationFinder_none_at basis O hnone j
      unfold selectedIpaRepresentationRelationAt?
        selectedQueryRepresentationRelationFromSharedAnnotations? at hat
      dsimp only at hat
      rw [cachedExecution_annotations_eq,
        selectedQueryRepresentationRelationFromAnnotations?_eq] at hat
      rcases selectedQueryRepresentationRelation?_eq_none _ _ _ _ _ hat with hfresh | pinned
      · exact absurd (hfresh.symm.trans hfind).symm (Option.some_ne_none label)
      · obtain rfl : pinned.query = label := Option.some.inj (pinned.found.symm.trans hfind)
        obtain ⟨hlen, hbad'⟩ := Set.mem_iUnion.mp hbad
        refine Set.mem_iUnion₂.mpr ⟨(family.selectedOutput basis O).count, hlen, ?_⟩
        have hs : narrowAtIpaRoundLen (family.selectedOutput basis O).count j
            (family.selectedIpaPoint basis (family.selectedOutput basis O) j) hlen =
            (family.components (family.selectedOutput basis O).count).ipaPoint basis j
              (family.selectedOutput basis O).output := Subtype.ext rfl
        have hdecode := (family.components (family.selectedOutput basis O).count)
          |>.decodeStatementIpaPrefix?_isSome basis (family.selectedOutput basis O).output j
        rw [← hs] at hdecode
        cases hdec : decodeStatementIpaPrefix? j (narrowAtIpaRoundLen
            (family.selectedOutput basis O).count j
            (family.selectedIpaPoint basis (family.selectedOutput basis O) j) hlen) with
        | none => simp [hdec] at hdecode
        | some decoded =>
            rw [ComputedAdaptiveActionStatementFSFamily.queriedIpaBad_eq_output_of_pinned_at
              (family.components (family.selectedOutput basis O).count) basis
              (family.selectedOutput basis O).output
              (O ∘ widenAdaptiveActionCountTranscript (family.selectedOutput basis O).count) j hs
              decoded hdec (narrowLabel _ rfl pinned.query) (pinned.fixed.narrow _ rfl)]
            -- The goal and `hbad'` are the same term. Elaborating a bare hypothesis first
            -- normalizes its type with `whnf` at default transparency, which here unfolds the bad
            -- set to its `if` on the transcript length and tries to compute the selected point;
            -- at reducible transparency the type stays folded and the check is immediate.
            with_reducible exact hbad'

/-! ## The four events over the shared table, and their prices -/

/-- The selected count's `z = 0` slice. -/
def selectedZeroEvent : Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | q.2 (family.selectedPreIpaPoint q.1 (family.selectedOutput q.1 q.2) 10) = 0}

/-- The selected count's IPA round roots, with no round relation found. -/
def selectedIpaEvent : Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | ∃ j : Fin actionCircuit.shape.k,
    let out := family.selectedOutput q.1 q.2
    let t := family.selectedIpaPoint q.1 out j
    q.2 t ∈ family.sharedOutputIpaBad q.1 j out t q.2 ∧
      family.selectedIpaRepresentationRelationFinder q.1 q.2 = none}

/-- The selected count's six root surfaces, with no pre-IPA relation found. -/
def selectedRootEvent : Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | ∃ i : Fin 6,
    let n := deployedRootChallengeIndex i
    let out := family.selectedOutput q.1 q.2
    let t := family.selectedPreIpaPoint q.1 out n
    q.2 t ∈ family.sharedOutputRootBad q.1 n out t q.2 ∧
      family.selectedPreIpaRepresentationRelationFinder q.1 q.2 = none}

/-- The selected count's five Action semantic surfaces, with no semantic relation found. -/
def selectedSemanticEvent : Set (AdaptiveActionCountBasis × family.Coins) :=
  {q | ∃ n : Fin 5,
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let out := family.selectedOutput q.1 q.2
    let t := family.selectedPreIpaPoint q.1 out n11
    q.2 t ∈ family.sharedOutputSemanticBad q.1 n out t q.2 ∧
      family.selectedSemanticRepresentationRelationFinder q.1 q.2 = none}

/-- The union of the four priced events. -/
def selectedSurfaceEvent : Set (AdaptiveActionCountBasis × family.Coins) :=
  family.selectedZeroEvent ∪
    (family.selectedIpaEvent ∪ (family.selectedRootEvent ∪ family.selectedSemanticEvent))

/-- The `z = 0` slice costs one field query, through the shared adversary's own budget. -/
theorem selectedZeroEvent_table_le :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | (basis, O) ∈ family.selectedZeroEvent} ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  have hzero := fsAdvantageFull_zero_slice_le (family.adversary basis).erase
    (fun _ _ _ => True)
    (fun (out : AdaptiveActionCountOutput maxActions family.components basis) i =>
      family.selectedPreIpaPoint basis out i)
    (fun (out : AdaptiveActionCountOutput maxActions family.components basis) j =>
      family.selectedIpaPoint basis out j)
    10 (family.queryBound basis)
  have hset : {O | (basis, O) ∈ family.selectedZeroEvent} =
      {O : family.Coins | fsWinsFull (family.adversary basis).erase (fun _ _ _ => True)
        (fun out i => family.selectedPreIpaPoint basis out i)
        (fun out j => family.selectedIpaPoint basis out j) O ∧
        O (family.selectedPreIpaPoint basis ((family.adversary basis).erase.run O) 10) = 0} := by
    ext O
    simp only [Set.mem_setOf_eq, selectedZeroEvent, fsWinsFull, true_and, selectedOutput,
      cachedExecution_output_eq, runOutput, LabeledOracleComp.run]
  rw [hset]
  exact hzero

/-- Each IPA round root costs `(Q + 1) · 2/|Fp|`; the rounds are summed. -/
theorem selectedIpaEvent_table_le :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | (basis, O) ∈ family.selectedIpaEvent} ≤
      actionCircuit.shape.k * ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) := by
  have hsub : {O | (basis, O) ∈ family.selectedIpaEvent} ⊆
      ⋃ j : Fin actionCircuit.shape.k, {O : family.Coins |
        let out := family.selectedOutput basis O
        let t := family.selectedIpaPoint basis out j
        O t ∈ family.sharedOutputIpaBad basis j out t O ∧
          family.selectedIpaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ j : Fin actionCircuit.shape.k,
        (PMF.uniformOfFintype family.Coins).toOuterMeasure {O : family.Coins |
          let out := family.selectedOutput basis O
          let t := family.selectedIpaPoint basis out j
          O t ∈ family.sharedOutputIpaBad basis j out t O ∧
            family.selectedIpaRepresentationRelationFinder basis O = none} ≤
      ∑ _j : Fin actionCircuit.shape.k,
        ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) := by
          gcongr with j
          exact family.selectedFinalBadWithoutRelation_table_le basis
            (fun out => family.selectedIpaPoint basis out j) (family.sharedOutputIpaBad basis j)
            (family.selectedIpaRepresentationRelationFinder basis)
            (family.sharedQueriedIpaBad basis j) (family.sharedOutputIpaBad basis j)
            (fun O => family.sharedIpaBad_cover basis j O)
            (family.sharedQueriedIpaBad_update_self basis j)
            (family.sharedOutputIpaBad_update_self basis j)
            (family.sharedQueriedIpaBad_measure_le basis j)
            (family.sharedOutputIpaBad_measure_le basis j)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Each root surface costs `(Q + 1)` times its budget at the largest count; the six sum to the
shape budget. -/
theorem selectedRootEvent_table_le :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | (basis, O) ∈ family.selectedRootEvent} ≤
      (family.Q + 1 : ℕ) *
        algebraicRootBudget (maxCountShape maxActions) actionCircuit.shape.k := by
  have hsub : {O | (basis, O) ∈ family.selectedRootEvent} ⊆
      ⋃ i : Fin 6, {O : family.Coins |
        let n := deployedRootChallengeIndex i
        let out := family.selectedOutput basis O
        let t := family.selectedPreIpaPoint basis out n
        O t ∈ family.sharedOutputRootBad basis n out t O ∧
          family.selectedPreIpaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ i : Fin 6, (PMF.uniformOfFintype family.Coins).toOuterMeasure {O : family.Coins |
        let n := deployedRootChallengeIndex i
        let out := family.selectedOutput basis O
        let t := family.selectedPreIpaPoint basis out n
        O t ∈ family.sharedOutputRootBad basis n out t O ∧
          family.selectedPreIpaRepresentationRelationFinder basis O = none} ≤
      ∑ i : Fin 6, (family.Q + 1 : ℕ) *
        deployedRootEventBudget (maxCountShape maxActions) i := by
          gcongr with i
          let n := deployedRootChallengeIndex i
          have h5n : 5 ≤ (n : ℕ) := by
            fin_cases i <;> norm_num [n, deployedRootChallengeIndex]
          simpa only [n, adaptiveRootEventIndex_deployedRootChallengeIndex] using
            family.selectedFinalBadWithoutRelation_table_le basis
              (fun out => family.selectedPreIpaPoint basis out n)
              (family.sharedOutputRootBad basis n)
              (family.selectedPreIpaRepresentationRelationFinder basis)
              (family.sharedQueriedRootBad basis n h5n) (family.sharedOutputRootBad basis n)
              (fun O => family.sharedRootBad_cover basis n h5n O)
              (family.sharedQueriedRootBad_update_self basis n h5n)
              (family.sharedOutputRootBad_update_self basis n)
              (family.sharedQueriedRootBad_measure_le basis n h5n)
              (family.sharedOutputRootBad_measure_le basis n h5n)
    _ = (family.Q + 1 : ℕ) * ∑ i : Fin 6,
        deployedRootEventBudget (maxCountShape maxActions) i := by
          rw [Finset.mul_sum]
    _ ≤ _ := by
      gcongr
      exact deployedRootEventBudget_sum_le (maxCountShape maxActions)

/-- Each semantic surface costs `(Q + 1)` times its bound `ε_semantic n`; the five are summed. -/
theorem selectedSemanticEvent_table_le (ε_semantic : Fin 5 → ENNReal)
    (hsurface : ∀ (c : Fin maxActions) (n : Fin 5)
      (instanceCommitment : Fin (countShape c).numProofs → ℕ → VestaG)
      (ps : ProofString (countShape c) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin (n : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ ε_semantic n) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | (basis, O) ∈ family.selectedSemanticEvent} ≤
      (family.Q + 1 : ℕ) * ∑ n : Fin 5, ε_semantic n := by
  have hsub : {O | (basis, O) ∈ family.selectedSemanticEvent} ⊆
      ⋃ n : Fin 5, {O : family.Coins |
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let out := family.selectedOutput basis O
        let t := family.selectedPreIpaPoint basis out n11
        O t ∈ family.sharedOutputSemanticBad basis n out t O ∧
          family.selectedSemanticRepresentationRelationFinder basis O = none} := by
    rintro O ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ n : Fin 5, (PMF.uniformOfFintype family.Coins).toOuterMeasure {O : family.Coins |
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let out := family.selectedOutput basis O
        let t := family.selectedPreIpaPoint basis out n11
        O t ∈ family.sharedOutputSemanticBad basis n out t O ∧
          family.selectedSemanticRepresentationRelationFinder basis O = none} ≤
      ∑ n : Fin 5, (family.Q + 1 : ℕ) * ε_semantic n := by
        gcongr with n
        exact family.selectedFinalBadWithoutRelation_table_le basis
          (fun out => family.selectedPreIpaPoint basis out (Fin.castLE (by omega) n))
          (family.sharedOutputSemanticBad basis n)
          (family.selectedSemanticRepresentationRelationFinder basis)
          (family.sharedQueriedSemanticBad basis n) (family.sharedOutputSemanticBad basis n)
          (fun O => family.sharedSemanticBad_cover basis n O)
          (family.sharedQueriedSemanticBad_update_self basis n)
          (family.sharedOutputSemanticBad_update_self basis n)
          (family.sharedQueriedSemanticBad_measure_le basis n (fun c => hsurface c n))
          (family.sharedOutputSemanticBad_measure_le basis n (fun c => hsurface c n))
    _ = _ := by rw [Finset.mul_sum]

/-! ## The selected statistical failure event is covered by the four priced events -/

set_option linter.constructorNameAsVariable false in
/-- At the selected output's own round point, the IPA fallback is the selected run's round
quadratic root set. -/
theorem mem_sharedOutputIpaBad_selected (O : family.Coins) (j : Fin actionCircuit.shape.k) :
    O (family.selectedIpaPoint basis (family.selectedOutput basis O) j) ∈
        family.sharedOutputIpaBad basis j (family.selectedOutput basis O)
          (family.selectedIpaPoint basis (family.selectedOutput basis O) j) O ↔
      (family.selectedCachedRun basis O).rounds j ∈
        szBadSet ((family.selectedCachedRun basis O).output.toAlgebraicWfProof
          |>.straightLineIpaRootPolynomial (family.selectedCachedRun basis O).pre
            (family.selectedCachedRun basis O).rounds j) := by
  let out := family.selectedOutput basis O
  let component := family.components out.count
  let table := O ∘ widenAdaptiveActionCountTranscript out.count
  have hfallback := component.outputIpaFallbackBad_eq_szBadSet basis out.output table j
    (family.selectedCachedRun basis O).pre (family.selectedCachedRun basis O).rounds
    (fun _ => rfl) (fun _ => rfl)
  unfold sharedOutputIpaBad
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨_, h⟩
    change table (component.ipaPoint basis j out.output) ∈
      component.outputIpaFallbackBad basis j out.output (component.ipaPoint basis j out.output)
        table at h
    rw [hfallback] at h
    exact h
  · intro h
    refine ⟨family.selectedIpaPoint_length basis out j, ?_⟩
    change table (component.ipaPoint basis j out.output) ∈
      component.outputIpaFallbackBad basis j out.output (component.ipaPoint basis j out.output)
        table
    rw [hfallback]
    exact h

/-- At the selected output's own pre-IPA point, the root fallback is the selected run's root
surface. -/
theorem mem_sharedOutputRootBad_selected (O : family.Coins) (n : Fin 11) :
    O (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) ∈
        family.sharedOutputRootBad basis n (family.selectedOutput basis O)
          (family.selectedPreIpaPoint basis (family.selectedOutput basis O) n) O ↔
      (family.selectedCachedRun basis O).pre n ∈
        (family.components (family.selectedOutput basis O).count).outputRootSurface basis n
          (family.selectedCachedRun basis O).output
          (fun i => (family.selectedCachedRun basis O).pre (i.castLE (le_of_lt n.isLt))) := by
  let out := family.selectedOutput basis O
  let component := family.components out.count
  let table := O ∘ widenAdaptiveActionCountTranscript out.count
  have hfallback := component.outputRootBad_eq_outputRootSurface basis out.output table n
    (family.selectedCachedRun basis O).pre (fun _ => rfl)
  unfold sharedOutputRootBad
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨_, h⟩
    change table (component.preIpaPoint basis n out.output) ∈
      component.outputRootBad basis n out.output (component.preIpaPoint basis n out.output)
        table at h
    rw [hfallback] at h
    exact h
  · intro h
    refine ⟨family.selectedPreIpaPoint_length basis out n, ?_⟩
    change table (component.preIpaPoint basis n out.output) ∈
      component.outputRootBad basis n out.output (component.preIpaPoint basis n out.output) table
    rw [hfallback]
    exact h

/-- At the selected output's own pre-IPA point, the semantic fallback is the selected run's
semantic surface. -/
theorem mem_sharedOutputSemanticBad_selected (O : family.Coins) (n : Fin 5) :
    O (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
        (Fin.castLE (by omega) n)) ∈
        family.sharedOutputSemanticBad basis n (family.selectedOutput basis O)
          (family.selectedPreIpaPoint basis (family.selectedOutput basis O)
            (Fin.castLE (by omega) n)) O ↔
      (family.selectedCachedRun basis O).pre (Fin.castLE (by omega) n) ∈
        (family.components (family.selectedOutput basis O).count).outputSemanticSurface basis n
          (family.selectedCachedRun basis O).output
          (fun i => (family.selectedCachedRun basis O).pre
            (i.castLE (le_of_lt (Fin.castLE (by omega) n : Fin 11).isLt))) := by
  let out := family.selectedOutput basis O
  let component := family.components out.count
  let table := O ∘ widenAdaptiveActionCountTranscript out.count
  have hfallback := component.outputSemanticBad_eq_outputSemanticSurface basis out.output table n
    (family.selectedCachedRun basis O).pre (fun _ => rfl)
  dsimp only at hfallback
  unfold sharedOutputSemanticBad
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨_, h⟩
    change table (component.preIpaPoint basis (Fin.castLE (by omega) n) out.output) ∈
      component.outputSemanticBad basis n out.output
        (component.preIpaPoint basis (Fin.castLE (by omega) n) out.output) table at h
    rw [hfallback] at h
    exact h
  · intro h
    refine ⟨family.selectedPreIpaPoint_length basis out _, ?_⟩
    change table (component.preIpaPoint basis (Fin.castLE (by omega) n) out.output) ∈
      component.outputSemanticBad basis n out.output
        (component.preIpaPoint basis (Fin.castLE (by omega) n) out.output) table
    rw [hfallback]
    exact h

/-- Each of the selected run's four bad sets (`selectedStatisticalSurface`), read at the run's own
points, is the corresponding fallback event, and an empty selected finder leaves every provenance
piece empty. -/
theorem selectedStatisticalFailureEvent_subset :
    family.selectedStatisticalFailureEvent ⊆ family.selectedSurfaceEvent := by
  intro q ⟨hrel, hsurf⟩
  obtain ⟨-, hpreNone, hipaNone, hsemanticNone, -⟩ :=
    (family.selectedProvenanceRelationFinder_eq_none_iff q.1 q.2).1
      (family.selectedRelationFinderWithCalls_none_provenance q.1 q.2 hrel)
  rcases hsurf with hz | ⟨j, hj⟩ | ⟨i, hi⟩ | ⟨n, hn⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl
      ⟨j, (family.mem_sharedOutputIpaBad_selected q.1 q.2 j).mpr hj, hipaNone⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨i, (family.mem_sharedOutputRootBad_selected q.1 q.2 _).mpr hi, hpreNone⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨n, (family.mem_sharedOutputSemanticBad_selected q.1 q.2 n).mpr hn, hsemanticNone⟩))

/-- **The selected statistical failure event, priced over the shared table.** Under the uniform
scalar basis and the uniform shared table, the probability that the selected count's reduction
returns no relation while the selected run lands in one of the four bad sets is at most
`(Q + 1)` times the sum of the four prices, with the root budget and the semantic bounds taken at
the largest count. `Q` is the shared adversary's own query budget; no factor of `maxActions`
appears. -/
theorem selectedStatisticalFailureEvent_prob_le (B : VestaG) (ε_semantic : Fin 5 → ENNReal)
    (hsurface : ∀ (c : Fin maxActions) (basis : AdaptiveActionCountBasis) (n : Fin 5)
      (instanceCommitment : Fin (countShape c).numProofs → ℕ → VestaG)
      (ps : ProofString (countShape c) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin (n : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ ε_semantic n) :
    (PMF.uniformOfFintype ((ActionBasisIndex → Fp) × family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.selectedStatisticalFailureEvent) ≤
      (family.Q + 1 : ℕ) *
        (1 / Fintype.card Fp +
          actionCircuit.shape.k * (2 / (Fintype.card Fp : ENNReal)) +
          algebraicRootBudget (maxCountShape maxActions) actionCircuit.shape.k +
          ∑ n : Fin 5, ε_semantic n) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono family.selectedStatisticalFailureEvent_subset)) ?_
  have hzero : (PMF.uniformOfFintype ((ActionBasisIndex → Fp) × family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.selectedZeroEvent) ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.selectedZeroEvent})
    intro logs
    exact family.selectedZeroEvent_table_le (scalarBasis B logs)
  have hipa : (PMF.uniformOfFintype ((ActionBasisIndex → Fp) × family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.selectedIpaEvent) ≤
      actionCircuit.shape.k * ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.selectedIpaEvent})
    intro logs
    exact family.selectedIpaEvent_table_le (scalarBasis B logs)
  have hroot : (PMF.uniformOfFintype ((ActionBasisIndex → Fp) × family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.selectedRootEvent) ≤
      (family.Q + 1 : ℕ) *
        algebraicRootBudget (maxCountShape maxActions) actionCircuit.shape.k := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.selectedRootEvent})
    intro logs
    exact family.selectedRootEvent_table_le (scalarBasis B logs)
  have hsemantic :
      (PMF.uniformOfFintype ((ActionBasisIndex → Fp) × family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.selectedSemanticEvent) ≤
      (family.Q + 1 : ℕ) * ∑ n : Fin 5, ε_semantic n := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.selectedSemanticEvent})
    intro logs
    exact family.selectedSemanticEvent_table_le (scalarBasis B logs) ε_semantic
      (fun c => hsurface c (scalarBasis B logs))
  unfold selectedSurfaceEvent
  simp only [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine le_trans (add_le_add hzero (MeasureTheory.measure_union_le _ _)) ?_
  refine le_trans (add_le_add_right (add_le_add hipa
    (MeasureTheory.measure_union_le _ _)) _) ?_
  refine le_trans (add_le_add_right (add_le_add_right (add_le_add hroot hsemantic) _) _) ?_
  ring_nf
  exact le_rfl

end ComputedAdaptiveActionCountFSFamily

end Zcash.Snark
