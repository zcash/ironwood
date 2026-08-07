import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Fingerprint.Rational.ConstraintWalk
import Zcash.Snark.Soundness.Deployed.Fold
import Zcash.Snark.Soundness.FiatShamir.Assembly

/-!
# The IPA-side representation walk

The grouping-independent tail of the coefficient walk: the assembled MSM's `gScalars`,
`wScalar`, and `uScalar` components are untouched by the whole multiopen stage — only the final
`ipaFold` writes them — so their closed forms and representations need nothing from the
grouping beyond "the member commitments carry a zero scalar block".

* `Msm.gwuZero` / `CommitmentRef.gwuZero` — the zero-scalar-block predicate, preserved by every
  multiopen accumulator (`appendTerm`/`scale`/`add`, `accumulateCommitment`, `compressSet`,
  `multiopenCombine`, `assembleOpening`) and satisfied by the vanishing `h` MSM, hence by every
  commitment `assembleQueries` emits and — via the grouping's member provenance — by every
  grouped member (`assembleQueries_grouped_gwuZero`), with no good-event hypothesis.
* Closed forms: unconditionally, `assembleFinalMsm`'s scalar block is the opening's block plus
  the IPA fold's contribution (`assembleFinalMsm_wScalar`/`_uScalar`/`_gScalars`); under
  `gwuZero` members the opening's block vanishes and the coefficients are exactly the IPA
  values (`…_of_gwuZero`), and `assembleFinalMsm?` returns the same MSM when it accepts
  (`assembleFinalMsm?_eq_some`).
* Representations: `computeB`/`computeS` fold to polynomials of the round challenges via their
  cons-direction recursions (`computeB_cons`, `computeS_cons`), giving `wScalar` at degree 1,
  `uScalar` at `2^k + k + 3`, every `computeS` entry at `1 + k`, and the `g`-block coordinates
  given a representation of the multiopen opening value (`gScalars_coord_rep` — the opening
  value is the one upstream input, supplied by the multiopen walk).
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)
open MvPolynomial

/-! ## The zero scalar block and its preservation -/

/-- The MSM's generator-coefficient block is zero: `gScalars`, `wScalar`, and `uScalar` all
vanish (the `other` terms are unconstrained). Every multiopen stage preserves this; only the
final `ipaFold` writes the block. -/
def _root_.Zcash.Arithmetic.Msm.gwuZero {k : ℕ} {F G : Type*} [Zero F] (m : Msm k F G) : Prop :=
  (∀ i, m.gScalars i = 0) ∧ m.wScalar = 0 ∧ m.uScalar = 0

/-- A commitment reference carries a zero scalar block: plain points trivially, MSM references
through `Msm.gwuZero`. -/
def CommitmentRef.gwuZero {k : ℕ} {F G : Type*} [Zero F] : CommitmentRef k F G → Prop
  | .point _ => True
  | .msm m => m.gwuZero

theorem gwuZero_zero (k : ℕ) (F G : Type*) [Zero F] : (Msm.zero k F G).gwuZero :=
  ⟨fun _ => rfl, rfl, rfl⟩

theorem gwuZero_appendTerm {k : ℕ} {F G : Type*} [Zero F] {m : Msm k F G}
    (h : m.gwuZero) (c : F) (P : G) : (m.appendTerm c P).gwuZero := h

theorem gwuZero_scale {k : ℕ} {F G : Type*} [MulZeroClass F] {m : Msm k F G}
    (h : m.gwuZero) (c : F) : (m.scale c).gwuZero := by
  obtain ⟨hg, hw, hu⟩ := h
  refine ⟨fun i => ?_, ?_, ?_⟩ <;> simp [Msm.scale, hg, hw, hu]

theorem gwuZero_add {k : ℕ} {F G : Type*} [AddZeroClass F] {m₁ m₂ : Msm k F G}
    (h₁ : m₁.gwuZero) (h₂ : m₂.gwuZero) : (m₁.add m₂).gwuZero := by
  obtain ⟨hg₁, hw₁, hu₁⟩ := h₁
  obtain ⟨hg₂, hw₂, hu₂⟩ := h₂
  refine ⟨fun i => ?_, ?_, ?_⟩ <;> simp [Msm.add, hg₁, hw₁, hu₁, hg₂, hw₂, hu₂]

/-- The vanishing `h` commitment is built from the zero MSM by `scale`/`appendTerm`, so its
scalar block is zero — the one `.msm` commitment the deployed query list contains. -/
theorem vanishingHCommitment_gwuZero {F G : Type*} [Field F] (k : ℕ) (xn : F)
    (hPieces : List G) : (vanishingHCommitment k xn hPieces).gwuZero := by
  rw [vanishingHCommitment]
  have aux : ∀ (l : List G) (m : Msm k F G), m.gwuZero →
      (l.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) m).gwuZero := by
    intro l
    induction l with
    | nil => intro m h; simpa using h
    | cons c t ih =>
        intro m h
        exact ih _ (gwuZero_appendTerm (gwuZero_scale h xn) 1 c)
  exact aux _ _ (gwuZero_zero ..)

theorem accumulateCommitment_gwuZero {k : ℕ} {F G : Type*} [Field F] {pow : F}
    {c : CommitmentRef k F G} {acc : Msm k F G} (hc : c.gwuZero) (hacc : acc.gwuZero) :
    (accumulateCommitment pow c acc).gwuZero := by
  cases c with
  | point p => exact gwuZero_appendTerm hacc pow p
  | msm m => exact gwuZero_add hacc (gwuZero_scale hc pow)

theorem compressSet_gwuZero {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ)
    (h : ∀ mem ∈ setQueries, mem.1.gwuZero) :
    (compressSet x1 setQueries numPoints).1.gwuZero := by
  have aux : ∀ (l : List (CommitmentRef k F G × List F)) (st : Msm k F G × List F × F),
      (∀ mem ∈ l, mem.1.gwuZero) → st.1.gwuZero →
      (l.foldl (fun (st : Msm k F G × List F × F) qc =>
        (accumulateCommitment st.2.2 qc.1 st.1,
         (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
         st.2.2 * x1)) st).1.gwuZero := by
    intro l
    induction l with
    | nil => intro st _ h; simpa using h
    | cons q t ih =>
        intro st hl hst
        exact ih _ (fun mem hm => hl mem (List.mem_cons_of_mem _ hm))
          (accumulateCommitment_gwuZero (hl q List.mem_cons_self) hst)
  exact aux _ _ h (gwuZero_zero ..)

theorem multiopenCombine_gwuZero {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F) (incoming : Msm k F G)
    (hq : ∀ q ∈ qCommitments, q.gwuZero) (hinc : incoming.gwuZero) :
    (multiopenCombine x4 qPrime qCommitments u msmEval incoming).1.gwuZero := by
  have aux : ∀ (l : List (Msm k F G × F)) (st : Msm k F G × F),
      (∀ p ∈ l, p.1.gwuZero) → st.1.gwuZero →
      (l.foldl (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
        st).1.gwuZero := by
    intro l
    induction l with
    | nil => intro st _ h; simpa using h
    | cons p t ih =>
        intro st hl hst
        exact ih _ (fun q hqm => hl q (List.mem_cons_of_mem _ hqm))
          (gwuZero_add (gwuZero_scale hst x4) (hl p List.mem_cons_self))
  refine aux _ _ (fun p hp => ?_) (gwuZero_appendTerm hinc 1 qPrime)
  obtain ⟨q, e⟩ := p
  exact hq q (List.of_mem_zip hp).1

/-- The multiopen opening keeps a zero scalar block whenever every grouped member's commitment
does — the whole multiopen stage never touches `gScalars`/`wScalar`/`uScalar`. -/
theorem assembleOpening_gwuZero {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G)
    (u : List F) (grouped : MultiopenGrouped k F G) (incoming : Msm k F G)
    (h : ∀ s ∈ grouped.sets, ∀ mem ∈ s, mem.1.gwuZero) (hinc : incoming.gwuZero) :
    (assembleOpening x1 x2 x3 x4 qPrime u grouped incoming).1.gwuZero := by
  rw [assembleOpening]
  refine multiopenCombine_gwuZero _ _ _ _ _ _ (fun q hq => ?_) hinc
  simp only [List.map_map, List.mem_map] at hq
  obtain ⟨sp, hsp, rfl⟩ := hq
  obtain ⟨s, p⟩ := sp
  exact compressSet_gwuZero _ _ _ fun mem hm => h s (List.of_mem_zip hsp).1 mem hm

/-! ## Closed forms for the assembled scalar block -/

section ClosedForms

variable {shape : Shape} {F G : Type*} [Field F]

section Projections

variable {k : ℕ} {F' G' : Type*}

@[simp] theorem appendTerm_gScalars (m : Msm k F' G') (c : F') (P : G') :
    (m.appendTerm c P).gScalars = m.gScalars := rfl
@[simp] theorem appendTerm_wScalar (m : Msm k F' G') (c : F') (P : G') :
    (m.appendTerm c P).wScalar = m.wScalar := rfl
@[simp] theorem appendTerm_uScalar (m : Msm k F' G') (c : F') (P : G') :
    (m.appendTerm c P).uScalar = m.uScalar := rfl
@[simp] theorem addToGScalars_wScalar [Add F'] [Zero F'] (m : Msm k F' G') (l : List F') :
    (m.addToGScalars l).wScalar = m.wScalar := rfl
@[simp] theorem addToGScalars_uScalar [Add F'] [Zero F'] (m : Msm k F' G') (l : List F') :
    (m.addToGScalars l).uScalar = m.uScalar := rfl
@[simp] theorem addToGScalars_gScalars [Add F'] [Zero F'] (m : Msm k F' G') (l : List F')
    (i : Fin (2 ^ k)) : (m.addToGScalars l).gScalars i = m.gScalars i + l.getD i.val 0 := rfl
@[simp] theorem addToUScalar_gScalars [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToUScalar c).gScalars = m.gScalars := rfl
@[simp] theorem addToUScalar_wScalar [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToUScalar c).wScalar = m.wScalar := rfl
@[simp] theorem addToUScalar_uScalar [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToUScalar c).uScalar = m.uScalar + c := rfl
@[simp] theorem addToWScalar_gScalars [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToWScalar c).gScalars = m.gScalars := rfl
@[simp] theorem addToWScalar_uScalar [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToWScalar c).uScalar = m.uScalar := rfl
@[simp] theorem addToWScalar_wScalar [Add F'] (m : Msm k F' G') (c : F') :
    (m.addToWScalar c).wScalar = m.wScalar + c := rfl

end Projections

/-- The per-round `L`/`R` fold touches only the `other` terms. -/
theorem foldl_appendTerm_pair_gScalars {k : ℕ} (l : List ((G × G) × F)) (m : Msm k F G) :
    (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m).gScalars
      = m.gScalars := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => exact ih _

/-- The per-round `L`/`R` fold touches only the `other` terms. -/
theorem foldl_appendTerm_pair_wScalar {k : ℕ} (l : List ((G × G) × F)) (m : Msm k F G) :
    (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m).wScalar
      = m.wScalar := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => exact ih _

/-- The per-round `L`/`R` fold touches only the `other` terms. -/
theorem foldl_appendTerm_pair_uScalar {k : ℕ} (l : List ((G × G) × F)) (m : Msm k F G) :
    (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m).uScalar
      = m.uScalar := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => exact ih _

/-- The assembled `w` coefficient, unconditionally: the opening's `wScalar` plus `-ipaF`. -/
theorem assembleFinalMsm_wScalar (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).wScalar
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          grouped (Msm.zero shape.k F G)).1.wScalar + -ps.ipaF := by
  simp only [assembleFinalMsm, ipaFold, addToGScalars_wScalar, addToWScalar_wScalar,
    addToUScalar_wScalar, foldl_appendTerm_pair_wScalar, appendTerm_wScalar]

/-- The assembled `u` coefficient, unconditionally: the opening's `uScalar` plus the IPA
value `-c · b · z`. -/
theorem assembleFinalMsm_uScalar (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).uScalar
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          grouped (Msm.zero shape.k F G)).1.uScalar
        + -ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z := by
  simp only [assembleFinalMsm, ipaFold, addToGScalars_uScalar, addToWScalar_uScalar,
    addToUScalar_uScalar, foldl_appendTerm_pair_uScalar, appendTerm_uScalar]

/-- The assembled `g` coefficients, unconditionally: the opening's entry, plus the opened
value at position `0`, plus the `computeS` folded-generator entry. -/
theorem assembleFinalMsm_gScalars (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) (i : Fin (2 ^ shape.k)) :
    (assembleFinalMsm ps ch grouped).gScalars i
      = ((assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).1.gScalars i
          + [-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
              (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k F G)).2].getD i.val 0)
        + (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD i.val 0 := by
  simp only [assembleFinalMsm, ipaFold, addToGScalars_gScalars, addToWScalar_gScalars,
    addToUScalar_gScalars, foldl_appendTerm_pair_gScalars, appendTerm_gScalars]

/-- Members with zero scalar blocks give the clean `w` coefficient: `-ipaF` exactly. -/
theorem assembleFinalMsm_wScalar_of_gwuZero (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G)
    (h : ∀ s ∈ grouped.sets, ∀ mem ∈ s, mem.1.gwuZero) :
    (assembleFinalMsm ps ch grouped).wScalar = -ps.ipaF := by
  rw [assembleFinalMsm_wScalar,
    (assembleOpening_gwuZero _ _ _ _ _ _ _ _ h (gwuZero_zero ..)).2.1, zero_add]

/-- Members with zero scalar blocks give the clean `u` coefficient: `-c · b · z` exactly. -/
theorem assembleFinalMsm_uScalar_of_gwuZero (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G)
    (h : ∀ s ∈ grouped.sets, ∀ mem ∈ s, mem.1.gwuZero) :
    (assembleFinalMsm ps ch grouped).uScalar
      = -ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z := by
  rw [assembleFinalMsm_uScalar,
    (assembleOpening_gwuZero _ _ _ _ _ _ _ _ h (gwuZero_zero ..)).2.2, zero_add]

/-- Members with zero scalar blocks give the clean `g` coefficients: the opened value at
position `0` plus the `computeS` entry, exactly. -/
theorem assembleFinalMsm_gScalars_of_gwuZero (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G)
    (h : ∀ s ∈ grouped.sets, ∀ mem ∈ s, mem.1.gwuZero) (i : Fin (2 ^ shape.k)) :
    (assembleFinalMsm ps ch grouped).gScalars i
      = [-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).2].getD i.val 0
        + (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD i.val 0 := by
  rw [assembleFinalMsm_gScalars,
    (assembleOpening_gwuZero ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      grouped (Msm.zero shape.k F G) h (gwuZero_zero ..)).1 i, zero_add]

end ClosedForms

/-! ## The deployed query list carries zero scalar blocks -/

section QueryScan

variable {k : ℕ} {F G : Type*} [Field F]

theorem columnQueries_commitment_gwuZero (omega x : F) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F) :
    ∀ q ∈ columnQueries (k := k) omega x commitment mkId layout evals,
      q.commitment.gwuZero := by
  intro q hq
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hq
  trivial

theorem permutationQueries_commitment_gwuZero (x xNext xLast : F) (mkId : ℕ → CommitmentId)
    (sets : List (G × PermSetEval F)) :
    ∀ q ∈ permutationQueries (k := k) x xNext xLast mkId sets, q.commitment.gwuZero := by
  intro q hq
  rw [permutationQueries] at hq
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filterMap] at hq
  rcases hq with ⟨s, _, rfl | rfl⟩ | ⟨s, _, hmap⟩
  · trivial
  · trivial
  · obtain ⟨le, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
    trivial

theorem lookupQueries_commitment_gwuZero (x xInv xNext : F)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval F)) :
    ∀ q ∈ lookupQueries (k := k) x xInv xNext mkProduct mkInput mkTable lookups,
      q.commitment.gwuZero := by
  intro q hq
  rw [lookupQueries] at hq
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
  obtain ⟨l, _, rfl | rfl | rfl | rfl | rfl⟩ := hq <;> trivial

theorem permutationCommonQueries_commitment_gwuZero (x : F) (mkId : ℕ → CommitmentId)
    (commsEvals : List (G × F)) :
    ∀ q ∈ permutationCommonQueries (k := k) x mkId commsEvals, q.commitment.gwuZero := by
  intro q hq
  obtain ⟨ce, _, rfl⟩ := List.mem_map.mp hq
  trivial

theorem vanishingQueries_commitment_gwuZero (x : F) (hCommitment : Msm k F G)
    (expectedHEval : F) (randomPolyCommitment : G) (randomEval : F)
    (hm : hCommitment.gwuZero) :
    ∀ q ∈ vanishingQueries x hCommitment expectedHEval randomPolyCommitment randomEval,
      q.commitment.gwuZero := by
  intro q hq
  rw [vanishingQueries] at hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact hm
  · rcases List.mem_cons.mp hq' with rfl | h
    · trivial
    · exact absurd h List.not_mem_nil

end QueryScan

/-- Every commitment the deployed query list emits has a zero scalar block: the five builders
produce plain points except the vanishing slot's `.msm`, whose MSM is
`vanishingHCommitment` — zero-blocked by construction. No good-event hypothesis. -/
theorem assembleQueries_commitment_gwuZero {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    ∀ q ∈ assembleQueries vk ic ps ch, q.commitment.gwuZero := by
  intro q hq
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · simp only [List.mem_flatten, List.mem_ofFn] at hq
    obtain ⟨block, ⟨p, rfl⟩, hqb⟩ := hq
    simp only [List.mem_append] at hqb
    rcases hqb with ((hqb | hqb) | hqb) | hqb
    · exact columnQueries_commitment_gwuZero _ _ _ _ _ _ q hqb
    · exact columnQueries_commitment_gwuZero _ _ _ _ _ _ q hqb
    · exact permutationQueries_commitment_gwuZero _ _ _ _ _ q hqb
    · exact lookupQueries_commitment_gwuZero _ _ _ _ _ _ _ q hqb
  · exact columnQueries_commitment_gwuZero _ _ _ _ _ _ q hq
  · exact permutationCommonQueries_commitment_gwuZero _ _ _ q hq
  · exact vanishingQueries_commitment_gwuZero _ _ _ _ _
      (vanishingHCommitment_gwuZero _ _ _) q hq

/-- Every grouped member's commitment has a zero scalar block, for any query list whose
commitments do: the grouping's members are drawn from the flat queries
(`constructIntermediateSets_member_provenance`). -/
theorem constructIntermediateSets_member_gwuZero {k : ℕ} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (queries : List (VerifierQuery k F G))
    (hq : ∀ q ∈ queries, q.commitment.gwuZero) :
    ∀ s ∈ (constructIntermediateSets queries).sets, ∀ mem ∈ s, mem.1.gwuZero := by
  intro s hs mem hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hig : (constructIntermediateSets queries).sets[i] =
      (constructIntermediateSets queries).sets.getD i [] := by
    rw [List.getD_eq_getElem _ _ hi]
  have hmg : (constructIntermediateSets queries).sets[i][m] =
      ((constructIntermediateSets queries).sets.getD i []).getD m
        ((constructIntermediateSets queries).sets[i][m]) := by
    rw [← hig, List.getD_eq_getElem]
  obtain ⟨qq, hqq, hcomm, -⟩ := constructIntermediateSets_member_provenance queries i m hi
    (by rw [← hig]; exact hm) ((constructIntermediateSets queries).sets[i][m])
    CommitmentId.vanishingH
  rw [hmg, hcomm]
  exact hq qq hqq

/-- **The deployed grouping's members all carry zero scalar blocks** — unconditional: the flat
queries do, and the grouping draws its members from them. This is the hypothesis the clean
closed forms (`assembleFinalMsm_*_of_gwuZero`) consume at the real pipeline. -/
theorem assembleQueries_grouped_gwuZero {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    ∀ s ∈ (constructIntermediateSets (assembleQueries vk ic ps ch)).sets,
      ∀ mem ∈ s, mem.1.gwuZero :=
  constructIntermediateSets_member_gwuZero _ (assembleQueries_commitment_gwuZero vk ic ps ch)

/-! ## Representations of the IPA-side coefficients -/

section IpaReps

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}

/-- Entry access into a represented list: in range it is a represented entry, past the end the
constant `0`; either way the position is point-independent. -/
theorem ListRep.getD_rep {den : MvPolynomial (ScalarSlot shape) Fp}
    {l : Point shape → List Fp} {d : ℕ} (h : ListRep vk den l d) (i : ℕ) :
    NumeratorRep vk den (fun pt => (l pt).getD i 0) d := by
  obtain ⟨fns, heq, hrep⟩ := h
  by_cases hi : i < fns.length
  · have hval : ∀ pt : Point shape, (l pt).getD i 0 = fns[i] pt := by
      intro pt
      rw [heq pt, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    exact (hrep _ (List.getElem_mem hi)).congr_event fun pt _ => (hval pt).symm
  · have hval : ∀ pt : Point shape, (l pt).getD i 0 = 0 := by
      intro pt
      rw [heq pt]
      exact List.getD_eq_default _ _ (by simpa using hi)
    have h0 : NumeratorRep vk den (fun _ : Point shape => (0 : Fp)) 0 :=
      ⟨0, by simp, fun pt _ => by simp⟩
    exact (h0.congr_event fun pt _ => (hval pt).symm).mono (Nat.zero_le d)

/-- `computeB` over represented degree-1 challenges: after `n` rounds the value is a polynomial
of total degree ≤ `n + 2ⁿ − 1` (each round multiplies by `1 + uⱼ · x₃^(2^r)`). -/
theorem computeB_rep_aux (l : List (Point shape → Fp))
    (hl : ∀ f ∈ l, NumeratorRep vk 1 f 1) :
    NumeratorRep vk 1 (fun pt => computeB (pt ScalarSlot.x3) (l.map (· pt)))
      (l.length + 2 ^ l.length - 1) := by
  induction l with
  | nil =>
    have h1 : NumeratorRep vk 1 (fun _ : Point shape => (1 : Fp)) 0 := NumeratorRep.const 1
    exact (h1.congr_event fun pt _ => by simp [computeB]).mono (Nat.zero_le _)
  | cons f t ih =>
    have hf := hl f List.mem_cons_self
    have iht := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hpow : NumeratorRep vk 1 (fun pt => (pt ScalarSlot.x3) ^ (2 ^ t.length))
        (2 ^ t.length) := by
      have := (NumeratorRep.var (vk := vk) ScalarSlot.x3).pow (2 ^ t.length)
      exact (this.denCongr (one_pow _)).mono (Nat.mul_one _).le
    have hfac : NumeratorRep vk 1
        (fun pt => 1 + f pt * (pt ScalarSlot.x3) ^ (2 ^ t.length)) (1 + 2 ^ t.length) := by
      have hmul := (hf.mul hpow).denCongr (one_mul 1)
      have := (NumeratorRep.const (vk := vk) 1).add hmul
      exact this.mono (max_le (Nat.zero_le _) le_rfl)
    have hstep := (iht.mul hfac).denCongr (one_mul 1)
    refine (hstep.congr_event fun pt _ => ?_).mono ?_
    · rw [List.map_cons, computeB_cons, List.length_map]
    · have h1 : 1 ≤ 2 ^ t.length := Nat.one_le_two_pow
      have h2 : 2 ^ (t.length + 1) = 2 ^ t.length + 2 ^ t.length := by
        rw [pow_succ]; omega
      rw [List.length_cons, h2]
      omega

/-- The `b` value: a polynomial of the round challenges and `x₃` at total degree
≤ `2^k + k + 1`. -/
theorem computeB_rep :
    NumeratorRep vk 1
      (fun pt => computeB (pt ScalarSlot.x3) (List.ofFn fun j => pt (ScalarSlot.ipaRound j)))
      (2 ^ shape.k + shape.k + 1) := by
  have h := computeB_rep_aux (vk := vk)
    (List.ofFn fun j => fun pt : Point shape => pt (ScalarSlot.ipaRound j))
    (by
      intro f hf
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
      exact NumeratorRep.var (vk := vk) _)
  refine (h.congr_event fun pt _ => ?_).mono ?_
  · rw [List.map_ofFn]
    rfl
  · rw [List.length_ofFn]
    have h1 : 1 ≤ 2 ^ shape.k := Nat.one_le_two_pow
    omega

/-- The assembled `w` coefficient `-ipaF`, at degree 1. -/
theorem wScalar_rep : NumeratorRep vk 1 (fun pt => -(pt ScalarSlot.ipaF)) 1 :=
  (NumeratorRep.var _).neg

/-- The assembled `u` coefficient `-c · b · z`, at degree ≤ `2^k + k + 3`. -/
theorem uScalar_rep :
    NumeratorRep vk 1
      (fun pt => -(pt ScalarSlot.ipaC)
        * computeB (pt ScalarSlot.x3) (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
        * pt ScalarSlot.z)
      (2 ^ shape.k + shape.k + 3) := by
  have h1 := (NumeratorRep.var (vk := vk) ScalarSlot.ipaC).neg
  have h2 := (h1.mul computeB_rep).denCongr (one_mul 1)
  have h3 := (h2.mul (NumeratorRep.var ScalarSlot.z)).denCongr (one_mul 1)
  exact h3.mono (by omega)

/-- `computeS` over represented degree-1 challenges and a represented seed: every entry of the
folded-generator vector is represented at degree ≤ `d₀ + n`. -/
theorem computeS_rep_aux (l : List (Point shape → Fp))
    (hl : ∀ f ∈ l, NumeratorRep vk 1 f 1) (init : Point shape → Fp) (d0 : ℕ)
    (hinit : NumeratorRep vk 1 init d0) :
    ListRep vk 1 (fun pt => computeS (l.map (· pt)) (init pt)) (d0 + l.length) := by
  induction l with
  | nil =>
    refine (ListRep.singleton hinit).congr (fun pt => ?_) |>.mono (by omega)
    simp [computeS]
  | cons f t ih =>
    have hf := hl f List.mem_cons_self
    have iht := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hmul : ListRep vk 1
        (fun pt => (computeS (t.map (· pt)) (init pt)).map (· * f pt))
        (d0 + t.length + 1) := by
      obtain ⟨fns, heq, hrep⟩ := iht
      refine ⟨fns.map (fun g => fun pt => g pt * f pt), fun pt => ?_, fun g hg => ?_⟩
      · have h := heq pt
        simp only at h ⊢
        rw [h, List.map_map, List.map_map]
        rfl
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact ((hrep g' hg').mul hf).denCongr (one_mul 1)
    have happ := (iht.mono (by omega : d0 + t.length ≤ d0 + t.length + 1)).append hmul
    refine (happ.congr fun pt => ?_).mono (by simp only [List.length_cons]; omega)
    rw [List.map_cons, computeS_cons]

/-- Every entry of the deployed folded-generator vector `computeS u (-c)` is a polynomial of
the round challenges and `ipaC` at total degree ≤ `1 + k`. -/
theorem computeS_getD_rep (i : ℕ) :
    NumeratorRep vk 1
      (fun pt => (computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
        (-(pt ScalarSlot.ipaC))).getD i 0)
      (1 + shape.k) := by
  have h := computeS_rep_aux (vk := vk)
    (List.ofFn fun j => fun pt : Point shape => pt (ScalarSlot.ipaRound j))
    (by
      intro f hf
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
      exact NumeratorRep.var (vk := vk) _)
    (fun pt => -(pt ScalarSlot.ipaC)) 1 (NumeratorRep.var (vk := vk) _).neg
  have h' : ListRep vk 1
      (fun pt => computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
        (-(pt ScalarSlot.ipaC)))
      (1 + shape.k) := by
    refine (h.congr fun pt => ?_).mono (by rw [List.length_ofFn])
    rw [List.map_ofFn]
    rfl
  exact h'.getD_rep i

/-- The `g`-block coordinate at a nonzero position: just the `computeS` entry (the opened
value contributes only at position `0`). -/
theorem gScalars_tail_rep (vFn : Point shape → Fp) (i : ℕ) (hi : i ≠ 0) :
    NumeratorRep vk 1
      (fun pt => [-vFn pt].getD i 0
        + (computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
            (-(pt ScalarSlot.ipaC))).getD i 0)
      (1 + shape.k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  exact (computeS_getD_rep (n + 1)).congr_event fun pt _ => by simp

/-- The `g`-block coordinate at position `0`: the negated opening value plus the `computeS`
head, over the opening value's denominator. The opening value's representation is the one
upstream input (the multiopen walk supplies it). -/
theorem gScalars_head_rep {den : MvPolynomial (ScalarSlot shape) Fp}
    {vFn : Point shape → Fp} {dv dDen : ℕ} (hv : NumeratorRep vk den vFn dv)
    (hden : den.totalDegree ≤ dDen) :
    NumeratorRep vk den
      (fun pt => [-vFn pt].getD 0 0
        + (computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
            (-(pt ScalarSlot.ipaC))).getD 0 0)
      (max dv (1 + shape.k + dDen)) := by
  have hs := ((computeS_getD_rep (vk := vk) 0).extend den).denCongr (one_mul den)
  have hs' := hs.mono (Nat.add_le_add le_rfl hden)
  have := hv.neg.add hs'
  exact this.congr_event fun pt _ => by simp

/-- The `g`-block coordinates, uniformly: given a representation of the opening value over
`den`, every coordinate is represented over `den` at degree ≤ `max dv (1 + k + dDen)`. -/
theorem gScalars_coord_rep {den : MvPolynomial (ScalarSlot shape) Fp}
    {vFn : Point shape → Fp} {dv dDen : ℕ} (hv : NumeratorRep vk den vFn dv)
    (hden : den.totalDegree ≤ dDen) (i : Fin (2 ^ shape.k)) :
    NumeratorRep vk den
      (fun pt => [-vFn pt].getD i.val 0
        + (computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
            (-(pt ScalarSlot.ipaC))).getD i.val 0)
      (max dv (1 + shape.k + dDen)) := by
  by_cases h0 : i.val = 0
  · rw [h0]
    exact gScalars_head_rep hv hden
  · have h := ((gScalars_tail_rep (vk := vk) vFn i.val h0).extend den).denCongr (one_mul den)
    refine h.mono ?_
    calc 1 + shape.k + den.totalDegree ≤ 1 + shape.k + dDen := Nat.add_le_add le_rfl hden
      _ ≤ max dv (1 + shape.k + dDen) := le_max_right _ _

end IpaReps

end Zcash.Snark
