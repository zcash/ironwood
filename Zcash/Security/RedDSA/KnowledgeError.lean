import Zcash.Common.RelationProbability
import Zcash.Security.RedDSA.Extraction
import Zcash.Snark.Soundness.AGM.AdaptiveOnline

/-!
# The binding-signature knowledge error: κ ≤ (qH+1)/|F| + (ε_DL + 1/|F|)

The κ-discharge for the extraction arm, composing the deterministic core
(`bindingSig_relation_of_nontrivial`) with the labeled adaptive squeeze
(`finalBadWithoutRelation_measure_le`) and the relation-to-discrete-log reduction
(`relation_prob_le_of_textbookDL`). The argument is the straight-line AGM+ROM extraction of
Fuchsbauer–Plouviez–Seurin (eprint 2019/877, section 3, Theorem 1), in the key-only setting the
balance argument needs — the signature is the adversary's own, so there is no signing oracle and
none of that proof's simulation terms.

The adversary is a `LabeledOracleComp`: each challenge query carries the algebraic adversary's
representation of its group elements over the presented basis (`QueryRep`), data the oracle
never sees, and the output announces the representation for the returned signature. The
representation in effect at the output's query point (`effectiveRep`) is the first query-time
annotation when the run queried that point, and the announced one otherwise. This is the FPS
table discipline: the first representation presented at a point is the one extraction reads,
so presenting a different one later changes nothing — which closes the trivial-representation
trap (`R = S • ℛ − c · bvk`) structurally.

The sample space is the challenge oracle's whole table (`Q → F`) times the basis logs
(`Fin m → F`; the bases are presented as `scalarBasis gen s`, and the reference-string
heuristic carries the bound to the deployed fixed bases — see the Security Definitions book
page). The knowledge-error event splits along the replayed relation finder:

* **no relation found** — then the challenge at the output's query point equals the effective
  representation's one bad challenge: a singleton fixed before that answer was drawn on the
  annotation branch, and computed from an output that reprogramming the point cannot change on
  the fallback branch. The labeled squeeze gives `(qH+1)/|F|` per basis-log fibre — the FPS
  `q_H + 1` accounting, with the game's own final challenge query played by the fallback;
* **relation found** — the finder is a discrete-log adversary: the tight Jaeger–Tessaro
  accounting gives `ε_DL + 1/|F|` per challenge table.

The two arms live on independent factors of the product, so the fibre-wise Fubini bounds
compose them with no cross term.

Two idealizations are inherited by any instantiation. The challenge oracle is exactly uniform
on `F`; the deployed challenge hash produces 512 bits reduced mod `r_ℙ`, at statistical
distance about `2^{-257}` per query — an instantiation-level accounting item, as for
`GenRandom` in `Zcash.Security.RedDSA.Basic`. And the labels are data: the model does not
constrain which representations the adversary presents, so the hypotheses alone are
satisfiable with representations no efficient party could compute. The theorem's content
comes from instantiating the labels with an algebraic adversary's actual representations —
the AGM reading — which ties them to the represented elements at the instantiation and makes
an extractor that reads them efficient.
-/

namespace Zcash.Security.RedDSA

open Zcash.Snark Zcash.Snark.LabeledOracleComp
open scoped ENNReal

section Composition

variable {Q F ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype F] [Nonempty F]
  [Fintype ι] [DecidableEq ι]

/-- **The κ bound: the two extraction arms combined.** The extraction-failure event sits in the
bad-challenge event (`badFiber s`, on the challenge-table factor `Q → F`, per basis-log
vector `s`) union the relation event (`relFiber O`, on the basis-log factor `ι → F`, per
challenge table `O` — the extracted relation's coefficients read the challenge). Each arm is
bounded on its own factor, so a union bound gives `κ ≤ qH/|F| + (ε + 1/|F|)`. -/
theorem kappa_le_of_arms
    {κEvent : Set ((Q → F) × (ι → F))}
    (badFiber : (ι → F) → Set (Q → F)) (relFiber : (Q → F) → Set (ι → F)) {qH ε : ℝ≥0∞}
    (hcontain : κEvent ⊆ {ω | ω.1 ∈ badFiber ω.2} ∪ {ω | ω.2 ∈ relFiber ω.1})
    (hbad : ∀ s, (PMF.uniformOfFintype (Q → F)).toOuterMeasure (badFiber s) ≤ qH / Fintype.card F)
    (hrel : ∀ O, (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relFiber O)
      ≤ ε + 1 / Fintype.card F) :
    (PMF.uniformOfFintype ((Q → F) × (ι → F))).toOuterMeasure κEvent
      ≤ qH / Fintype.card F + (ε + 1 / Fintype.card F) := by
  refine le_trans (MeasureTheory.measure_mono hcontain) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add (uniformOfFintype_prod_fiber_bound badFiber hbad)
    (uniformOfFintype_prod_fiber_bound_right relFiber hrel)

end Composition

/-- The κ-game adversary's output: the Schnorr response, the signature's challenge query
point, and the announced representation of the signature's group elements. -/
structure KappaOutput (F Q : Type*) (m : ℕ) where
  response : F
  queryPoint : Q
  announced : QueryRep F m

instance {F Q : Type*} [Zero F] [Inhabited Q] {m : ℕ} : Inhabited (KappaOutput F Q m) :=
  ⟨⟨0, default, default⟩⟩

section Discharge

variable {Q F M : Type*} [Fintype Q] [DecidableEq Q] [Field F] [Fintype F] [Nonempty F]
  [AddCommGroup M] [Module F M] (m : ℕ)

variable (gen : M) (r_idx : Fin m)
  (adv : (Fin m → M) → LabeledOracleComp Q F (fun _ => QueryRep F m) (KappaOutput F Q m))

/-- The adversary's output at challenge table `O` and basis logs `s`. -/
def dischargeOut (O : Q → F) (s : Fin m → F) : KappaOutput F Q m :=
  (adv (scalarBasis gen s)).run O

/-- The run's challenge: the oracle's answer at the output's query point. -/
def dischargeChallenge (O : Q → F) (s : Fin m → F) : F :=
  O (dischargeOut m gen adv O s).queryPoint

/-- The representation in effect at the output's query point: the first query-time annotation
when the run queried that point, and the announced output representation otherwise. The
fallback plays the game's own final challenge query — the Fuchsbauer–Plouviez–Seurin
`q_H + 1` accounting. -/
def effectiveRep (O : Q → F) (s : Fin m → F) : QueryRep F m :=
  ((adv (scalarBasis gen s)).findLabel O (dischargeOut m gen adv O s).queryPoint).getD
    (dischargeOut m gen adv O s).announced

/-- The Schnorr verification equation `[S] ℛ = R + [c] bvk`, with `R` and `bvk` read off the
effective representation at the presented basis. -/
def Verifies (O : Q → F) (s : Fin m → F) : Prop :=
  letI b := scalarBasis gen s
  letI t := effectiveRep m gen adv O s
  (dischargeOut m gen adv O s).response • b r_idx
    = representationEval b t.commitment
      + (dischargeChallenge m gen adv O s) • representationEval b t.key

variable [DecidableEq F]

/-- The knowledge-error event: the run produces a verifying binding signature whose effective
representation has a pivot — a key coefficient off the ℛ slot. (A key represented on the ℛ
slot alone needs no extraction: the extractor that reads `key r_idx` succeeds there.) -/
def kappaEvent : Set ((Q → F) × (Fin m → F)) :=
  {ω | Verifies m gen r_idx adv ω.1 ω.2
    ∧ ((effectiveRep m gen adv ω.1 ω.2).pivot r_idx).isSome}

variable [DecidableEq M]

/-- The relation finder the discrete-log reduction runs: replay the adversary at the presented
basis, and when its output verifies with nonzero assembled coefficients, return the assembled
relation. Computable — the branch conditions are equalities in `M` and in `Fin m → F`. -/
def relFinder (O : Q → F) (b : Fin m → M) : Option (AlgebraicRelationWitness (F := F) b) :=
  letI out := (adv b).run O
  letI t := ((adv b).findLabel O out.queryPoint).getD out.announced
  letI c := O out.queryPoint
  if h : (out.response • b r_idx
        = representationEval b t.commitment + c • representationEval b t.key)
      ∧ t.assembled r_idx c out.response ≠ 0 then
    some (bindingSig_relation_of_nontrivial b r_idx t c out.response h.1 h.2)
  else none

/-- Bad-challenge arm (fibre over the basis logs `s`): the knowledge-error conditions hold and
the replayed finder returns no relation. -/
def badFiber (s : Fin m → F) : Set (Q → F) :=
  {O | Verifies m gen r_idx adv O s
    ∧ ((effectiveRep m gen adv O s).pivot r_idx).isSome
    ∧ relFinder m r_idx adv O (scalarBasis gen s) = none}

/-- Relation arm (fibre over the challenge table `O`): the replayed finder returns a
relation. -/
def relFiber (O : Q → F) : Set (Fin m → F) :=
  {s | (relFinder m r_idx adv O (scalarBasis gen s)).isSome}

omit [Fintype Q] [Fintype F] [Nonempty F] in
/-- **Deterministic containment.** On the knowledge-error event, either the replayed finder
found a relation (the relation arm) or it found none (the bad-challenge arm). -/
theorem kappaEvent_subset :
    kappaEvent m gen r_idx adv
      ⊆ {ω | ω.1 ∈ badFiber m gen r_idx adv ω.2} ∪ {ω | ω.2 ∈ relFiber m gen r_idx adv ω.1} := by
  rintro ⟨O, s⟩ ⟨hver, hpiv⟩
  rcases hfind : relFinder m r_idx adv O (scalarBasis gen s) with _ | w
  · exact Or.inl ⟨hver, hpiv, hfind⟩
  · exact Or.inr (by simp only [relFiber, Set.mem_setOf_eq, hfind, Option.isSome_some])

/-- The knowledge-error conditions as a set of answers at the output's query point — the
`finalBad` handed to the labeled squeeze: challenges satisfying the verification equation on
the effective representation, when that representation has a pivot. -/
def finalBadSet (b : Fin m → M) (out : KappaOutput F Q m) (O : Q → F) : Set F :=
  letI eff := ((adv b).findLabel O out.queryPoint).getD out.announced
  {x | out.response • b r_idx
      = representationEval b eff.commitment + x • representationEval b eff.key
    ∧ (eff.pivot r_idx).isSome}

/-- **The bad-challenge arm discharged by the labeled squeeze.** At basis logs `s`, within
query budget `qH`, the bad-challenge fibre has measure at most `(qH+1)/|F|`. On that fibre the
oracle's answer at the output's query point equals the effective representation's one bad
challenge: on the annotation branch a singleton fixed before the answer was drawn, and on the
fallback branch a singleton computed from an output that reprogramming the point cannot
change. The `+1` is the Fuchsbauer–Plouviez–Seurin `q_H + 1` accounting, with the game's own
final challenge query played by the fallback branch. -/
theorem badFiber_measure_le {s : Fin m → F} {qH : ℕ}
    (hQ : (adv (scalarBasis gen s)).QueryBound qH) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure (badFiber m gen r_idx adv s)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (finalBadWithoutRelation_measure_le (adv (scalarBasis gen s))
      (fun out => out.queryPoint)
      (fun out _ O => finalBadSet m r_idx adv (scalarBasis gen s) out O)
      (fun O => relFinder m r_idx adv O (scalarBasis gen s))
      (fun _ label _ => {label.badChallenge r_idx})
      (fun out _ _ => {out.announced.badChallenge r_idx})
      ?_ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ label _ => le_of_eq (uniformOfFintype_toOuterMeasure_singleton _))
      (fun out _ _ => le_of_eq (uniformOfFintype_toOuterMeasure_singleton _))
      hQ)
    (le_of_eq (mul_one_div _ _)))
  · -- the bad-challenge fibre is the squeeze's event
    rintro O ⟨hver, hpiv, hnone⟩
    exact ⟨⟨hver, hpiv⟩, hnone⟩
  · -- hcover: with no relation found, the challenge is the effective bad challenge
    intro O hfinal hnone
    obtain ⟨hver, hpiv⟩ := hfinal
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpiv
    have hc : O (((adv (scalarBasis gen s)).run O).queryPoint)
        = (((adv (scalarBasis gen s)).findLabel O
              ((adv (scalarBasis gen s)).run O).queryPoint).getD
            ((adv (scalarBasis gen s)).run O).announced).badChallenge r_idx := by
      by_contra hne
      have hcond := And.intro hver
        (QueryRep.assembled_ne_zero_of_ne_badChallenge
          (S := ((adv (scalarBasis gen s)).run O).response) hj hne)
      have hnone' : relFinder m r_idx adv O (scalarBasis gen s) = none := hnone
      rw [relFinder, dif_pos hcond] at hnone'
      exact Option.some_ne_none _ hnone'
    unfold firstLabelOrFallbackBad
    rw [hc]
    cases (adv (scalarBasis gen s)).findLabel O
        (((adv (scalarBasis gen s)).run O).queryPoint) <;>
      rfl

omit [Fintype Q] [Nonempty F] in
/-- The relation arm is the relation-finding event of the replayed finder. -/
theorem relFiber_subset_relSet (O : Q → F) :
    relFiber m gen r_idx adv O ⊆ ↑(relSet gen (relFinder m r_idx adv O)) := by
  intro s hs
  simpa only [relSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] using hs

omit [Fintype Q] in
/-- **The relation arm discharged against textbook discrete log.** If the finder's textbook-DL
advantage is at most `ε`, the relation fibre has measure at most `ε + 1/|F|` — the tight
Jaeger–Tessaro accounting, with no multiplicative loss. -/
theorem relFiber_measure_le {O : Q → F} {ε : ℝ≥0∞}
    (hdl : TextbookDLAdvantageLE gen (relFinder m r_idx adv O) ε) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure (relFiber m gen r_idx adv O)
      ≤ ε + 1 / Fintype.card F :=
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  le_trans (MeasureTheory.measure_mono (relFiber_subset_relSet m gen r_idx adv O))
    (relation_prob_le_of_textbookDL gen (relFinder m r_idx adv O) hdl)

/-- **The knowledge error bounded: κ ≤ (qH+1)/|F| + (ε_DL + 1/|F|).** For a labeled algebraic
adversary within query budget `qH`, if every replayed relation finder has textbook-DL
advantage at most `ε`, the probability of a verifying binding signature whose effective
representation has a pivot is at most `(qH+1)/|F| + (ε + 1/|F|)`. The `qH + 1` is the FPS
`q_H + 1` accounting, carried by the squeeze's fallback branch — no completion step, and no
hypothesis that the adversary queries its output's point.

The DL hypothesis is per challenge table — one `ε` bounding the finder's advantage for every
`O`, a supremum over unbounded advice and so stronger than the advantage of any single
reduction. That is an artefact of the fibre-wise composition; a joint experiment in which the
reduction samples the table itself needs only the one composite reduction's advantage. -/
theorem kappaEvent_measure_le {qH : ℕ} {ε : ℝ≥0∞}
    (hQ : ∀ s : Fin m → F, (adv (scalarBasis gen s)).QueryBound qH)
    (hdl : ∀ O : Q → F, TextbookDLAdvantageLE gen (relFinder m r_idx adv O) ε) :
    (PMF.uniformOfFintype ((Q → F) × (Fin m → F))).toOuterMeasure (kappaEvent m gen r_idx adv)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F + (ε + 1 / Fintype.card F) :=
  kappa_le_of_arms (badFiber m gen r_idx adv) (relFiber m gen r_idx adv)
    (kappaEvent_subset m gen r_idx adv)
    (fun s => badFiber_measure_le m gen r_idx adv (hQ s))
    (fun O => relFiber_measure_le m gen r_idx adv (hdl O))

end Discharge

section Degenerate

variable {F M ι : Type*} [Field F] [Fintype F] [Nonempty F] [DecidableEq F]
  [AddCommGroup M] [Module F M] [DecidableEq M]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The relation finder for an all-zero basis: every coefficient vector is a relation there,
so return the all-ones one. Returns nothing on any other basis. -/
def zeroBasisRelationFinder : (b : ι → M) → Option (AlgebraicRelationWitness (F := F) b) :=
  fun b =>
    if h : ∀ i, b i = 0 then
      some { coeffs := fun _ => 1
             nontrivial := fun h1 => one_ne_zero (congrFun h1 (Classical.arbitrary ι))
             relation := by simp [representationEval, h] }
    else none

/-- **Degeneracy of the zero base, as a theorem.** At base `0` every presented basis is
all-zero, so `zeroBasisRelationFinder` finds a relation on every sample, and any `ε`
satisfying the textbook-DL hypothesis for it is at least `1 − 1/|F|`. The κ bounds above
therefore cannot be instantiated with a small `ε` at a degenerate base: the hypothesis
carries the non-degeneracy requirement, and no side condition on `gen` is needed. -/
theorem textbookDLAdvantageLE_base_zero {ε : ℝ≥0∞}
    (h : TextbookDLAdvantageLE (0 : M) (zeroBasisRelationFinder (F := F) (ι := ι)) ε) :
    1 ≤ ε + 1 / Fintype.card F := by
  have hrel := relation_prob_le_of_textbookDL (0 : M) _ h
  have huniv : relSet (0 : M) (zeroBasisRelationFinder (F := F) (ι := ι)) = Finset.univ := by
    ext s
    simp [relSet, zeroBasisRelationFinder, scalarBasis]
  rw [huniv] at hrel
  calc (1 : ℝ≥0∞)
      = (PMF.uniformOfFintype (ι → F)).toOuterMeasure ↑(Finset.univ : Finset (ι → F)) := by
        rw [Finset.coe_univ, uniformOfFintype_toOuterMeasure_univ]
    _ ≤ ε + 1 / Fintype.card F := hrel

end Degenerate

end Zcash.Security.RedDSA
