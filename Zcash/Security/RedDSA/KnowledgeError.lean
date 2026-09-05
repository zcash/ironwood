import Zcash.Common.RelationProbabilityCoins
import Zcash.Security.RedDSA.Extraction
import Zcash.Snark.Soundness.AGM.AdaptiveOnline

/-!
# The binding-signature knowledge error: κ ≤ (qH+1)/|F| + (ε_DL + 1/|F|)

Throughout, κ is the knowledge error: the probability that the adversary's output verifies
while the extractor fails to produce the witness — here, a verifying binding signature whose
announced representations do not yield the binding key. Definitions prefixed with `kappa` build
this event and its bound.

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
(`Fin m → F`; the bases are presented as `scalarBasis gen logs`, and the reference-string
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

The same split also composes at a single presented basis, with no log sampling. Both arms
then live over the challenge-table factor, so a plain union bound composes them
(`kappaEventAt_measure_le`). The relation arm is carried as a named hypothesis: the
probability that the replayed finder returns a relation at that basis.

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

open Zcash.Snark Zcash.Common Zcash.Common.LabeledOracleComp
open scoped ENNReal

section Composition

variable {Q F ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype F] [Nonempty F]
  [Fintype ι] [DecidableEq ι]

/-- **The κ bound: the two extraction arms combined.** The extraction-failure event sits in the
bad-challenge event (`badFiber logs`, on the challenge-table factor `Q → F`, per basis-log
vector `logs`) union the relation event (`relFiber table`, on the basis-log factor `ι → F`, per
challenge table `table` — the extracted relation's coefficients read the challenge). Each arm is
bounded on its own factor, so a union bound gives `κ ≤ qH/|F| + (ε + 1/|F|)`. -/
theorem kappa_le_of_arms
    {κEvent : Set ((Q → F) × (ι → F))}
    (badFiber : (ι → F) → Set (Q → F)) (relFiber : (Q → F) → Set (ι → F)) {qH ε : ℝ≥0∞}
    (hcontain : κEvent ⊆ {ω | ω.1 ∈ badFiber ω.2} ∪ {ω | ω.2 ∈ relFiber ω.1})
    (hbad : ∀ logs,
      (PMF.uniformOfFintype (Q → F)).toOuterMeasure (badFiber logs) ≤ qH / Fintype.card F)
    (hrel : ∀ table, (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relFiber table)
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

/-- The adversary's output at the presented `basis` and challenge table `table`. -/
def dischargeOutAt (basis : Fin m → M) (table : Q → F) : KappaOutput F Q m :=
  (adv basis).run table

/-- The run's challenge at the presented `basis`: the oracle's answer at the output's query
point. -/
def dischargeChallengeAt (basis : Fin m → M) (table : Q → F) : F :=
  table (dischargeOutAt m adv basis table).queryPoint

/-- The representation in effect at the output's query point, at the presented `basis`: the
first query-time annotation when the run queried that point, and the announced output
representation otherwise. The fallback plays the game's own final challenge query — the
Fuchsbauer–Plouviez–Seurin `q_H + 1` accounting. -/
def effectiveRepAt (basis : Fin m → M) (table : Q → F) : QueryRep F m :=
  ((adv basis).findLabel table (dischargeOutAt m adv basis table).queryPoint).getD
    (dischargeOutAt m adv basis table).announced

/-- The Schnorr verification equation `S • ℛ = R + c • bvk` at the presented `basis`, with `R`
and `bvk` read off the effective representation. -/
def VerifiesAt (basis : Fin m → M) (table : Q → F) : Prop :=
  letI t := effectiveRepAt m adv basis table
  (dischargeOutAt m adv basis table).response • basis r_idx
    = representationEval basis t.commitment
      + (dischargeChallengeAt m adv basis table) • representationEval basis t.key

/-- The adversary's output at challenge table `table` and the basis discrete logarithms `logs`. -/
def dischargeOut (table : Q → F) (logs : Fin m → F) : KappaOutput F Q m :=
  dischargeOutAt m adv (scalarBasis gen logs) table

/-- The run's challenge: the oracle's answer at the output's query point. -/
def dischargeChallenge (table : Q → F) (logs : Fin m → F) : F :=
  dischargeChallengeAt m adv (scalarBasis gen logs) table

/-- The representation in effect at the output's query point: `effectiveRepAt` at the sampled
basis. -/
def effectiveRep (table : Q → F) (logs : Fin m → F) : QueryRep F m :=
  effectiveRepAt m adv (scalarBasis gen logs) table

/-- The Schnorr verification equation at the sampled basis: `VerifiesAt` at
`scalarBasis gen logs`. -/
def Verifies (table : Q → F) (logs : Fin m → F) : Prop :=
  VerifiesAt m r_idx adv (scalarBasis gen logs) table

variable [DecidableEq F]

/-- The knowledge-error event at the presented `basis`, over the challenge-table factor alone:
the run produces a verifying binding signature whose effective representation has a pivot — a
key coefficient off the ℛ slot. (A key represented on the ℛ slot alone needs no extraction:
the extractor that reads `key r_idx` succeeds there.) -/
def kappaEventAt (basis : Fin m → M) : Set (Q → F) :=
  {table | VerifiesAt m r_idx adv basis table
    ∧ ((effectiveRepAt m adv basis table).pivot r_idx).isSome}

/-- The knowledge-error event over the sampled product space: `kappaEventAt` at the sampled
basis of each sample's logs. -/
def kappaEvent : Set ((Q → F) × (Fin m → F)) :=
  {ω | ω.1 ∈ kappaEventAt m r_idx adv (scalarBasis gen ω.2)}

omit [Fintype Q] [Fintype F] [Nonempty F] in
/-- Membership in the sampled product-space event, from the per-basis event at the sample's
own basis. -/
theorem mem_kappaEvent {table : Q → F} {logs : Fin m → F}
    (h : table ∈ kappaEventAt m r_idx adv (scalarBasis gen logs)) :
    (table, logs) ∈ kappaEvent m gen r_idx adv := h

variable [DecidableEq M]

/-- The relation finder the discrete-log reduction runs: replay the adversary at the presented
basis, and when its output verifies with nonzero assembled coefficients, return the assembled
relation. Computable — the branch conditions are equalities in `M` and in `Fin m → F`. -/
def relFinder (table : Q → F) (basis : Fin m → M) :
    Option (AlgebraicRelationWitness (F := F) basis) :=
  letI out := (adv basis).run table
  letI t := ((adv basis).findLabel table out.queryPoint).getD out.announced
  letI c := table out.queryPoint
  if h : (out.response • basis r_idx
        = representationEval basis t.commitment + c • representationEval basis t.key)
      ∧ t.assembled r_idx c out.response ≠ 0 then
    some (bindingSig_relation_of_nontrivial basis r_idx t c out.response h.1 h.2)
  else none

/-- The bad-challenge event at the presented `basis`, over the challenge-table factor: the
knowledge-error conditions hold and the replayed finder returns no relation. -/
def badFiberAt (basis : Fin m → M) : Set (Q → F) :=
  {table | VerifiesAt m r_idx adv basis table
    ∧ ((effectiveRepAt m adv basis table).pivot r_idx).isSome
    ∧ relFinder m r_idx adv table basis = none}

/-- The relation event at the presented `basis`, over the challenge-table factor: the
replayed finder returns a relation. -/
def relFiberAt (basis : Fin m → M) : Set (Q → F) :=
  {table | (relFinder m r_idx adv table basis).isSome}

/-- Bad-challenge arm (fibre over the basis discrete logarithms `logs`): `badFiberAt` at the
sampled basis. -/
def badFiber (logs : Fin m → F) : Set (Q → F) :=
  badFiberAt m r_idx adv (scalarBasis gen logs)

/-- Relation arm (fibre over the challenge table `table`): the replayed finder returns a
relation. -/
def relFiber (table : Q → F) : Set (Fin m → F) :=
  {logs | (relFinder m r_idx adv table (scalarBasis gen logs)).isSome}

omit [Fintype Q] [Fintype F] [Nonempty F] in
/-- **Deterministic containment at a fixed basis.** On the knowledge-error event at the
presented `basis`, either the replayed finder found no relation (the bad-challenge arm) or
it found one (the relation arm). -/
theorem kappaEventAt_subset (basis : Fin m → M) :
    kappaEventAt m r_idx adv basis
      ⊆ badFiberAt m r_idx adv basis ∪ relFiberAt m r_idx adv basis := by
  rintro table ⟨hver, hpiv⟩
  rcases hfind : relFinder m r_idx adv table basis with _ | w
  · exact Or.inl ⟨hver, hpiv, hfind⟩
  · exact Or.inr (by simp only [relFiberAt, Set.mem_setOf_eq, hfind, Option.isSome_some])

omit [Fintype Q] [Fintype F] [Nonempty F] in
/-- **Deterministic containment.** On the knowledge-error event, either the replayed finder
found a relation (the relation arm) or it found none (the bad-challenge arm). -/
theorem kappaEvent_subset :
    kappaEvent m gen r_idx adv
      ⊆ {ω | ω.1 ∈ badFiber m gen r_idx adv ω.2} ∪ {ω | ω.2 ∈ relFiber m gen r_idx adv ω.1} := by
  rintro ⟨table, logs⟩ ⟨hver, hpiv⟩
  rcases hfind : relFinder m r_idx adv table (scalarBasis gen logs) with _ | w
  · exact Or.inl ⟨hver, hpiv, hfind⟩
  · exact Or.inr (by simp only [relFiber, Set.mem_setOf_eq, hfind, Option.isSome_some])

/-- The knowledge-error conditions as a set of answers at the output's query point — the
`finalBad` handed to the labeled squeeze: challenges satisfying the verification equation on
the effective representation, when that representation has a pivot. -/
def finalBadSet (basis : Fin m → M) (out : KappaOutput F Q m) (table : Q → F) : Set F :=
  letI eff := ((adv basis).findLabel table out.queryPoint).getD out.announced
  {x | out.response • basis r_idx
      = representationEval basis eff.commitment + x • representationEval basis eff.key
    ∧ (eff.pivot r_idx).isSome}

/-- **The bad-challenge event discharged by the labeled squeeze, at the presented `basis`.**
Within query budget `qH`, the bad-challenge event has measure at most `(qH+1)/|F|`. On that
event the oracle's answer at the output's query point equals the effective representation's
one bad challenge: on the annotation branch a singleton fixed before the answer was drawn,
and on the fallback branch a singleton computed from an output that reprogramming the point
cannot change. The `+1` is the Fuchsbauer–Plouviez–Seurin `q_H + 1` accounting, with the
game's own final challenge query played by the fallback branch. -/
theorem badFiberAt_measure_le {basis : Fin m → M} {qH : ℕ}
    (hQ : (adv basis).QueryBound qH) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure (badFiberAt m r_idx adv basis)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (finalBadWithoutRelation_measure_le (adv basis)
      (fun out => out.queryPoint)
      (fun out _ table => finalBadSet m r_idx adv basis out table)
      (fun table => relFinder m r_idx adv table basis)
      (fun _ label _ => {label.badChallenge r_idx})
      (fun out _ _ => {out.announced.badChallenge r_idx})
      ?_ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ label _ => le_of_eq (uniformOfFintype_toOuterMeasure_singleton _))
      (fun out _ _ => le_of_eq (uniformOfFintype_toOuterMeasure_singleton _))
      hQ)
    (le_of_eq (mul_one_div _ _)))
  · -- the bad-challenge event is the squeeze's event
    rintro table ⟨hver, hpiv, hnone⟩
    exact ⟨⟨hver, hpiv⟩, hnone⟩
  · -- hcover: with no relation found, the challenge is the effective bad challenge
    intro table hfinal hnone
    obtain ⟨hver, hpiv⟩ := hfinal
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpiv
    have hc : table (((adv basis).run table).queryPoint)
        = (((adv basis).findLabel table
              ((adv basis).run table).queryPoint).getD
            ((adv basis).run table).announced).badChallenge r_idx := by
      by_contra hne
      have hcond := And.intro hver
        (QueryRep.assembled_ne_zero_of_ne_badChallenge
          (S := ((adv basis).run table).response) hj hne)
      have hnone' : relFinder m r_idx adv table basis = none := hnone
      rw [relFinder, dif_pos hcond] at hnone'
      exact Option.some_ne_none _ hnone'
    unfold firstLabelOrFallbackBad
    rw [hc]
    cases (adv basis).findLabel table
        (((adv basis).run table).queryPoint) <;>
      rfl

/-- **The knowledge error at a fixed basis: κ ≤ (qH+1)/|F| + ε_rel.** For a labeled algebraic
adversary within query budget `qH` at the presented `basis`, if the probability over the
challenge table that the replayed finder returns a relation at this basis is at most `ε`,
then the probability of a verifying binding signature whose effective representation has a
pivot is at most `(qH+1)/|F| + ε`. No basis is sampled: both arms live over the
challenge-table factor, and the composition is a plain union bound. The bound therefore
holds at any fixed basis —in particular the deployed one— with the relation arm carried as
a named hypothesis on that basis. -/
theorem kappaEventAt_measure_le {basis : Fin m → M} {qH : ℕ} {ε : ℝ≥0∞}
    (hQ : (adv basis).QueryBound qH)
    (hrel : (PMF.uniformOfFintype (Q → F)).toOuterMeasure (relFiberAt m r_idx adv basis)
      ≤ ε) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure (kappaEventAt m r_idx adv basis)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F + ε :=
  le_trans (MeasureTheory.measure_mono (kappaEventAt_subset m r_idx adv basis))
    (le_trans (MeasureTheory.measure_union_le _ _)
      (add_le_add (badFiberAt_measure_le m r_idx adv hQ) hrel))

/-- The bad-challenge fibre at the basis discrete logarithms `logs`:
`badFiberAt_measure_le` at the sampled basis. -/
theorem badFiber_measure_le {logs : Fin m → F} {qH : ℕ}
    (hQ : (adv (scalarBasis gen logs)).QueryBound qH) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure (badFiber m gen r_idx adv logs)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F :=
  badFiberAt_measure_le m r_idx adv hQ

omit [Fintype Q] [Nonempty F] in
/-- The relation arm is the relation-finding event of the replayed finder. -/
theorem relFiber_subset_relSet (table : Q → F) :
    relFiber m gen r_idx adv table ⊆ ↑(relSet gen (relFinder m r_idx adv table)) := by
  intro logs hs
  simpa only [relSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] using hs

omit [Fintype Q] in
/-- **The relation arm discharged against textbook discrete log.** If the finder's textbook-DL
advantage is at most `ε`, the relation fibre has measure at most `ε + 1/|F|` — the tight
Jaeger–Tessaro accounting, with no multiplicative loss. -/
theorem relFiber_measure_le {table : Q → F} {ε : ℝ≥0∞}
    (hdl : TextbookDLAdvantageLE gen (relFinder m r_idx adv table) ε) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure (relFiber m gen r_idx adv table)
      ≤ ε + 1 / Fintype.card F :=
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  le_trans (MeasureTheory.measure_mono (relFiber_subset_relSet m gen r_idx adv table))
    (relation_prob_le_of_textbookDL gen (relFinder m r_idx adv table) hdl)

/-- **The knowledge error bounded: κ ≤ (qH+1)/|F| + (ε_DL + 1/|F|).** For a labeled algebraic
adversary within query budget `qH`, if every replayed relation finder has textbook-DL
advantage at most `ε`, the probability of a verifying binding signature whose effective
representation has a pivot is at most `(qH+1)/|F| + (ε + 1/|F|)`. The `qH + 1` is the FPS
`q_H + 1` accounting, carried by the squeeze's fallback branch — no completion step, and no
hypothesis that the adversary queries its output's point.

The DL hypothesis is per challenge table — one `ε` bounding the finder's advantage for every
`table`, a supremum over unbounded advice and so stronger than the advantage of any single
reduction. That is an artefact of the fibre-wise composition; a joint experiment in which the
reduction samples the table itself needs only the one composite reduction's advantage. -/
theorem kappaEvent_measure_le {qH : ℕ} {ε : ℝ≥0∞}
    (hQ : ∀ logs : Fin m → F, (adv (scalarBasis gen logs)).QueryBound qH)
    (hdl : ∀ table : Q → F, TextbookDLAdvantageLE gen (relFinder m r_idx adv table) ε) :
    (PMF.uniformOfFintype ((Q → F) × (Fin m → F))).toOuterMeasure (kappaEvent m gen r_idx adv)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F + (ε + 1 / Fintype.card F) :=
  kappa_le_of_arms (badFiber m gen r_idx adv) (relFiber m gen r_idx adv)
    (kappaEvent_subset m gen r_idx adv)
    (fun logs => badFiber_measure_le m gen r_idx adv (hQ logs))
    (fun table => relFiber_measure_le m gen r_idx adv (hdl table))

/-- **The knowledge error bounded, with a single randomized reduction:
κ ≤ (qH+1)/#F + (ε_DL + 1/#F).** As `kappaEvent_measure_le`, with the per-table DL
hypothesis replaced by one bound for the coin-consuming finder — the reduction samples the
challenge table as its own coins (`TextbookDLWithCoinsAdvantageLE` at `ρ := Q → F`), so the
supremum over tables disappears. -/
theorem kappaEvent_measure_le_of_coins {qH : ℕ} {ε : ℝ≥0∞}
    (hQ : ∀ logs : Fin m → F, (adv (scalarBasis gen logs)).QueryBound qH)
    (hdl : TextbookDLWithCoinsAdvantageLE gen
        (fun basis table => relFinder m r_idx adv table basis) ε) :
    (PMF.uniformOfFintype ((Q → F) × (Fin m → F))).toOuterMeasure (kappaEvent m gen r_idx adv)
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card F + (ε + 1 / Fintype.card F) := by
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  have hsub : kappaEvent m gen r_idx adv
      ⊆ {ω | ω.1 ∈ badFiber m gen r_idx adv ω.2}
        ∪ {ω : (Q → F) × (Fin m → F) |
            (ω.2, ω.1)
              ∈ ↑(relSetWithCoins gen (fun basis table => relFinder m r_idx adv table basis))} := by
    intro ω hω
    rcases kappaEvent_subset m gen r_idx adv hω with h | h
    · exact Or.inl h
    · refine Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
      simpa only [relFiber, Set.mem_setOf_eq] using h
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  · exact uniformOfFintype_prod_fiber_bound (badFiber m gen r_idx adv)
      (fun logs => badFiber_measure_le m gen r_idx adv (hQ logs))
  · have hswap : (PMF.uniformOfFintype ((Q → F) × (Fin m → F))).toOuterMeasure
        {ω : (Q → F) × (Fin m → F) |
          (ω.2, ω.1)
            ∈ ↑(relSetWithCoins gen (fun basis table => relFinder m r_idx adv table basis))}
        = (PMF.uniformOfFintype ((Fin m → F) × (Q → F))).toOuterMeasure
          ↑(relSetWithCoins gen (fun basis table => relFinder m r_idx adv table basis)) := by
      rw [← map_uniformOfFintype_equiv (Equiv.prodComm (Q → F) (Fin m → F)),
        PMF.toOuterMeasure_map_apply]
      congr 1
    rw [hswap]
    exact relationWithCoins_prob_le_of_textbookDL gen _ hdl

end Discharge

section Degenerate

variable {F M ι : Type*} [Field F] [Fintype F] [Nonempty F] [DecidableEq F]
  [AddCommGroup M] [Module F M] [DecidableEq M]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The relation finder for an all-zero basis: every coefficient vector is a relation there,
so return the all-ones one. Returns nothing on any other basis. -/
def zeroBasisRelationFinder : (basis : ι → M) → Option (AlgebraicRelationWitness (F := F) basis) :=
  fun basis =>
    if h : ∀ i, basis i = 0 then
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
    ext logs
    simp [relSet, zeroBasisRelationFinder, scalarBasis]
  rw [huniv] at hrel
  calc (1 : ℝ≥0∞)
      = (PMF.uniformOfFintype (ι → F)).toOuterMeasure ↑(Finset.univ : Finset (ι → F)) := by
        rw [Finset.coe_univ, uniformOfFintype_toOuterMeasure_univ]
    _ ≤ ε + 1 / Fintype.card F := hrel

end Degenerate

end Zcash.Security.RedDSA
