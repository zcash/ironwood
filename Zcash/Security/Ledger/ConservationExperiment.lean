import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ValueRelationArm

/-!
# The conservation experiment: both arms in one sample space

The capstones bound the conservation and cap violations by `εdlr + κ`, over an abstract
`PMF (ValidAnnotated …)` with the two arms' bounds as named hypotheses. This module
instantiates that composition in the challenge-oracle model, in one experiment: over the
adversary's coins, the challenge table, and the logs of the `m` presented bases, the
probability that the output ledger is valid *and* violates conservation (or the cap) at some
prefix `i < k` is at most `ε_dl + (qH+2)/#F`.

The composition is at the reduction layer. Both arms' finders return relations over the same
presented basis. One combined machine (`conservationRelFinder`) therefore replays the adversary
and returns whichever relation its sample yields: the relation arm's (`valueRelFinder`) when
that arm fires, and otherwise the extraction-failure arm's (`relFinder`, run on the composite
knowledge-error adversary). Every violation sample lands in the combined machine's relation
event or in the knowledge-error bad-challenge fibre (`conservationRelOrBadChallenge`). One
textbook discrete-log bound for the one machine therefore covers both arms' relation slices,
and their two programmed-basis losses merge into the single `1/#F` inside `(qH+2)/#F`. The
discrete-log hypothesis is stated for the coin-consuming form of the finder
(`TextbookDLWithCoinsAdvantageLE`, with the challenge table as the coins). It is quantified
only over the adversary's coins; no supremum over challenge tables remains anywhere in the
experiment.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable (m : ℕ)

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The challenge-oracle experiment distribution: the adversary's coins `j`, a uniform
challenge table `Q → ZMod r`, and uniform logs `Fin m → ZMod r` of the `m` presented bases. -/
noncomputable def challengeExperiment {ι : Type u} (p : PMF ι) :
    PMF (ι × ((Q → ZMod r) × (Fin m → ZMod r))) :=
  p.bind fun j => (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j)

omit [Inhabited Q] in
/-- The adversary-coins marginal of the challenge experiment is unchanged. -/
theorem challengeExperiment_map_fst {ι : Type u} (p : PMF ι) :
    (challengeExperiment (Q := Q) (r := r) m p).map Prod.fst = p := by
  rw [challengeExperiment, PMF.map_bind]
  simp only [PMF.map_comp,
    show ∀ j : ι, Prod.fst ∘ Prod.mk j =
      Function.const ((Q → ZMod r) × (Fin m → ZMod r)) j from fun _ => rfl,
    PMF.map_const]
  exact PMF.bind_pure p

/-- The sample-space lift of a per-primitives ledger event: the samples on which the
adversary's output ledger, run at the sampled primitives `kappaPrimitivesAt`, is valid and
lands in `Event` at those primitives. -/
def sampledLedgerEvent {ι : Type u}
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (Event : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)) :
    Set (ι × ((Q → ZMod r) × (Fin m → ZMod r))) :=
  setOf fun x =>
    ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
        kv issuance maxActions (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
      (⟨_, hval⟩ : ValidAnnotated (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig
          x.2.1 x.2.2) kv issuance maxActions)
        ∈ Event (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- `sampledLedgerEvent` is monotone in the event family: it preserves `⊆`. -/
theorem sampledLedgerEvent_mono {ι : Type u}
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    {E₁ E₂ : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)} (h : ∀ P, E₁ P ⊆ E₂ P) :
    sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA E₁
      ⊆ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA E₂ :=
  fun _ ⟨hval, hx⟩ => ⟨hval, h _ hx⟩

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- `sampledLedgerEvent` preserves unions: it is a join-homomorphism, since the `∃ hval`
that lifts the event distributes over the disjunction. -/
theorem sampledLedgerEvent_union {ι : Type u}
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (E₁ E₂ : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)) :
    sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA (fun P => E₁ P ∪ E₂ P)
      = sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA E₁
        ∪ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA E₂ := by
  ext x
  constructor
  · rintro ⟨hval, hx | hx⟩
    exacts [Or.inl ⟨hval, hx⟩, Or.inr ⟨hval, hx⟩]
  · rintro (⟨hval, hx⟩ | ⟨hval, hx⟩)
    exacts [⟨hval, Or.inl hx⟩, ⟨hval, Or.inr hx⟩]

/-- **The combined conservation relation finder.** Replay the labeled adversary at the
presented basis and return whichever relation the sample yields: the relation arm's
(`valueRelFinder`, at the value and randomness slots) when it fires, and the
extraction-failure arm's (`relFinder`, on the composite knowledge-error adversary, at the
randomness slot) otherwise. One machine per adversary coin, so one textbook discrete-log
bound covers both arms' relation slices. -/
def conservationRelFinder (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (O : Q → ZMod r) (b : Fin m → G) :
    Option (AlgebraicRelationWitness (F := ZMod r) b) :=
  valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b
    <|> relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O b

omit [Fintype Q] in
/-- The combined finder returns a relation whenever either arm's finder does. -/
theorem conservationRelFinder_isSome {hne_idx : v_idx ≠ r_idx} {k : ℕ}
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {O : Q → ZMod r} {b : Fin m → G}
    (h : (valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b).isSome
      ∨ (relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O b).isSome) :
    (conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b).isSome := by
  unfold conservationRelFinder
  rcases hv : valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b with _ | w
  · rcases h with h | h
    · exact absurd h (by simp [hv])
    · simpa using h
  · simp

/-- **The combined reduction's per-coin discharge event.** The samples on which the combined
finder returns a relation, together with those on which the knowledge-error bad-challenge
fibre fires. Every conservation (and cap) violation sample lands here, and its measure is
`ε_dl + (qH+2)/#F` (`conservationRelOrBadChallenge_measure_le`). -/
def conservationRelOrBadChallenge (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    Set ((Q → ZMod r) × (Fin m → ZMod r)) :=
  {ω | (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun b O =>
        conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b))}
    ∪ {ω | ω.1 ∈ badFiber m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) ω.2}

/-- **The per-coin discharge: one discrete-log bound covers both arms.** Within query budget
`qH`, the combined reduction's discharge event has measure at most `ε_dl + (qH+2)/#F`: the
relation slice at `ε_dl + 1/#F` (`relationWithCoins_prob_le_of_textbookDL`, applied once,
to the combined finder) and the bad-challenge fibre at `(qH+1)/#F`
(`badFiber_measure_le`). -/
theorem conservationRelOrBadChallenge_measure_le (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} (hQ : ∀ b, (LA b).QueryBound qH) {ε_dl : ℝ≥0∞}
    (hdl : TextbookDLWithCoinsAdvantageLE gen (fun b O =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b) ε_dl) :
    (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
        (conservationRelOrBadChallenge m gen v_idx r_idx queryOf P₀ toSig hne_idx k LA)
      ≤ ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  have hrel : (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
      {ω : (Q → ZMod r) × (Fin m → ZMod r) |
        (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun b O =>
          conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b))}
      ≤ ε_dl + 1 / Fintype.card (ZMod r) := by
    have hswap : (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
        {ω : (Q → ZMod r) × (Fin m → ZMod r) |
          (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun b O =>
            conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b))}
        = (PMF.uniformOfFintype ((Fin m → ZMod r) × (Q → ZMod r))).toOuterMeasure
          ↑(relSetWithCoins gen (fun b O =>
            conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O b)) := by
      rw [← map_uniformOfFintype_equiv (Equiv.prodComm (Q → ZMod r) (Fin m → ZMod r)),
        PMF.toOuterMeasure_map_apply]
      congr 1
    rw [hswap]
    exact relationWithCoins_prob_le_of_textbookDL gen _ hdl
  have hbad : (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
      {ω : (Q → ZMod r) × (Fin m → ZMod r) |
        ω.1 ∈ badFiber m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) ω.2}
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) :=
    uniformOfFintype_prod_fiber_bound
      (badFiber m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA))
      (fun s => badFiber_measure_le m gen r_idx _
        (kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ _)))
  unfold conservationRelOrBadChallenge
  refine le_trans (MeasureTheory.measure_union_le _ _)
    (le_trans (add_le_add hrel hbad) (le_of_eq ?_))
  rw [add_assoc, ENNReal.div_add_div_same]
  push_cast
  ring_nf

/-- **The conservation experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output ledger is valid and violates balance conservation
at some prefix `i < k` — the capstone's `balanceConservationViolationBefore`, at the sampled
primitives — is at most `ε_dl + (qH+2)/#F`. The discrete-log hypothesis is a single bound
for the combined coin-consuming finder, per adversary coin: one machine covers both arms'
relation slices, so their programmed-basis losses merge. -/
theorem balanceConservationBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun b O =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_dl) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono ?_)
    (conservationRelOrBadChallenge_measure_le m gen v_idx r_idx queryOf P₀ toSig hne_idx k
      (hQ j) (hdl j))
  rintro ⟨O, s⟩ ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases balanceConservationViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) O s) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, e, he⟩
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
        (Or.inl (valueRelation_finder_isSome m gen v_idx r_idx queryOf P₀ toSig hne_idx hr
          (le_of_lt hik) hval hw))⟩))
  · rcases kappaEvent_subset m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        (extractFail_mem_kappaEvent m gen v_idx r_idx queryOf P₀ toSig
          ((halg j).atLabel) ((halg j).atOutput) hr (le_of_lt hik) hval he)
      with hbad | hrel
    · exact Or.inr hbad
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig (Or.inr hrel)⟩))

/-- **The cap experiment.** As `balanceConservationBefore_measure_le_experiment`, for the
shielded pool exceeding the minted issuance at some prefix `i < k`. -/
theorem shieldedBalanceCapBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun b O =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_dl) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono ?_)
    (conservationRelOrBadChallenge_measure_le m gen v_idx r_idx queryOf P₀ toSig hne_idx k
      (hQ j) (hdl j))
  rintro ⟨O, s⟩ ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases shieldedBalanceCapViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) O s) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, e, he⟩
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
        (Or.inl (valueRelation_finder_isSome m gen v_idx r_idx queryOf P₀ toSig hne_idx hr
          (le_of_lt hik) hval hw))⟩))
  · rcases kappaEvent_subset m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        (extractFail_mem_kappaEvent m gen v_idx r_idx queryOf P₀ toSig
          ((halg j).atLabel) ((halg j).atOutput) hr (le_of_lt hik) hval he)
      with hbad | hrel
    · exact Or.inr hbad
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig (Or.inr hrel)⟩))

end Zcash.Security.Ledger.Model
