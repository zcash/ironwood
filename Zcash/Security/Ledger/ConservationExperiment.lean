import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ValueRelationArm

/-!
# The conservation experiment: both arms in one sample space

The capstones bound the conservation and cap violations by `ε_dlr + κ`, over an abstract
`PMF (ValidAnnotated …)` with the two arms' bounds as named hypotheses. (κ is the knowledge
error: the probability that a binding signature verifies while binding-key extraction fails —
see `Zcash.Security.RedDSA.KnowledgeError`.) This module instantiates that composition in
the challenge-oracle model, in one experiment: over the adversary's coins, the challenge
table, and the logs of the `m` presented bases, the probability that the output ledger is
valid *and* violates conservation (or the cap) at some prefix `i < k` is at most
`ε_dl + (qH+2)/#F`.

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

The same composition also runs at a single presented basis, with no log sampling
(`balanceConservationBefore_measure_le_experimentAt`). Both arms then live over the
challenge-table factor. The relation arm is a named hypothesis: the probability that the
combined finder returns a relation at that basis is at most `ε_valuedlr`. The bound is
`ε_valuedlr + (qH+1)/#F` — one `1/#F` less than the sampled form, because the relation arm
is assumed rather than discharged, so the Jaeger–Tessaro guessing loss does not arise.
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

/-- The fixed-basis experiment distribution: the adversary's coins `j` and a uniform
challenge table `Q → ZMod r`. No basis logs are sampled; the basis is a parameter of the
events run over this distribution. -/
noncomputable def challengeTableExperiment {ι : Type u} (p : PMF ι) :
    PMF (ι × (Q → ZMod r)) :=
  p.bind fun j => (PMF.uniformOfFintype (Q → ZMod r)).map (Prod.mk j)

omit [Inhabited Q] in
/-- The coins marginal of the fixed-basis experiment: mapping to the coin component
recovers the coin distribution. -/
theorem challengeTableExperiment_map_fst {ι : Type u} (p : PMF ι) :
    (challengeTableExperiment (Q := Q) (r := r) p).map Prod.fst = p := by
  rw [challengeTableExperiment, PMF.map_bind]
  simp only [PMF.map_comp,
    show ∀ j : ι, Prod.fst ∘ Prod.mk j = Function.const (Q → ZMod r) j from fun _ => rfl,
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

/-- The lift of a per-primitives ledger event at the presented `basis`: the samples on which
the adversary's output ledger, run at `primitivesAtBasis basis`, is valid and lands in
`Event` at those primitives. -/
def ledgerEventAt {ι : Type u} (basis : Fin m → G)
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (Event : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)) :
    Set (ι × (Q → ZMod r)) :=
  setOf fun x =>
    ∃ hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis x.2)
        kv issuance maxActions (((LA x.1 basis).run x.2).map Prod.fst),
      (⟨_, hval⟩ : ValidAnnotated (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis x.2)
          kv issuance maxActions)
        ∈ Event (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis x.2)

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- `ledgerEventAt` is monotone in the event family: it preserves `⊆`. -/
theorem ledgerEventAt_mono {ι : Type u} (basis : Fin m → G)
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    {E₁ E₂ : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)} (h : ∀ P, E₁ P ⊆ E₂ P) :
    ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA E₁
      ⊆ ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA E₂ :=
  fun _ ⟨hval, hx⟩ => ⟨hval, h _ hx⟩

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- `ledgerEventAt` preserves unions: it is a join-homomorphism, since the `∃ hval` that
lifts the event distributes over the disjunction. -/
theorem ledgerEventAt_union {ι : Type u} (basis : Fin m → G)
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (E₁ E₂ : ∀ P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG,
      Set (ValidAnnotated P kv issuance maxActions)) :
    ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA (fun P => E₁ P ∪ E₂ P)
      = ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA E₁
        ∪ ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA E₂ := by
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
    (table : Q → ZMod r) (basis : Fin m → G) :
    Option (AlgebraicRelationWitness (F := ZMod r) basis) :=
  valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis
    <|> relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) table basis

omit [Fintype Q] in
/-- The combined finder returns a relation whenever either arm's finder does. -/
theorem conservationRelFinder_isSome {hne_idx : v_idx ≠ r_idx} {k : ℕ}
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {table : Q → ZMod r} {basis : Fin m → G}
    (h : (valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis).isSome
      ∨ (relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
          table basis).isSome) :
    (conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis).isSome := by
  unfold conservationRelFinder
  rcases hv : valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis with _ | w
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
  {ω | (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun basis table =>
        conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis))}
    ∪ {ω | ω.1 ∈ badFiber m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) ω.2}

/-- **The per-coin discharge: one discrete-log bound covers both arms.** Within query budget
`qH`, the combined reduction's discharge event has measure at most `ε_dl + (qH+2)/#F`: the
relation slice at `ε_dl + 1/#F` (`relationWithCoins_prob_le_of_textbookDL`, applied once,
to the combined finder) and the bad-challenge fibre at `(qH+1)/#F`
(`badFiber_measure_le`). -/
theorem conservationRelOrBadChallenge_measure_le (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} (hQ : ∀ basis, (LA basis).QueryBound qH) {ε_dl : ℝ≥0∞}
    (hdl : TextbookDLWithCoinsAdvantageLE gen (fun basis table =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis) ε_dl) :
    (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
        (conservationRelOrBadChallenge m gen v_idx r_idx queryOf P₀ toSig hne_idx k LA)
      ≤ ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  have hrel : (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
      {ω : (Q → ZMod r) × (Fin m → ZMod r) |
        (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun basis table =>
          conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis))}
      ≤ ε_dl + 1 / Fintype.card (ZMod r) := by
    have hswap : (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).toOuterMeasure
        {ω : (Q → ZMod r) × (Fin m → ZMod r) |
          (ω.2, ω.1) ∈ ↑(relSetWithCoins gen (fun basis table =>
            conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis))}
        = (PMF.uniformOfFintype ((Fin m → ZMod r) × (Q → ZMod r))).toOuterMeasure
          ↑(relSetWithCoins gen (fun basis table =>
            conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis)) := by
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
      (fun logs => badFiber_measure_le m gen r_idx _
        (kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ _)))
  unfold conservationRelOrBadChallenge
  refine le_trans (MeasureTheory.measure_union_le _ _)
    (le_trans (add_le_add hrel hbad) (le_of_eq ?_))
  rw [add_assoc, ENNReal.div_add_div_same]
  push_cast
  ring_nf

/-- The relation event of the combined finder at the presented `basis`, over the
challenge-table factor: the event that the named value-DLR advantage bounds. -/
def conservationRelFiberAt (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (basis : Fin m → G) : Set (Q → ZMod r) :=
  {table | (conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA table basis).isSome}

/-- **The per-coin discharge event at the presented `basis`.** The combined finder's relation
event together with the knowledge-error bad-challenge event, both over the challenge-table
factor. Every violation sample at this basis lands here, and its measure is
`ε_valuedlr + (qH+1)/#F` (`conservationRelOrBadChallengeAt_measure_le`). -/
def conservationRelOrBadChallengeAt (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (basis : Fin m → G) : Set (Q → ZMod r) :=
  conservationRelFiberAt m v_idx r_idx queryOf P₀ toSig hne_idx k LA basis
    ∪ badFiberAt m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) basis

/-- **The per-coin discharge at a fixed basis: a union bound.** Within query budget `qH`, if
the combined finder returns a relation at the presented `basis` with probability at most
`ε_valuedlr` over the challenge table, the discharge event has measure at most
`ε_valuedlr + (qH+1)/#F`: the relation event is the named hypothesis, and the bad-challenge
event is the per-basis squeeze (`badFiberAt_measure_le`). No Jaeger–Tessaro guessing loss
arises, so the denominator term is `(qH+1)/#F` where the sampled form has `(qH+2)/#F`. -/
theorem conservationRelOrBadChallengeAt_measure_le (hne_idx : v_idx ≠ r_idx) (k : ℕ)
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} {qH : ℕ} (hQ : (LA basis).QueryBound qH) {ε_valuedlr : ℝ≥0∞}
    (hrel : (PMF.uniformOfFintype (Q → ZMod r)).toOuterMeasure
        (conservationRelFiberAt m v_idx r_idx queryOf P₀ toSig hne_idx k LA basis)
      ≤ ε_valuedlr) :
    (PMF.uniformOfFintype (Q → ZMod r)).toOuterMeasure
        (conservationRelOrBadChallengeAt m v_idx r_idx queryOf P₀ toSig hne_idx k LA basis)
      ≤ ε_valuedlr + ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) :=
  le_trans (MeasureTheory.measure_union_le _ _)
    (add_le_add hrel
      (badFiberAt_measure_le m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
        (kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig hQ)))

omit [Fintype Q] in
/-- **The per-coin conservation containment at a fixed basis.** A challenge table on
which coin `j`'s output ledger is valid at the presented basis and violates balance
conservation at some prefix `i < k` lands in the per-coin discharge event: the combined
finder returns a relation at this basis, or the table is bad for the machine's
challenge queries. -/
theorem conservationViolationAt_subset_dischargeAt {ι : Type u}
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} (hne_idx : v_idx ≠ r_idx)
    (halg : ∀ j : ι, AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) (j : ι) :
    (fun table => (j, table)) ⁻¹' ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
        (fun P => balanceConservationViolationBefore (P := P) (kv := kv)
          (issuance := issuance) (maxActions := maxActions) k) ⊆
      conservationRelOrBadChallengeAt m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j)
        basis := by
  rintro table ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases balanceConservationViolationBefore_subset_fallible
      (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
      (bindingAtBasis m v_idx r_idx queryOf P₀ toSig basis table) hr
      (extractorAtBasis m r_idx queryOf P₀ k (LA j) basis table) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, failure, hfailure⟩
  · exact Or.inl (conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
      (Or.inl (valueRelation_finder_isSomeAt m v_idx r_idx queryOf P₀ toSig hne_idx hr
        (le_of_lt hik) hval hw)))
  · rcases kappaEventAt_subset m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        basis
        (extractFail_mem_kappaEventAt m v_idx r_idx queryOf P₀ toSig
          (halg j) hr (le_of_lt hik) hval hfailure)
      with hbad | hrel'
    · exact Or.inr hbad
    · exact Or.inl (conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig (Or.inr hrel'))

omit [Fintype Q] in
/-- **The per-coin cap containment at a fixed basis.** As
`conservationViolationAt_subset_dischargeAt`, for the shielded pool exceeding the minted
issuance at some prefix `i < k`. -/
theorem shieldedBalanceCapViolationAt_subset_dischargeAt {ι : Type u}
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} (hne_idx : v_idx ≠ r_idx)
    (halg : ∀ j : ι, AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) (j : ι) :
    (fun table => (j, table)) ⁻¹' ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
        (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := kv)
          (issuance := issuance) (maxActions := maxActions) k) ⊆
      conservationRelOrBadChallengeAt m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j)
        basis := by
  rintro table ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases shieldedBalanceCapViolationBefore_subset_fallible
      (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
      (bindingAtBasis m v_idx r_idx queryOf P₀ toSig basis table) hr
      (extractorAtBasis m r_idx queryOf P₀ k (LA j) basis table) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, failure, hfailure⟩
  · exact Or.inl (conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
      (Or.inl (valueRelation_finder_isSomeAt m v_idx r_idx queryOf P₀ toSig hne_idx hr
        (le_of_lt hik) hval hw)))
  · rcases kappaEventAt_subset m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        basis
        (extractFail_mem_kappaEventAt m v_idx r_idx queryOf P₀ toSig
          (halg j) hr (le_of_lt hik) hval hfailure)
      with hbad | hrel'
    · exact Or.inr hbad
    · exact Or.inl (conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig (Or.inr hrel'))

/-- **The joint bad-challenge bound.** Over the coins and the challenge table, the event
that the table is bad for the sampled coin's machine at the presented basis has measure
at most `(qH+1)/#F`: the per-coin squeeze (`badFiberAt_measure_le`), integrated over the
coins. -/
theorem challengeTableExperiment_badFiberAt_measure_le {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} {qH : ℕ} (hQ : ∀ j, (LA j basis).QueryBound qH) (k : ℕ) :
    (challengeTableExperiment p).toOuterMeasure
        {x : ι × (Q → ZMod r) | x.2 ∈ badFiberAt m r_idx
          (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA x.1)) basis}
      ≤ ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  exact le_trans (MeasureTheory.measure_mono fun table ht => ht)
    (badFiberAt_measure_le m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
      (kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ j)))

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
    {qH : ℕ} (hQ : ∀ j basis, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun basis table =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) table basis) ε_dl) :
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
  rintro ⟨table, logs⟩ ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases balanceConservationViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig table logs)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig table logs) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) table logs) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, failure, hfailure⟩
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
        (Or.inl (valueRelation_finder_isSomeAt m v_idx r_idx queryOf P₀ toSig hne_idx hr
          (le_of_lt hik) hval hw))⟩))
  · rcases kappaEvent_subset m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        (mem_kappaEvent m gen r_idx _
          (extractFail_mem_kappaEventAt m v_idx r_idx queryOf P₀ toSig
            (halg j logs) hr (le_of_lt hik) hval hfailure))
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
    {qH : ℕ} (hQ : ∀ j basis, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun basis table =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) table basis) ε_dl) :
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
  rintro ⟨table, logs⟩ ⟨hval, hviol⟩
  dsimp only at hval hviol
  rcases shieldedBalanceCapViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig table logs)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig table logs) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) table logs) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, failure, hfailure⟩
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig
        (Or.inl (valueRelation_finder_isSomeAt m v_idx r_idx queryOf P₀ toSig hne_idx hr
          (le_of_lt hik) hval hw))⟩))
  · rcases kappaEvent_subset m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
        (mem_kappaEvent m gen r_idx _
          (extractFail_mem_kappaEventAt m v_idx r_idx queryOf P₀ toSig
            (halg j logs) hr (le_of_lt hik) hval hfailure))
      with hbad | hrel
    · exact Or.inr hbad
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        conservationRelFinder_isSome m v_idx r_idx queryOf P₀ toSig (Or.inr hrel)⟩))

/-- **The conservation experiment at a fixed basis.** Over the adversary's coins and the
challenge table alone, at the presented `basis`, the probability that the output ledger is
valid and violates balance conservation at some prefix `i < k` is at most
`ε_valuedlr + (qH+1)/#F`. The relation arm is the named per-coin hypothesis `hrel`: the
combined finder returns a relation at this basis with probability at most `ε_valuedlr`.
The algebraicity hypothesis is likewise needed only at this basis. -/
theorem balanceConservationBefore_measure_le_experimentAt {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ)
    {ε_valuedlr : ℝ≥0∞}
    (hrel : ∀ j : ι, (PMF.uniformOfFintype (Q → ZMod r)).toOuterMeasure
        (conservationRelFiberAt m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) basis)
      ≤ ε_valuedlr) :
    (challengeTableExperiment p).toOuterMeasure
        (ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_valuedlr + ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  exact le_trans (MeasureTheory.measure_mono
      (conservationViolationAt_subset_dischargeAt m v_idx r_idx queryOf P₀ toSig hne_idx
        halg hr k j))
    (conservationRelOrBadChallengeAt_measure_le m v_idx r_idx queryOf P₀ toSig hne_idx k
      (hQ j) (hrel j))

/-- **The cap experiment at a fixed basis.** As
`balanceConservationBefore_measure_le_experimentAt`, for the shielded pool exceeding the
minted issuance at some prefix `i < k`. -/
theorem shieldedBalanceCapBefore_measure_le_experimentAt {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ)
    {ε_valuedlr : ℝ≥0∞}
    (hrel : ∀ j : ι, (PMF.uniformOfFintype (Q → ZMod r)).toOuterMeasure
        (conservationRelFiberAt m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) basis)
      ≤ ε_valuedlr) :
    (challengeTableExperiment p).toOuterMeasure
        (ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_valuedlr + ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  exact le_trans (MeasureTheory.measure_mono
      (shieldedBalanceCapViolationAt_subset_dischargeAt m v_idx r_idx queryOf P₀ toSig
        hne_idx halg hr k j))
    (conservationRelOrBadChallengeAt_measure_le m v_idx r_idx queryOf P₀ toSig hne_idx k
      (hQ j) (hrel j))

omit [DecidableEq G] in
/-- **The standalone value-DLR game priced at textbook discrete log — the isolated
Jaeger–Tessaro terminal step.** At the two named value-base slots (`ValueBaseIndex`), a
finder's probability of returning a nontrivial relation over bases programmed from the
DL challenge is at most `ε + 1/#F`.
This states what the named `ε_valuedlr` costs against textbook discrete log. The deployed
experiments deliberately do not take this step: a programmed basis is inconsistent with the
deployed one, so they carry `ε_valuedlr` as the named advantage at the deployed bases, and
this pricing stands alone on the programmed relation game. -/
theorem valueRelationWithCoins_prob_le_of_textbookDL {ρ : Type*}
    [Fintype ρ] [Nonempty ρ] [DecidableEq ρ] (B : G)
    (finder : (b : BasisIndex 0 ValueBaseIndex → G) → ρ →
      Option (AlgebraicRelationWitness (F := ZMod r) b))
    {ε : ℝ≥0∞} (hdl : TextbookDLWithCoinsAdvantageLE B finder ε) :
    (PMF.uniformOfFintype ((BasisIndex 0 ValueBaseIndex → ZMod r) × ρ)).toOuterMeasure
        (relSetWithCoins B finder)
      ≤ ε + 1 / Fintype.card (ZMod r) :=
  relationWithCoins_prob_le_of_textbookDL B finder hdl

end Zcash.Security.Ledger.Model
