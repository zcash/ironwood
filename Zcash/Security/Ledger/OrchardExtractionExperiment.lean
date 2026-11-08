import Zcash.Security.Ledger.AdaptiveActionBundleBridge
import Zcash.Security.Ledger.AdaptiveActionReduction
import Zcash.Security.Ledger.OrchardIntegrityExperiment
import Zcash.Snark.Capstones.Action

/-!
# The Orchard extraction experiment

Compose the ledger games with the Action circuit's knowledge extractor.

The `_idealizedks` experiments quantify over witness-annotated adversaries: every
action of the output chain carries the witness for the Action statement. This module
builds that annotated adversary from a proof-emitting one. The composed adversary's
proofs come from one shared adaptive-count Action execution
(`AdaptiveActionReduction.Family`): one online-AGM adversary, one random-oracle table,
and one query budget produce the proofs at every chain position, and each position's
action count is part of that execution's output. The sample space adds the generator
table and that one shared transcript table; the annotations are computed by the
composed ledger extractor (`selectedLedgerExtractor`) from the sampled run.

Two facts shape the composition. First, consensus validity is public: structural
validity, type checks on public data, and verification of the proofs and signatures.
Nothing in it speaks about openings of commitments or extracted witnesses. Second,
the annotations cannot be a function of the public chain: the commitments are
perfectly hiding, so which opening a chain "contains" is well-defined only relative
to a prover execution. The constructed adversary's annotations are therefore a
function of its coins —which include the sampled run— and that is the only shape a
sound composition can take.

The oracle of this model is the typed squeeze on transcript elements, over one domain
large enough for every permitted action count (`AdaptiveActionCountTranscript`). Every
count's schedule reads the same table, so no per-size presentation of the oracle is
involved, and the count may depend on earlier oracle answers.

The bounds follow the recipe of the book's Security Models page. The computable
reductions compose first: `combinedRelationFinder` returns the first relation that any
chain position's run exposes, and `selectedLedgerExtractor` turns a position's accepted
proof into its ledger data or a Sinsemilla escape. The set-level containments come next
(`runExtractionFailureEvent_subset`, and the `…_subset` lemmas of
`AdaptiveActionReduction`), holding for every sample. Probability enters once, at the
end: `Family.orchardEvent` lifts an event from the group basis to the generator table,
the lift is a preimage and so preserves inclusions and unions, and
`runsLaw_measure_orchardEvent` carries its measure to the uniform scalar sample, where
monotonicity and subadditivity give the sum. So the discrete-log term is charged once,
for the combined finder (one `TextbookDLWithCoinsAdvantageLE` hypothesis), and only the
selected count's statistical surfaces and the ledger-bridge escapes keep a union bound
over the chain positions. Neither `numChainPositions` nor `maxActions` multiplies the
discrete-log term. The generator queries are indexed by `ActionBasisIndex`, the
circuit's basis index.

The bound `ε_stat` on the statistical surfaces of the selected count (`hstat`) is a
hypothesis of the endpoints here. The surfaces are the four of the fixed-count families:
`z = 0`, the IPA binding discrepancy, a failed deployed-root check, and the five Action
semantic surfaces. The fixed-count capstone bounds them by the query budget plus one,
times a sum of surface degrees over `|Fp|`
(`orchard_action_adaptiveStatement_knowledge_error_bound`), which is far below the
discrete-log term for any feasible query budget. The same bound, with the degrees taken
at the largest count, is expected for the shared execution and is not yet proved; until
it is, the endpoints take `ε_stat` as a parameter, and a reader should judge them with
that expected size in mind.

The composed endpoints run at the deployed value bases (`deployedViolationEvent` over
`deployedExperiment`): the extracted witnesses open the value commitments at the
deployed bases, and validity is stated at exactly those bases, so the violation arm
is inhabited by the chains the extractor actually produces. Only the binding
challenge hash is idealized as the table, and the conservation side's relation arm is
the named `ε_valuedlr` of the exhibited deployed finder. The `_combinedDLR` endpoints
carry every ledger-side relation arm —the bridge escapes, the Sinsemilla relation, and
the value relation— in one term (`combinedDLRAdvantage`).
-/

open scoped ENNReal

namespace Zcash.Security.Ledger.OrchardExtractionExperiment

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.AdaptiveActionBundleBridge
open Zcash.Security.Ledger.AdaptiveActionReduction
open Zcash.Security.Ledger.Bridge
open Zcash.Security.Ledger.Model
open Zcash.Security.Ledger.Pool
open Zcash.Snark.ActionTerminal

namespace Family

/-- The runs component of the composed sample: the generator table paired with the one
shared adaptive-count oracle table. One table serves every action count, so the sample
has no component per count: the adversary cannot obtain a fresh table by changing its
count, and the discrete-log hypothesis is stated once, over this one table. -/
abbrev Runs {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) {T : Type*} [DecidableEq T]
    (_query : ActionBasisIndex → T) :=
  (↥(Set.range _query) → VestaG) × family.Coins

/-- The law of the runs component: a uniform generator table and a uniform shared
transcript table. -/
noncomputable def runsLaw {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) {T : Type*} [DecidableEq T]
    (query : ActionBasisIndex → T) : PMF (Runs family query) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)

/-- The lift of a reduction-layer event, stated over the group basis, to the generator
table: a preimage, so it preserves inclusions and unions. -/
def orchardEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) {T : Type*} [DecidableEq T]
    (query : ActionBasisIndex → T)
    (event : Set family.GroupSample) : Set (Runs family query) :=
  (fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' event

/-- A reduction-layer event has the same measure under the runs law as its scalar-basis
form has under the uniform scalar sample, by the uniform-URS identification of the
generator random oracle. -/
theorem runsLaw_measure_orchardEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : ActionBasisIndex → T)
    (hquery : Function.Injective query) (event : Set family.GroupSample) :
    (runsLaw family query).toOuterMeasure (orchardEvent family query event) =
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B event) := by
  unfold runsLaw orchardEvent
  exact uniformURS_basis_transfer (orchardGeneratorROSetup query) B
    (orchardGeneratorROBasis query) event
    (orchard_uniformURSIdentification_of_generatorRO actionCircuit.shape.k B hB query hquery)

/-- The extraction-failure arm at the reduction layer, over the generator table:
selected-count knowledge failure or a supplied ledger-bridge escape at one of the
emitted chain positions. -/
def extractionFailureEvent {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions) {T : Type*} [DecidableEq T]
    (query : ActionBasisIndex → T)
    (escape : Fin numChainPositions → Set family.GroupSample) : Set (Runs family query) :=
  orchardEvent family query (family.ledgerExtractionFailureEvent escape)

/-- **Extraction failure with no `numChainPositions * maxActions` discrete-log loss.**
The bound is `(DLOG + 1 / |Fp|) + numChainPositions * (statistical error + bridge escape)`:
no term is multiplied by `maxActions`, and `numChainPositions` does not multiply the
discrete-log term. `maxActions` can enter only through `ε_stat`, the bound on the selected
count's statistical surfaces, whose expected size the module doc gives. -/
theorem extractionFailureEvent_measure_le {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : ActionBasisIndex → T)
    (hquery : Function.Injective query)
    (escape : Fin numChainPositions → Set family.GroupSample)
    {dlBound ε_stat ε_escape : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (escape position)) ≤ ε_escape) :
    (runsLaw family query).toOuterMeasure
        (extractionFailureEvent family query escape) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (numChainPositions : ℝ≥0∞) * (ε_stat + ε_escape) := by
  unfold extractionFailureEvent
  rw [runsLaw_measure_orchardEvent family B hB query hquery]
  exact family.ledgerExtractionFailureEvent_prob_le B escape hDL hstat hescape

/-- The knowledge arm alone at the reduction layer: the selected-count knowledge failures
of the emitted chain positions, bounded by the one discrete-log term and the
per-position statistical residual. -/
theorem knowledgeFailureEvent_measure_le {numChainPositions maxActions : ℕ}
    (family : Family numChainPositions maxActions)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : ActionBasisIndex → T)
    (hquery : Function.Injective query)
    {dlBound ε_stat : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat) :
    (runsLaw family query).toOuterMeasure
        (orchardEvent family query family.ledgerKnowledgeFailureEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * ε_stat := by
  rw [runsLaw_measure_orchardEvent family B hB query hquery]
  exact family.ledgerKnowledgeFailureEvent_prob_le B hDL hstat

end Family

/-! ## The proof-emitting ledger adversary -/

/-- The transaction-level data the ledger machine supplies for one chain position: the
declared transaction fields and a signature for every possible action position. The
action count is not requested: the shared Action execution selects it, and only the
selected prefix of `sigs` is consumed. The action instances and witnesses come from the
selected count's extracted ledger data. -/
structure TxRequest (MSG : Type) (maxActions : ℕ) where
  /-- The spend-authorization signature at each possible action position. -/
  sigs : Fin maxActions → RedDSA.Sig Fq PallasGroup
  /-- The declared net value leaving the pool. -/
  vBalance : ℤ
  /-- The sighash the transaction's signatures are over. -/
  sighash : MSG
  /-- The binding signature. -/
  bindingSig : RedDSA.Sig Fq PallasGroup

/-- **The proof-emitting balance adversary model, as a type.** One shared adaptive-count
Action execution (`actionFamily`) produces the proofs at every chain position and
selects each position's action count; the ledger machine (`machine`) sees the generator
table, the whole sampled transcript table, and the presented bases, and requests one
transaction per position. It cannot resample a transcript for a different position or
count. The witness annotations are not part of this model: the composition computes
them by extraction. -/
structure ExtractionBalanceAdversary (MSG : Type) [Fintype MSG] [DecidableEq MSG]
    [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    {T : Type} [DecidableEq T] (query : ActionBasisIndex → T)
    (numChainPositions maxActions : ℕ) : Type 1 where
  /-- The adversary's coin space. -/
  ι : Type
  /-- The coin distribution. -/
  coins : PMF ι
  /-- The shared adaptive-count Action execution producing every chain position's proof. -/
  actionFamily : AdaptiveActionReduction.Family numChainPositions maxActions
  /-- The ledger machine: from the coins, the sampled run, and the presented bases,
  request one transaction per chain position, with its announced binding
  representation. -/
  machine : ι → (table : ↥(Set.range query) → VestaG) → actionFamily.Coins →
    (Fin 2 → PallasGroup) →
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (TxRequest MSG maxActions × QueryRep Fq 2))
  /-- The challenge-oracle query budget. -/
  qH : ℕ
  /-- The ledger machine respects the budget at every input. -/
  queryBound : ∀ j table O b, (machine j table O b).QueryBound qH

namespace ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : ActionBasisIndex → T}
  {numChainPositions maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query numChainPositions maxActions)

/-- The deployed annotated transaction type the assembled chain carries. -/
abbrev AnnotatedTx :=
  Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Pool.Encoding
    MSG (RedDSA.Sig Fq PallasGroup)
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth

/-- The runs component of the composed sample: the generator table and the one shared
transcript table. -/
abbrev Runs := Family.Runs A.actionFamily query

/-- Assemble one transaction at one chain position: extract that position's ledger data
at its selected action count from the shared run, and zip it with the requested
signatures. Returns nothing exactly when the composed extractor does: when the selected
proof's knowledge extraction fails, or a member of the extracted bundle escapes the
bridge. The assembled chain then stops at this position, and such samples are counted in
the extraction-failure arm of the composed bound rather than judged by ledger validity. -/
def assembleTx (r : Runs A) (position : Fin numChainPositions) (req : TxRequest MSG maxActions) :
    Option (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind) :=
  let family := A.actionFamily.positionFamily position
  let basis := orchardGeneratorROBasis query r.1
  let selected := (family.cachedExecution basis r.2).1
  match selectedLedgerExtractor family spendAuthVerify (redPallasBindingVerify H_bind)
      basis r.2 with
  | none => none
  | some members =>
      some { actions := (List.finRange (selected.count.1 + 1)).map fun i =>
               { inst := (members i).success.inst
                 w := (members i).success.w
                 sig := req.sigs (i.castLE (Nat.succ_le_of_lt selected.count.isLt)) }
             vBalance := req.vBalance
             sighash := req.sighash
             bindingSig := req.bindingSig }

/-- Assemble the annotated chain: process the requests at successive chain positions,
and stop at the first position whose extraction fails. The samples cut short here are
exactly the samples that the extraction-failure arm of the composed experiment
covers. -/
def assembleChain (r : Runs A) :
    ℕ → List (TxRequest MSG maxActions × QueryRep Fq 2) →
      List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind × QueryRep Fq 2)
  | _, [] => []
  | position, (req, rep) :: rest =>
      if hposition : position < numChainPositions then
        match assembleTx H_bind A r ⟨position, hposition⟩ req with
        | none => []
        | some tx => (tx, rep) :: assembleChain r (position + 1) rest
      else []

/-- The constructed annotated adversary's machine: run the ledger machine on the
sampled run and annotate its output by extraction. -/
def toLA (x : A.ι × Runs A) (b : Fin 2 → PallasGroup) :
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind ×
        QueryRep Fq 2)) :=
  (A.machine x.1 x.2.1 x.2.2 b).bind fun out =>
    .pure (assembleChain H_bind A x.2 0 out)

/-- The assembled machine keeps the ledger machine's query budget: annotating the
output by extraction adds no challenge-oracle queries. -/
theorem toLA_queryBound (x : A.ι × Runs A) (b : Fin 2 → PallasGroup) :
    (toLA H_bind A x b).QueryBound A.qH := by
  unfold toLA
  simp only [LabeledOracleComp.QueryBound, LabeledOracleComp.erase_bind]
  exact (OracleComp.queryBound_bind (A.queryBound x.1 x.2.1 x.2.2 b)
    (fun a => .pure _ 0)).mono (by omega)

/-- The law of the runs component: a uniform generator table and a uniform shared
transcript table. -/
noncomputable def runsLaw : PMF (Runs A) :=
  Family.runsLaw A.actionFamily query

/-- **The composed adversary as an idealized annotated adversary.** Its coins are the
ledger machine's coins together with the sampled run, and the annotations are computed
by the composed extractor, a function of those coins, as the module doc explains they
must be. The query bound is supplied for the assembled machine; the algebraicity
obligation at every presented basis is a hypothesis. -/
noncomputable def toIdealizedKS
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j)) :
    IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind where
  ι := A.ι × Runs A
  coins := independentProductPMF A.coins (runsLaw A)
  LA := toLA H_bind A
  qH := A.qH
  queryBound := toLA_queryBound H_bind A
  algebraic := halg

/-- The extraction-failure event of one chain position, over the group basis and the
shared table: the selected proof is accepted, and the composed extractor returns
nothing. -/
def positionExtractionFailure (position : Fin numChainPositions) :
    Set A.actionFamily.GroupSample :=
  {p | (A.actionFamily.positionFamily position).selectedAccepts p.1 p.2 ∧
    selectedLedgerExtractor (A.actionFamily.positionFamily position) spendAuthVerify
      (redPallasBindingVerify H_bind) p.1 p.2 = none}

/-- The event that one chain position's selected proof is accepted and a member of its
extracted bundle escapes the bridge. -/
def positionEscape (position : Fin numChainPositions) : Set A.actionFamily.GroupSample :=
  {p | (A.actionFamily.positionFamily position).selectedAccepts p.1 p.2 ∧
    (selectedLedgerEscapeFinder (A.actionFamily.positionFamily position) spendAuthVerify
      (redPallasBindingVerify H_bind) p.1 p.2).isSome}

/-- One chain position's extraction failure decomposes into its selected-count
knowledge failure and its computed ledger escape (`selectedLedgerExtractor_eq_none_iff`). -/
theorem positionExtractionFailure_subset (position : Fin numChainPositions) :
    positionExtractionFailure H_bind A position ⊆
      (A.actionFamily.positionFamily position).selectedKnowledgeFailureEvent ∪
        positionEscape H_bind A position := by
  rintro p ⟨hacc, hnone⟩
  rcases (selectedLedgerExtractor_eq_none_iff (A.actionFamily.positionFamily position)
      spendAuthVerify (redPallasBindingVerify H_bind) p.1 p.2).mp hnone with h | h
  · exact Or.inl ⟨hacc, h⟩
  · exact Or.inr ⟨hacc, h⟩

/-- Extraction failure at some emitted chain position, over the runs component. -/
def runExtractionFailureEvent : Set (Runs A) :=
  Family.orchardEvent A.actionFamily query
    (A.actionFamily.ledgerFailureEvent (positionExtractionFailure H_bind A))

/-- The knowledge arm over the runs component: selected-count knowledge failure at some
emitted chain position. -/
def runKnowledgeFailureEvent : Set (Runs A) :=
  Family.orchardEvent A.actionFamily query A.actionFamily.ledgerKnowledgeFailureEvent

/-- The escape arm over the runs component: a computed ledger escape at some emitted
chain position. -/
def runEscapeEvent : Set (Runs A) :=
  Family.orchardEvent A.actionFamily query
    (A.actionFamily.ledgerFailureEvent (positionEscape H_bind A))

/-- Extraction failure at the run level is covered by the reduction layer's
knowledge-or-escape event. -/
theorem runExtractionFailureEvent_subset :
    runExtractionFailureEvent H_bind A ⊆
      Family.extractionFailureEvent A.actionFamily query (positionEscape H_bind A) := by
  unfold runExtractionFailureEvent Family.extractionFailureEvent Family.orchardEvent
  apply Set.preimage_mono
  intro p hp
  obtain ⟨position, hposition⟩ := Set.mem_iUnion.mp hp
  exact Set.mem_iUnion.mpr
    ⟨position, positionExtractionFailure_subset H_bind A position hposition⟩

/-- Extraction failure at the run level is covered by the knowledge arm and the escape
arm. -/
theorem runExtractionFailureEvent_subset_knowledge_union_escape :
    runExtractionFailureEvent H_bind A ⊆
      runKnowledgeFailureEvent A ∪ runEscapeEvent H_bind A := by
  unfold runExtractionFailureEvent runKnowledgeFailureEvent runEscapeEvent
    Family.orchardEvent
  rw [← Set.preimage_union]
  apply Set.preimage_mono
  intro p hp
  obtain ⟨position, hposition⟩ := Set.mem_iUnion.mp hp
  rcases positionExtractionFailure_subset H_bind A position hposition with h | h
  · exact Or.inl (Set.mem_iUnion.mpr ⟨position, h⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨position, h⟩)

/-- The extraction-failure arm of the composed experiment: some emitted chain
position's selected proof is accepted and its composed extractor returns nothing. -/
def extractionFailureEvent :
    Set ((A.ι × Runs A) × (OrchardQuery MSG → Fq)) :=
  (fun x => x.1.2) ⁻¹' runExtractionFailureEvent H_bind A

/-- An event that reads only the runs component has the same measure under the
composed deployed experiment as under the runs law. -/
theorem deployedExperiment_measure_runs
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (E : Set (Runs A)) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹' E) =
      (runsLaw A).toOuterMeasure E := by
  have hfst : (toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst =
      independentProductPMF A.coins (runsLaw A) :=
    challengeTableExperiment_map_fst _
  have hsnd : (independentProductPMF A.coins (runsLaw A)).map Prod.snd = runsLaw A :=
    independentProductPMF_map_snd _ _
  have hmap : (toIdealizedKS H_bind A halg).deployedExperiment.map
      (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) = runsLaw A := by
    have hcomp : ((toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst).map
        Prod.snd =
        (toIdealizedKS H_bind A halg).deployedExperiment.map (Prod.snd ∘ Prod.fst) :=
      PMF.map_comp _ _ _
    calc (toIdealizedKS H_bind A halg).deployedExperiment.map
          (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2)
        = (toIdealizedKS H_bind A halg).deployedExperiment.map
            (Prod.snd ∘ Prod.fst) := rfl
      _ = ((toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst).map
            Prod.snd := hcomp.symm
      _ = runsLaw A := by rw [hfst, hsnd]
  calc (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹' E)
      = ((toIdealizedKS H_bind A halg).deployedExperiment.map
          (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2)).toOuterMeasure
          E :=
        (PMF.toOuterMeasure_map_apply _ _ _).symm
    _ = (runsLaw A).toOuterMeasure E := by rw [hmap]

/-- **The extraction-failure arm of the composed experiment.** The discrete-log term
is charged once, for the combined relation finder of the shared execution;
`numChainPositions` multiplies only the selected-count statistical surface and the
computed bridge escape, and no term is multiplied by `maxActions`, which can enter only
through `ε_stat` (whose expected size the module doc gives). -/
theorem extractionFailureEvent_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    {dlBound ε_stat ε_escape : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (positionEscape H_bind A position)) ≤ ε_escape) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (numChainPositions : ℝ≥0∞) * (ε_stat + ε_escape) := by
  refine le_trans (le_of_eq (deployedExperiment_measure_runs H_bind A halg _)) ?_
  refine le_trans (MeasureTheory.measure_mono (runExtractionFailureEvent_subset H_bind A)) ?_
  exact Family.extractionFailureEvent_measure_le A.actionFamily B hB query hquery
    (positionEscape H_bind A) hDL hstat hescape

/-- The knowledge arm of the composed experiment, bounded on its own by the one
discrete-log term and each chain position's statistical residual. -/
theorem knowledgeFailure_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    {dlBound ε_stat : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹'
          runKnowledgeFailureEvent A) ≤
      (dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * ε_stat := by
  refine le_trans (le_of_eq (deployedExperiment_measure_runs H_bind A halg _)) ?_
  exact Family.knowledgeFailureEvent_measure_le A.actionFamily B hB query hquery hDL hstat

end ExtractionBalanceAdversary

section Endpoints

open ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : ActionBasisIndex → T}
  {numChainPositions maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query numChainPositions maxActions)

/-- **Balance integrity for the proof-emitting adversary, at deployed Orchard.**
Except with probability at most the bound, every emitted chain position whose selected
proof the verifier accepts yields extracted ledger data, and the annotated chain
assembled from that data —whenever it validates at the deployed value bases— satisfies
balance integrity at every prefix below `numChainPositions`.

The event's validity conjunct is consensus validity together with the assembled
annotations. Consensus validity itself is public and says nothing about openings; the
annotations are computed by the composed extractor from the sampled run (module doc).
The composed statement is at the deployed value bases: the extracted witnesses open
the value commitments at exactly the bases where validity is stated
(`deployedViolationEvent`), so no reference-string heuristic is involved on the value
side.

`hDL` is the one discrete-log hypothesis, on the combined relation finder of the shared
Action execution; `hstat` bounds the selected count's statistical surfaces at each
chain position, and `hescape` each position's Sinsemilla-escape event. The model's
query budget `qH` —respected by the `queryBound` field— is what the bound's `(qH+1)/#F`
term counts; `halg` is the algebraicity restriction at every presented basis. The
remaining hypotheses and the second summand are the deployed KS-idealized integrity
endpoint's, applied at the constructed adversary. -/
theorem orchardBalanceIntegrityExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat ε_escape ε_sinsemilladlr ε_valuedlr : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (positionEscape H_bind A position)) ≤ ε_escape)
    (hsin : (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
      ((toIdealizedKS H_bind A halg).deployedSinsemillaRelationEvent issuance
        maxActions numChainPositions)
      ≤ ε_sinsemilladlr)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder numChainPositions j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * (ε_stat + ε_escape)) +
        (ε_sinsemilladlr + (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq)) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg B hB hquery hDL hstat hescape)
    (orchardBalanceIntegrity_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax numChainPositions hsin hrel)

/-- **Balance conservation for the proof-emitting adversary, at deployed Orchard.**
As the integrity endpoint (`orchardBalanceIntegrityExtraction_measure_le`), covering
the conservation violation alone; the second summand is the deployed KS-idealized
conservation endpoint's bound. -/
theorem orchardBalanceConservationExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat ε_escape ε_valuedlr : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (positionEscape H_bind A position)) ≤ ε_escape)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder numChainPositions j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * (ε_stat + ε_escape)) +
        (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg B hB hquery hDL hstat hescape)
    (orchardBalanceConservation_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax numChainPositions hrel)

/-- **Shielded balance cap for the proof-emitting adversary, at deployed Orchard.**
As the conservation endpoint, for the shielded pool exceeding the minted issuance at
some prefix below `numChainPositions`. -/
theorem orchardShieldedBalanceCapExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat ε_escape ε_valuedlr : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat)
    (hescape : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (positionEscape H_bind A position)) ≤ ε_escape)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder numChainPositions j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * (ε_stat + ε_escape)) +
        (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg B hB hquery hDL hstat hescape)
    (orchardShieldedBalanceCap_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax numChainPositions hrel)

/-- **The combined DLR event.** Some emitted chain position's selected proof is accepted
and its extracted bundle escapes the bridge, the constructed adversary's valid chain
computes a Sinsemilla relation at some prefix below `numChainPositions`, or the
value-DLR finder returns a relation. On every sample here the adversary's own data
computes a nontrivial relation over the combined deployed basis (`orchardPoints`). -/
def combinedDLREvent
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) :
    Set ((A.ι × Runs A) × (OrchardQuery MSG → Fq)) :=
  ((fun x => x.1.2) ⁻¹' runEscapeEvent H_bind A) ∪
  ((toIdealizedKS H_bind A halg).deployedSinsemillaRelationEvent issuance maxActions
      numChainPositions ∪
    {x | ((toIdealizedKS H_bind A halg).valueDLRFinder numChainPositions x.1 x.2).isSome})

/-- **The combined DLR advantage**, the single ledger-side relation term of the
`_combinedDLR` endpoints: the probability that the composed deployed experiment lands
in `combinedDLREvent`. -/
noncomputable def combinedDLRAdvantage
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) : ℝ≥0∞ :=
  (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
    (combinedDLREvent H_bind A halg issuance)

/-- **Balance integrity for the proof-emitting adversary, at the combined deployed
basis.** As `orchardBalanceIntegrityExtraction_measure_le`, with the ledger-side
relation arms carried by the one combined term (`combinedDLRAdvantage`): the Action
discrete-log term is charged once, `numChainPositions` multiplies only the selected
count's statistical residual, the escape union is one event inside the combined term,
and the only counting term outside is the challenge-oracle squeeze `(qH+1)/#F`. -/
theorem orchardBalanceIntegrityExtraction_measure_le_combinedDLR
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * ε_stat) +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) numChainPositions) ⊆
      ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹'
        runKnowledgeFailureEvent A) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id numChainPositions
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · rcases runExtractionFailureEvent_subset_knowledge_union_escape H_bind A hx with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    · rcases balanceIntegrityAt_subset 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          orchardValueBases (toIdealizedKS H_bind A halg).LA numChainPositions hx with harm | hcons
      · exact Or.inr (Or.inl (Or.inr (Or.inl
          (balanceSubsetArmsAt_subset_orchardRelation spendAuthVerify
            (redPallasBindingVerify H_bind) issuance maxActions 2 0 1 orchardQueryOf id
            (toIdealizedKS H_bind A halg).LA orchardValueBases numChainPositions harm))))
      · rcases conservationViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
            (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
            (by decide)
            (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
            (orchard_ledger_no_overflow hmax) numChainPositions x.1 hcons with hfib | hbad
        · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
              numChainPositions x.1 table).isSome} :=
            (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
              numChainPositions x.1 ▸ hfib
          exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
        · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (knowledgeFailure_measure_le H_bind A halg B hB hquery hDL hstat) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) numChainPositions

/-- **Balance conservation for the proof-emitting adversary, at the combined deployed
basis.** As the integrity form
(`orchardBalanceIntegrityExtraction_measure_le_combinedDLR`), for the conservation
violation alone. -/
theorem orchardBalanceConservationExtraction_measure_le_combinedDLR
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * ε_stat) +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) numChainPositions) ⊆
      ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹'
        runKnowledgeFailureEvent A) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id numChainPositions
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · rcases runExtractionFailureEvent_subset_knowledge_union_escape H_bind A hx with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    · rcases conservationViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          (by decide)
          (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
          (orchard_ledger_no_overflow hmax) numChainPositions x.1 hx with hfib | hbad
      · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
            numChainPositions x.1 table).isSome} :=
          (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
            numChainPositions x.1 ▸ hfib
        exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
      · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (knowledgeFailure_measure_le H_bind A halg B hB hquery hDL hstat) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) numChainPositions

/-- **Shielded balance cap for the proof-emitting adversary, at the combined deployed
basis.** As the conservation form, for the shielded pool exceeding the minted issuance
at some prefix below `numChainPositions`. -/
theorem orchardShieldedBalanceCapExtraction_measure_le_combinedDLR
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0) (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {dlBound ε_stat : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ position,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.positionFamily position).selectedStatisticalFailureEvent) ≤ ε_stat) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) numChainPositions)) ≤
      ((dlBound + 1 / Fintype.card Fp) + (numChainPositions : ℝ≥0∞) * ε_stat) +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) numChainPositions) ⊆
      ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) => x.1.2) ⁻¹'
        runKnowledgeFailureEvent A) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id numChainPositions
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · rcases runExtractionFailureEvent_subset_knowledge_union_escape H_bind A hx with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    · rcases shieldedBalanceCapViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          (by decide)
          (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
          (orchard_ledger_no_overflow hmax) numChainPositions x.1 hx with hfib | hbad
      · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
            numChainPositions x.1 table).isSome} :=
          (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
            numChainPositions x.1 ▸ hfib
        exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
      · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (knowledgeFailure_measure_le H_bind A halg B hB hquery hDL hstat) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) numChainPositions

end Endpoints

end Zcash.Security.Ledger.OrchardExtractionExperiment
