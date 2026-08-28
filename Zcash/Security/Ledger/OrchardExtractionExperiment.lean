import Zcash.Security.Ledger.AdaptiveActionBundleBridge
import Zcash.Security.Ledger.AdaptiveActionReduction
import Zcash.Security.Ledger.OrchardIntegrityExperiment
import Zcash.Snark.Capstones.Action

/-!
# Orchard extraction with adaptive Action counts

This file wires the issue #214 adaptive-count reduction into the proof-emitting
Orchard ledger experiment. One shared random-oracle table drives every emitted
slot, and each slot selects its Action count inside that computation. The
selected witnesses are refined to ledger data and used to construct the
witness-annotated adversary consumed by the existing ledger games.

The combined Action relation finder is charged to DLOG once. Only the
selected-count statistical surfaces and ledger-bridge escapes retain a
per-slot union bound. The fixed-count SNARK endpoints themselves are unchanged;
the improvement is in their composition at the ledger boundary.
-/

open scoped ENNReal

namespace Zcash.Security.Ledger.OrchardExtractionExperiment

open Zcash.Common
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common.LabeledOracleComp
open Zcash.Security.BindingSignature
open Zcash.Security.Concrete
open Zcash.Security.Ledger.AdaptiveActionBundleBridge
open Zcash.Security.Ledger.AdaptiveActionReduction
open Zcash.Security.Ledger.Bridge
open Zcash.Security.Ledger.Model
open Zcash.Security.Ledger.Pool
open Zcash.Security.RedDSA
open Zcash.Snark

namespace Family

/-- Orchard generator-table sample paired with the one shared adaptive Action
oracle table. There is no product over Action counts. -/
abbrev Runs {k maxActions : ℕ} (family : Family k maxActions)
    {T : Type*} [DecidableEq T]
    (_query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T) :=
  (↥(Set.range _query) → VestaG) × family.Coins

/-- The concrete Orchard law for the shared ledger extraction run. -/
noncomputable def runsLaw {k maxActions : ℕ} (family : Family k maxActions)
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T) : PMF (Runs family query) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)

/-- Pull a reduction-layer event back to Orchard's generator-oracle sample. -/
def orchardEvent {k maxActions : ℕ} (family : Family k maxActions)
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (event : Set family.GroupSample) : Set (Runs family query) :=
  (fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' event

/-- The concrete Orchard extraction-failure arm: selected Action knowledge
failure or a supplied ledger-bridge escape at one of the emitted slots. -/
def extractionFailureEvent {k maxActions : ℕ} (family : Family k maxActions)
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (escape : Fin k → Set family.GroupSample) : Set (Runs family query) :=
  orchardEvent family query (family.ledgerExtractionFailureEvent escape)

/-- **Concrete Orchard ledger extraction with no `k * maxActions` DLOG loss.**

The result is

`(DLOG + 1 / |Fp|) + k * (Action statistical error + bridge escape)`.

In particular, `maxActions` does not multiply any term and `k` does not
multiply DLOG. -/
theorem extractionFailureEvent_measure_le {k maxActions : ℕ}
    (family : Family k maxActions)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (hquery : Function.Injective query)
    (escape : Fin k → Set family.GroupSample)
    {dlBound epsilonStat epsilonEscape : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B
          (family.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype family.ScalarSample).toOuterMeasure
        (family.scalarEvent B (escape slot)) ≤ epsilonEscape) :
    (runsLaw family query).toOuterMeasure
        (extractionFailureEvent family query escape) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (k : ENNReal) * (epsilonStat + epsilonEscape) := by
  unfold runsLaw extractionFailureEvent orchardEvent
  rw [uniformURS_basis_transfer
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (family.ledgerExtractionFailureEvent escape)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.shape.k B hB query hquery)]
  exact family.ledgerExtractionFailureEvent_prob_le B escape hDL hstat hescape

end Family

/-! ## Full proof-emitting ledger experiment -/

/-- Transaction data supplied by the ledger machine for one emitted slot.  The
Action count is deliberately absent: it is selected by the shared Action
execution.  `sigs` provides a signature for every possible position; only the
prefix selected by that execution is consumed. -/
structure TxRequest (MSG : Type) (maxActions : ℕ) where
  sigs : Fin maxActions → RedDSA.Sig Fq PallasGroup
  vBalance : ℤ
  sighash : MSG
  bindingSig : RedDSA.Sig Fq PallasGroup

/-- A proof-emitting balance adversary whose Action proofs form one shared,
stateful adaptive-count execution.  The ledger machine sees that run and may
choose its transaction data from it, but it cannot resample a transcript for a
different slot or count. -/
structure ExtractionBalanceAdversary (MSG : Type) [Fintype MSG] [DecidableEq MSG]
    [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    {T : Type} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (k maxActions : ℕ) : Type 1 where
  ι : Type
  coins : PMF ι
  actionFamily : AdaptiveActionReduction.Family k maxActions
  B : ι → (table : ↥(Set.range query) → VestaG) → actionFamily.Coins →
    (Fin 2 → PallasGroup) →
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (TxRequest MSG maxActions × QueryRep Fq 2))
  qH : ℕ

namespace ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T]
  {query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- The witness-annotated transaction type consumed by the existing
KS-idealized ledger experiment. -/
abbrev AnnotatedTx :=
  Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Pool.Encoding
    MSG (RedDSA.Sig Fq PallasGroup)
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth

/-- One generator table paired with the shared Action random-oracle table. -/
abbrev Runs := Family.Runs A.actionFamily query

/-- Assemble one annotated transaction from the ledger request and the witness
extracted at this slot's adaptively selected Action count. -/
def assembleTx (r : Runs A) (slot : Fin k) (req : TxRequest MSG maxActions) :
    Option (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind) :=
  let family := A.actionFamily.slotFamily slot
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

/-- Annotate successive requests by extraction, stopping at the first failure
or after the `k` emitted slots covered by the reduction. -/
def assembleChain (r : Runs A) :
    ℕ → List (TxRequest MSG maxActions × QueryRep Fq 2) →
      List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind × QueryRep Fq 2)
  | _, [] => []
  | t, (req, rep) :: rest =>
      if ht : t < k then
        match assembleTx H_bind A r ⟨t, ht⟩ req with
        | none => []
        | some tx => (tx, rep) :: assembleChain r (t + 1) rest
      else []

/-- The annotated ledger adversary obtained by running the proof-emitting
machine and replacing its accepted Action proofs with extracted witnesses. -/
def toLA (x : A.ι × Runs A) (basis : Fin 2 → PallasGroup) :
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind × QueryRep Fq 2)) :=
  (A.B x.1 x.2.1 x.2.2 basis).bind fun out =>
    .pure (assembleChain H_bind A x.2 0 out)

/-- Concrete law of the generator table and the one shared Action table. -/
noncomputable def runsLaw : PMF (Runs A) :=
  Family.runsLaw A.actionFamily query

/-- The proof-emitting adversary transported to the existing witness-annotated
ledger game.  Its annotations are computed from its sampled run, not supplied
as adversarial inputs. -/
noncomputable def toIdealizedKS
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j)) :
    IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind where
  ι := A.ι × Runs A
  coins := independentProductPMF A.coins (runsLaw A)
  LA := toLA H_bind A
  qH := A.qH
  queryBound := hqb
  algebraic := halg

/-- Exact failure of the selected proof at one emitted slot: verification
accepts, but the adaptive-count ledger extractor returns no annotation. -/
def slotExtractionFailure (slot : Fin k) : Set A.actionFamily.GroupSample :=
  {p | (A.actionFamily.slotFamily slot).selectedAccepts p.1 p.2 ∧
    selectedLedgerExtractor (A.actionFamily.slotFamily slot) spendAuthVerify
      (redPallasBindingVerify H_bind) p.1 p.2 = none}

/-- The computed Sinsemilla bridge escape for one accepted selected proof. -/
def slotEscape (slot : Fin k) : Set A.actionFamily.GroupSample :=
  {p | (A.actionFamily.slotFamily slot).selectedAccepts p.1 p.2 ∧
    (selectedLedgerEscapeFinder (A.actionFamily.slotFamily slot) spendAuthVerify
      (redPallasBindingVerify H_bind) p.1 p.2).isSome}

/-- Exact ledger extraction failure at a slot is either selected-count Action
knowledge failure or that slot's computed ledger bridge escape. -/
theorem slotExtractionFailure_subset (slot : Fin k) :
    slotExtractionFailure H_bind A slot ⊆
      (A.actionFamily.slotFamily slot).selectedKnowledgeFailureEvent ∪
        slotEscape H_bind A slot := by
  rintro p ⟨haccepts, hnone⟩
  rcases (selectedLedgerExtractor_eq_none_iff
      (A.actionFamily.slotFamily slot) spendAuthVerify
      (redPallasBindingVerify H_bind) p.1 p.2).mp hnone with hknowledge | hescape
  · exact Or.inl ⟨haccepts, hknowledge⟩
  · exact Or.inr ⟨haccepts, hescape⟩

/-- Exact extraction failure among the `k` emitted slots, pulled back through
the concrete Orchard generator-table sample. -/
def runExtractionFailureEvent : Set (Runs A) :=
  Family.orchardEvent A.actionFamily query
    (A.actionFamily.ledgerFailureEvent (slotExtractionFailure H_bind A))

/-- The exact run-level failure event is contained in the adaptive reduction's
knowledge-or-escape event. -/
theorem runExtractionFailureEvent_subset :
    runExtractionFailureEvent H_bind A ⊆
      Family.extractionFailureEvent A.actionFamily query (slotEscape H_bind A) := by
  unfold runExtractionFailureEvent Family.extractionFailureEvent Family.orchardEvent
  apply Set.preimage_mono
  intro p hp
  obtain ⟨slot, hslot⟩ := Set.mem_iUnion.mp hp
  exact Set.mem_iUnion.mpr ⟨slot, slotExtractionFailure_subset H_bind A slot hslot⟩

/-- Exact extraction failure in the full challenge experiment. -/
def extractionFailureEvent :
    Set ((A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq))) :=
  (fun x => x.1.2) ⁻¹' runExtractionFailureEvent H_bind A

/-- Events depending only on the generator and Action tables have their
`runsLaw` measure inside the larger ledger challenge experiment. -/
theorem experiment_measure_runs
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j))
    (E : Set (Runs A)) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) ×
          ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) => x.1.2) ⁻¹' E) =
      (runsLaw A).toOuterMeasure E := by
  have hfst : (toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst =
      independentProductPMF A.coins (runsLaw A) :=
    challengeExperiment_map_fst 2 _
  have hsnd : (independentProductPMF A.coins (runsLaw A)).map Prod.snd = runsLaw A :=
    independentProductPMF_map_snd _ _
  have hmap : (toIdealizedKS H_bind A hqb halg).experiment.map
      (fun x : (A.ι × Runs A) ×
        ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) => x.1.2) = runsLaw A := by
    have hcomp : ((toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst).map
        Prod.snd = (toIdealizedKS H_bind A hqb halg).experiment.map
          (Prod.snd ∘ Prod.fst) :=
      PMF.map_comp _ _ _
    calc
      (toIdealizedKS H_bind A hqb halg).experiment.map
          (fun x : (A.ι × Runs A) ×
            ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) => x.1.2)
        = (toIdealizedKS H_bind A hqb halg).experiment.map
            (Prod.snd ∘ Prod.fst) := rfl
      _ = ((toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst).map
            Prod.snd := hcomp.symm
      _ = runsLaw A := by rw [hfst, hsnd]
  calc
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) ×
          ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) => x.1.2) ⁻¹' E)
      = ((toIdealizedKS H_bind A hqb halg).experiment.map
          (fun x : (A.ι × Runs A) ×
            ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) => x.1.2)).toOuterMeasure E :=
        (PMF.toOuterMeasure_map_apply _ _ _).symm
    _ = (runsLaw A).toOuterMeasure E := by rw [hmap]

/-- **Extraction failure for the full proof-emitting ledger experiment.**
The Action DLOG term is charged once.  The `k` factor multiplies only the
selected-count statistical surface and the computed bridge escape; there is no
`maxActions` multiplier. -/
theorem extractionFailureEvent_measure_le
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0)
    (hquery : Function.Injective query)
    {dlBound epsilonStat epsilonEscape : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      A.actionFamily.combinedRelationFinder dlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (slotEscape H_bind A slot)) ≤ epsilonEscape) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (k : ENNReal) * (epsilonStat + epsilonEscape) := by
  unfold extractionFailureEvent
  have hruns := experiment_measure_runs H_bind A hqb halg
    (runExtractionFailureEvent H_bind A)
  calc
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x => x.1.2) ⁻¹' runExtractionFailureEvent H_bind A)
      = (runsLaw A).toOuterMeasure (runExtractionFailureEvent H_bind A) := hruns
    _ ≤ (runsLaw A).toOuterMeasure
          (Family.extractionFailureEvent A.actionFamily query (slotEscape H_bind A)) :=
        MeasureTheory.measure_mono (runExtractionFailureEvent_subset H_bind A)
    _ ≤ (dlBound + 1 / Fintype.card Fp) +
          (k : ENNReal) * (epsilonStat + epsilonEscape) :=
        Family.extractionFailureEvent_measure_le A.actionFamily B hB query hquery
          (slotEscape H_bind A) hDL hstat hescape

end ExtractionBalanceAdversary

section Endpoints

open ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T]
  {query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- **Balance integrity for the full proof-emitting Orchard ledger
experiment.**  The Action DLOG reduction is paid once; only the selected-count
statistical and ledger-bridge terms retain the `k`-slot union bound.  The second
summand is the existing KS-idealized balance-integrity bound. -/
theorem orchardBalanceIntegrityExtraction_measure_le
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0)
    (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {actionDlBound epsilonStat epsilonEscape epsilonSinsemillaDLR ledgerDlBound : ENNReal}
    (hActionDL : TextbookDLWithCoinsAdvantageLE B
      A.actionFamily.combinedRelationFinder actionDlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (slotEscape H_bind A slot)) ≤ epsilonEscape)
    (hsin : (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
      ((toIdealizedKS H_bind A hqb halg).sinsemillaRelationEvent issuance maxActions k) ≤
        epsilonSinsemillaDLR)
    (hLedgerDL : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ledgerDlBound) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      ((actionDlBound + 1 / Fintype.card Fp) +
          (k : ENNReal) * (epsilonStat + epsilonEscape)) +
        (epsilonSinsemillaDLR +
          (ledgerDlBound + ((A.qH + 2 : ℕ) : ENNReal) / Fintype.card Fq)) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg B hB hquery
      hActionDL hstat hescape)
    (orchardBalanceIntegrity_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hsin hLedgerDL)

/-- **Balance conservation for the full proof-emitting Orchard ledger
experiment.**  This has the same adaptive Action extraction term as the
integrity endpoint and the existing conservation bound as its second summand. -/
theorem orchardBalanceConservationExtraction_measure_le
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0)
    (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {actionDlBound epsilonStat epsilonEscape ledgerDlBound : ENNReal}
    (hActionDL : TextbookDLWithCoinsAdvantageLE B
      A.actionFamily.combinedRelationFinder actionDlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (slotEscape H_bind A slot)) ≤ epsilonEscape)
    (hLedgerDL : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ledgerDlBound) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      ((actionDlBound + 1 / Fintype.card Fp) +
          (k : ENNReal) * (epsilonStat + epsilonEscape)) +
        (ledgerDlBound + ((A.qH + 2 : ℕ) : ENNReal) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg B hB hquery
      hActionDL hstat hescape)
    (orchardBalanceConservation_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hLedgerDL)

/-- **Shielded balance cap for the full proof-emitting Orchard ledger
experiment.**  As for conservation, with the shielded-pool cap violation as the
ledger event. -/
theorem orchardShieldedBalanceCapExtraction_measure_le
    (hqb : ∀ j basis, (toLA H_bind A j basis).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j))
    (B : VestaG) (hB : B ≠ 0)
    (hquery : Function.Injective query)
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {actionDlBound epsilonStat epsilonEscape ledgerDlBound : ENNReal}
    (hActionDL : TextbookDLWithCoinsAdvantageLE B
      A.actionFamily.combinedRelationFinder actionDlBound)
    (hstat : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B
          (A.actionFamily.slotFamily slot).selectedStatisticalFailureEvent) ≤ epsilonStat)
    (hescape : ∀ slot,
      (PMF.uniformOfFintype A.actionFamily.ScalarSample).toOuterMeasure
        (A.actionFamily.scalarEvent B (slotEscape H_bind A slot)) ≤ epsilonEscape)
    (hLedgerDL : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ledgerDlBound) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      ((actionDlBound + 1 / Fintype.card Fp) +
          (k : ENNReal) * (epsilonStat + epsilonEscape)) +
        (ledgerDlBound + ((A.qH + 2 : ℕ) : ENNReal) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg B hB hquery
      hActionDL hstat hescape)
    (orchardShieldedBalanceCap_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hLedgerDL)

end Endpoints
end Zcash.Security.Ledger.OrchardExtractionExperiment
