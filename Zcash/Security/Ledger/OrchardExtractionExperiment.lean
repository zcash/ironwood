import Zcash.Security.Ledger.ActionBundleBridge
import Zcash.Security.Ledger.OrchardIntegrityExperiment
import Zcash.Snark.Capstones.Action

/-!
# The Orchard extraction experiment

Compose the ledger games with the Action circuit's knowledge extractor.

The `_idealizedks` experiments quantify over witness-annotated adversaries: every
action of the output chain carries the witness for the Action statement. This module
builds that annotated adversary from a proof-emitting one. The composed adversary
presents, per chain position and bundle size, the Fiat–Shamir family that produces its
proofs; the sample space adds the generator table and one transcript per bundle size;
and the annotations are computed by the composed ledger extractor
(`actionLedgerOutcome`) from the sampled runs.

Two facts shape the composition. First, consensus validity is public: structural
validity, type checks on public data, and verification of the proofs and signatures.
Nothing in it speaks about openings of commitments or extracted witnesses. Second,
the annotations cannot be a function of the public chain: the commitments are
perfectly hiding, so which opening a chain "contains" is well-defined only relative
to a prover execution. The constructed adversary's annotations are therefore a
function of its coins —which include the sampled runs— and that is the only shape a
sound composition can take.

The bundle size is selected adaptively, and the oracle tables are shared per bundle
size. The deployed verifier absorbs the verifying key digest, every instance
commitment, and every advice commitment before squeezing its first challenge, so the
pre-challenge transcript determines the bundle size and distinct sizes never share a
squeeze input. Sampling one independent transcript per size is therefore a sound
finite presentation of one random oracle — and every chain position's proof at a
given size reads that size's one shared table, as a real adversary's proofs against
one oracle would. The ledger machine may select each position's size after seeing the
runs. The cost is that the knowledge-soundness terms of the composed bound sum over
the slot-size pairs — a factor `k * maxActions` — counting the extraction targets
this model hands the adversary. Removing the factor is tracked as #214.

The composed endpoints run at the deployed value bases (`deployedViolationEvent` over
`deployedExperiment`): the extracted witnesses open the value commitments at the
deployed bases, and validity is stated at exactly those bases, so the violation arm
is inhabited by the chains the extractor actually produces. Only the binding
challenge hash is idealized as the table, and the conservation side's relation arm is
the named `ε_valuedlr` of the exhibited deployed finder.
-/

open scoped ENNReal

namespace Zcash.Security.Ledger.OrchardExtractionExperiment

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.ActionBundleBridge
open Zcash.Security.Ledger.Bridge
open Zcash.Security.Ledger.Model
open Zcash.Security.Ledger.Pool
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Capstone (adaptiveStatement_pairCount_lt
  orchard_action_adaptiveStatement_knowledge_error_bound)
open Zcash.Snark.Keygen (actionProofParamsFor)

/-- The transaction-level data the ledger machine supplies for one chain position: the
action count and the declared transaction fields. The action instances and witnesses
are not requested — they come from the selected slot's extracted ledger data. -/
structure TxRequest (MSG : Type) (maxActions : ℕ) where
  /-- The number of actions the transaction carries. -/
  numActions : ℕ
  /-- A transaction carries at least one action. -/
  numActions_nonzero : numActions ≠ 0
  /-- The action count is within the model's cap. -/
  numActions_le : numActions ≤ maxActions
  /-- The spend-authorization signature of each action. -/
  sigs : Fin numActions → RedDSA.Sig Fq PallasGroup
  /-- The declared net value leaving the pool. -/
  vBalance : ℤ
  /-- The sighash the transaction's signatures are over. -/
  sighash : MSG
  /-- The binding signature. -/
  bindingSig : RedDSA.Sig Fq PallasGroup

/-- The family slot a request selects: the families producing `numActions` actions sit
at slot `numActions - 1`. -/
def TxRequest.slot {MSG : Type} {maxActions : ℕ} (req : TxRequest MSG maxActions) :
    Fin maxActions :=
  ⟨req.numActions - 1, by
    have h1 := req.numActions_nonzero
    have h2 := req.numActions_le
    omega⟩

/-- The selected slot's proof-parameter size is the request's action count. -/
theorem TxRequest.slot_val_add_one {MSG : Type} {maxActions : ℕ}
    (req : TxRequest MSG maxActions) : req.slot.1 + 1 = req.numActions := by
  have h := req.numActions_nonzero
  simp only [TxRequest.slot]
  omega

/-- **The proof-emitting balance adversary model, as a type.** Per chain position
`t < k` and bundle size, a Fiat–Shamir family produces the proofs; the ledger machine
(`machine`) sees the whole sampled runs component and the presented bases, and requests
one transaction per position. The witness annotations are not part of this model — the
composition computes them by extraction. -/
structure ExtractionBalanceAdversary (MSG : Type) [Fintype MSG] [DecidableEq MSG]
    [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    {T : Type} [DecidableEq T] (query : AugmentedIndex actionCircuit.n → T)
    (k maxActions : ℕ) : Type 1 where
  /-- The adversary's coin space. -/
  ι : Type
  /-- The coin distribution. -/
  coins : PMF ι
  /-- Per slot and bundle size, the family producing that proof. -/
  families : Fin k → (n : Fin maxActions) →
    ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor (n.1 + 1))
  /-- The ledger machine: from the coins, the sampled runs, and the presented bases,
  request one transaction per chain position, with its announced binding
  representation. -/
  machine : ι → (table : ↥(Set.range query) → VestaG) →
    (Os : ∀ n : Fin maxActions,
      AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp) →
    (Fin 2 → PallasGroup) →
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (TxRequest MSG maxActions × QueryRep Fq 2))
  /-- The challenge-oracle query budget. -/
  qH : ℕ
  /-- The ledger machine respects the budget at every input. -/
  queryBound : ∀ j table Os b, (machine j table Os b).QueryBound qH

namespace ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : AugmentedIndex actionCircuit.n → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- The deployed annotated transaction type the assembled chain carries. -/
abbrev AnnotatedTx :=
  Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Pool.Encoding
    MSG (RedDSA.Sig Fq PallasGroup)
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth

/-- The runs component of the composed sample: the generator table, and one shared
Fiat–Shamir transcript per bundle size. The adversary argument is unused in the body —
the tables are shared per size, not owned by any family — and is kept so that use
sites determine the index parameters, as the model layer's `Coins` does with its
family argument. -/
abbrev Runs (_A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions) :=
  (↥(Set.range query) → VestaG) ×
    ∀ n : Fin maxActions,
      AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp

/-- Assemble one transaction at one chain position: extract the selected slot's ledger
data from the selected size's shared run and zip it with the requested signatures.
Returns nothing exactly when the composed extractor does. -/
def assembleTx (r : Runs A) (t : Fin k) (req : TxRequest MSG maxActions) :
    Option (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind) :=
  match actionLedgerExtractor (A.families t req.slot)
      (adaptiveStatement_pairCount_lt (req.slot.1 + 1) (A.families t req.slot))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query r.1) (r.2 req.slot) with
  | none => none
  | some members =>
      some { actions := (List.finRange (req.slot.1 + 1)).map fun i =>
               { inst := (members i).success.inst
                 w := (members i).success.w
                 sig := req.sigs (Fin.cast req.slot_val_add_one i) }
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
  | t, (req, rep) :: rest =>
      if ht : t < k then
        match assembleTx H_bind A r ⟨t, ht⟩ req with
        | none => []
        | some tx => (tx, rep) :: assembleChain r (t + 1) rest
      else []

/-- The constructed annotated adversary's machine: run the ledger machine on the
sampled runs and annotate its output by extraction. -/
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

/-- The law of the runs component: a uniform generator table, and one independent
uniform transcript per bundle size. -/
noncomputable def runsLaw : PMF (Runs A) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype (∀ n : Fin maxActions,
      AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp))

/-- **The composed adversary as an idealized annotated adversary.**  Its coins are the
ledger machine's coins together with the sampled runs, and the annotations are computed
by the composed extractor — a function of those coins, as the module doc explains they
must be. The query-bound and algebraicity obligations are supplied for the assembled
machine. -/
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

/-- The extraction-failure event of one slot and size, over the generator table and
that size's shared run: the run accepts, and the composed extractor returns nothing. -/
def runExtractionFailure (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × ((A.families t n).Coins)) :=
  {p | (A.families t n).accepts (orchardGeneratorROBasis query p.1) p.2 ∧
    actionLedgerExtractor (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2 = none}

/-- Collapse the runs sample to one bundle size: the table, and that size's shared
transcript. -/
def runsAt (n : Fin maxActions) :
    Runs A → (↥(Set.range query) → VestaG) ×
      (AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp) :=
  Prod.map id (fun Os => Os n)

/-- The law of a collapsed runs sample is the knowledge endpoints' own law: the
generator table with that one size's uniform transcript. -/
theorem runsLaw_map_runsAt (n : Fin maxActions) :
    (runsLaw A).map (runsAt A n) =
      independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp)) := by
  rw [runsAt, runsLaw, independentProductPMF_map_prodMap, PMF.map_id,
    uniformOfFintype_pi_map_eval]
  rfl

/-- The law of one size's run: the generator table with that size's uniform
transcript. This is the knowledge endpoints' own sample law, so per-run hypotheses
stated over it are the endpoints' conclusions verbatim. -/
noncomputable def runLawAt (n : Fin maxActions) :
    PMF ((↥(Set.range query) → VestaG) ×
      (AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp)) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype
      (AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp))

/-- One run's knowledge-failure event, pulled back to the generator table: the run
accepts and the witness projection returns nothing. -/
def runKnowledgeFailure (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × ((A.families t n).Coins)) :=
  (fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
    (A.families t n).adaptiveStatementKnowledgeFailureEvent
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))

/-- The event that one run accepts and a member of its extracted bundle escapes the
bridge, over the generator table and that size's shared run. -/
def runEscape (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × ((A.families t n).Coins)) :=
  {p | (A.families t n).accepts (orchardGeneratorROBasis query p.1) p.2 ∧
    (actionLedgerEscapeFinder (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2).isSome}

/-- One run's extraction failure decomposes into that run's knowledge-failure event
and its computed ledger escape (`actionLedgerExtractor_eq_none_iff`). -/
theorem runExtractionFailure_subset (t : Fin k) (n : Fin maxActions) :
    runExtractionFailure H_bind A t n ⊆
      runKnowledgeFailure A t n ∪ runEscape H_bind A t n := by
  rintro p ⟨hacc, hnone⟩
  rcases (actionLedgerExtractor_eq_none_iff (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2).mp hnone with h | h
  · exact Or.inl ⟨hacc, h⟩
  · exact Or.inr ⟨hacc, h⟩

/-- An event that reads only the generator table and one size's shared run has the
same measure under the composed deployed experiment as under that run's own law. -/
theorem deployedExperiment_measure_runsAt
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (n : Fin maxActions)
    (E : Set ((↥(Set.range query) → VestaG) ×
      (AdaptiveActionStatementTranscript (actionProofParamsFor (n.1 + 1)) → Fp))) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) =>
          runsAt A n x.1.2) ⁻¹' E) =
      (runLawAt n).toOuterMeasure E := by
  have hfst : (toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst =
      independentProductPMF A.coins (runsLaw A) :=
    challengeTableExperiment_map_fst _
  have hsnd : (independentProductPMF A.coins (runsLaw A)).map Prod.snd = runsLaw A :=
    independentProductPMF_map_snd _ _
  have hmap : (toIdealizedKS H_bind A halg).deployedExperiment.map
      (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) =>
        runsAt A n x.1.2) = runLawAt n := by
    have h1a : ((toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst).map
        Prod.snd =
        (toIdealizedKS H_bind A halg).deployedExperiment.map
          (Prod.snd ∘ Prod.fst) :=
      PMF.map_comp _ _ _
    have h1b : ((toIdealizedKS H_bind A halg).deployedExperiment.map
          (Prod.snd ∘ Prod.fst)).map (runsAt A n) =
        (toIdealizedKS H_bind A halg).deployedExperiment.map
          ((runsAt A n) ∘ (Prod.snd ∘ Prod.fst)) :=
      PMF.map_comp _ _ _
    have h1 : (toIdealizedKS H_bind A halg).deployedExperiment.map
        (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) =>
          runsAt A n x.1.2) =
        (((toIdealizedKS H_bind A halg).deployedExperiment.map Prod.fst).map
          Prod.snd).map (runsAt A n) := by
      rw [h1a, h1b]
      rfl
    rw [h1, hfst, hsnd, runsLaw_map_runsAt]
    rfl
  calc (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) =>
          runsAt A n x.1.2) ⁻¹' E)
      = ((toIdealizedKS H_bind A halg).deployedExperiment.map
          (fun x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) =>
            runsAt A n x.1.2)).toOuterMeasure E :=
        (PMF.toOuterMeasure_map_apply _ _ _).symm
    _ = (runLawAt n).toOuterMeasure E := by rw [hmap]

/-- The extraction-failure arm of the composed experiment: some run among the sampled
slot-size pairs accepts and its composed extractor returns nothing. -/
def extractionFailureEvent :
    Set ((A.ι × Runs A) × (OrchardQuery MSG → Fq)) :=
  ⋃ q : Fin k × Fin maxActions,
    (fun x => runsAt A q.2 x.1.2) ⁻¹' runExtractionFailure H_bind A q.1 q.2

/-- The extraction-failure arm costs one knowledge-soundness bound and one escape
bound per slot-size pair: the factor `k * maxActions` counts the extraction targets
this model hands the adversary. Removing the factor —composing with the SNARK
argument at the reduction layer instead of consuming its endpoint— is tracked as
#214. -/
theorem extractionFailureEvent_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    {ε_ks ε_escape : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) := by
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  have hslot : ∀ q : Fin k × Fin maxActions,
      (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x => runsAt A q.2 x.1.2) ⁻¹'
          runExtractionFailure H_bind A q.1 q.2) ≤ ε_ks + ε_escape := by
    intro q
    refine le_trans
      (le_of_eq (deployedExperiment_measure_runsAt H_bind A halg q.2 _)) ?_
    refine le_trans (MeasureTheory.measure_mono
      (runExtractionFailure_subset H_bind A q.1 q.2)) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    exact add_le_add (hks q.1 q.2) (hescape q.1 q.2)
  refine le_trans (ENNReal.tsum_le_tsum hslot) (le_of_eq ?_)
  calc ∑' _q : Fin k × Fin maxActions, (ε_ks + ε_escape)
      = (Fintype.card (Fin k × Fin maxActions) : ℝ≥0∞) * (ε_ks + ε_escape) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((k * maxActions : ℕ) : ℝ≥0∞) * (ε_ks + ε_escape) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end ExtractionBalanceAdversary

section Endpoints

open ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : AugmentedIndex actionCircuit.n → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- **Balance integrity for the proof-emitting adversary, at deployed Orchard.**
Except with probability at most the bound, every run among the sampled slot-size pairs
that the verifier accepts yields extracted ledger data, and the annotated chain
assembled from that data —whenever it validates at the deployed value bases— satisfies
balance integrity at every prefix below `k`.

The event's validity conjunct is consensus validity together with the assembled
annotations. Consensus validity itself is public and says nothing about openings; the
annotations are computed by the composed extractor from the sampled runs (module doc).
The composed statement is at the deployed value bases: the extracted witnesses open
the value commitments at exactly the bases where validity is stated
(`deployedViolationEvent`), so no reference-string heuristic is involved on the value
side.

`hks` is stated so that `orchard_action_adaptiveStatement_knowledge_error_bound`
applies to it verbatim, one application per slot-size pair; `hescape` names each
pair's Sinsemilla-escape bound. The model's query budget `qH` —respected by the
`queryBound` field— is what the bound's `(qH+1)/#F` term counts; `halg` is the
algebraicity restriction at every presented basis. The remaining hypotheses and the
second summand are the deployed KS-idealized integrity endpoint's, applied at the
constructed adversary. -/
theorem orchardBalanceIntegrityExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_sinsemilladlr ε_valuedlr : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hsin : (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
      ((toIdealizedKS H_bind A halg).deployedSinsemillaRelationEvent issuance
        maxActions k)
      ≤ ε_sinsemilladlr)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder k j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_sinsemilladlr + (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq)) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg hks hescape)
    (orchardBalanceIntegrity_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax k hsin hrel)

/-- **Balance conservation for the proof-emitting adversary, at deployed Orchard.**
As the integrity endpoint (`orchardBalanceIntegrityExtraction_measure_le`), covering
the conservation violation alone; the second summand is the deployed KS-idealized
conservation endpoint's bound. -/
theorem orchardBalanceConservationExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_valuedlr : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder k j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg hks hescape)
    (orchardBalanceConservation_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax k hrel)

/-- **Shielded balance cap for the proof-emitting adversary, at deployed Orchard.**
As the conservation endpoint, for the shielded pool exceeding the minted issuance at
some prefix below `k`. -/
theorem orchardShieldedBalanceCapExtraction_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_valuedlr : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hrel : ∀ j, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | ((toIdealizedKS H_bind A halg).valueDLRFinder k j table).isSome}
      ≤ ε_valuedlr) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A halg hks hescape)
    (orchardShieldedBalanceCap_measure_le_idealizedks_deployed
      (toIdealizedKS H_bind A halg) issuance maxActions hmax k hrel)

/-- The knowledge-error bound of one slot-size pair at a DLOG profile: the bound that
`orchard_action_adaptiveStatement_knowledge_error_bound` proves for the pair's
knowledge-failure event under `runLawAt`. The `_of_dlogProfiles` endpoints take one
profile per pair and compare this quantity against the uniform `ε_ks`. -/
noncomputable def knowledgeErrorBound (t : Fin k) (n : Fin maxActions) {B : VestaG}
    (profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
      (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    ℝ≥0∞ :=
  (profile.advantage ((A.families t n).adaptiveStatementDlogRandomOracleQueries)
      (ComputedAdaptiveActionStatementFSFamily.adaptiveStatementDlogGroupWork
        profile.proverGroupWork profile.reductionGroupWork) +
    1 / Fintype.card Fp) +
  ((A.families t n).Q + 1 : ℕ) *
    (1 / Fintype.card Fp +
      actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal)) +
      algebraicRootBudget
        (actionCircuit.shape.withProofParams (actionProofParamsFor (n.1 + 1)))
        actionCircuit.domainExponent +
      ∑ i : Fin 5,
        ((![(n.1 + 1) * 2 ^ 25, (n.1 + 1) * 950835027, (n.1 + 1) * 73554,
            (n.1 + 1) * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp)

/-- The worst slot-size pair's knowledge-error bound at the supplied DLOG profiles. -/
noncomputable def worstKnowledgeError {B : VestaG}
    (profiles : ∀ (t : Fin k) (n : Fin maxActions),
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
        (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    ℝ≥0∞ :=
  ⨆ (t : Fin k) (n : Fin maxActions), knowledgeErrorBound A t n (profiles t n)

/-- **The combined DLR event.** Some slot-size pair's run accepts and its extracted
bundle escapes the bridge, the constructed adversary's valid chain computes a Sinsemilla
relation at some prefix below `k`, or the value-DLR finder returns a relation. On every
sample here the adversary's own data computes a nontrivial relation over the combined
deployed basis (`orchardPoints`). -/
def combinedDLREvent
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) :
    Set ((A.ι × Runs A) × (OrchardQuery MSG → Fq)) :=
  (⋃ q : Fin k × Fin maxActions,
    (fun x => runsAt A q.2 x.1.2) ⁻¹' runEscape H_bind A q.1 q.2) ∪
  ((toIdealizedKS H_bind A halg).deployedSinsemillaRelationEvent issuance maxActions
      k ∪
    {x | ((toIdealizedKS H_bind A halg).valueDLRFinder k x.1 x.2).isSome})

/-- **The combined DLR advantage** — the single relation term of the composed
endpoints: the probability that the composed deployed experiment lands in
`combinedDLREvent`. -/
noncomputable def combinedDLRAdvantage
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) : ℝ≥0∞ :=
  (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
    (combinedDLREvent H_bind A halg issuance)

/-- Each pair's knowledge-soundness hypothesis, proved by the adaptive-statement
capstone at that pair's DLOG profile and compared against the uniform bound. -/
theorem runKnowledgeFailure_measure_le_of_dlogProfile (hquery : Function.Injective query)
    {B : VestaG} (hB : B ≠ 0) (t : Fin k) (n : Fin maxActions)
    (profile : ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
      (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B)
    {ε_ks : ℝ≥0∞} (hadv : knowledgeErrorBound A t n profile ≤ ε_ks) :
    (runLawAt n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks :=
  le_trans
    (orchard_action_adaptiveStatement_knowledge_error_bound (n.1 + 1) B hB query hquery
      (A.families t n) profile)
    hadv

/-- The knowledge arm of the extraction-failure event, bounded on its own: one capstone
application per slot-size pair, each against the worst pair's knowledge-error bound. -/
theorem knowledgeFailureUnion_measure_le
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (hquery : Function.Injective query) {B : VestaG} (hB : B ≠ 0)
    (profiles : ∀ (t : Fin k) (n : Fin maxActions),
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
        (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (⋃ q : Fin k × Fin maxActions,
          (fun x => runsAt A q.2 x.1.2) ⁻¹' runKnowledgeFailure A q.1 q.2) ≤
      (k * maxActions : ℕ) * worstKnowledgeError A profiles := by
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  have hslot : ∀ q : Fin k × Fin maxActions,
      (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        ((fun x => runsAt A q.2 x.1.2) ⁻¹' runKnowledgeFailure A q.1 q.2) ≤
      worstKnowledgeError A profiles := by
    intro q
    refine le_trans
      (le_of_eq (deployedExperiment_measure_runsAt H_bind A halg q.2 _)) ?_
    exact runKnowledgeFailure_measure_le_of_dlogProfile A hquery hB q.1 q.2
      (profiles q.1 q.2)
      (le_iSup₂ (f := fun t n => knowledgeErrorBound A t n (profiles t n)) q.1 q.2)
  refine le_trans (ENNReal.tsum_le_tsum hslot) (le_of_eq ?_)
  calc ∑' _q : Fin k × Fin maxActions, worstKnowledgeError A profiles
      = (Fintype.card (Fin k × Fin maxActions) : ℝ≥0∞) *
          worstKnowledgeError A profiles := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((k * maxActions : ℕ) : ℝ≥0∞) * worstKnowledgeError A profiles := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **Balance integrity for the proof-emitting adversary, at the combined deployed
basis.** As `orchardBalanceIntegrityExtraction_measure_le`, with each slot-size pair's
knowledge hypothesis discharged by the adaptive-statement capstone at a supplied DLOG
profile, and the relation arms carried by the one combined term
(`combinedDLRAdvantage`). The `k * maxActions` factor multiplies only the knowledge
arm — the escape union is one event inside the combined term — and the only counting
term outside is the challenge-oracle squeeze `(qH+1)/#F`. -/
theorem orchardBalanceIntegrityExtraction_measure_le_of_dlogProfiles
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    (hquery : Function.Injective query) {B : VestaG} (hB : B ≠ 0)
    (profiles : ∀ (t : Fin k) (n : Fin maxActions),
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
        (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * worstKnowledgeError A profiles +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k) ⊆
      (⋃ q : Fin k × Fin maxActions,
        (fun x => runsAt A q.2 x.1.2) ⁻¹' runKnowledgeFailure A q.1 q.2) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id k
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      rcases runExtractionFailure_subset H_bind A q.1 q.2 hq with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)
      · exact Or.inr (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)))
    · rcases balanceIntegrityAt_subset 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          orchardValueBases (toIdealizedKS H_bind A halg).LA k hx with harm | hcons
      · exact Or.inr (Or.inl (Or.inr (Or.inl
          (balanceSubsetArmsAt_subset_orchardRelation spendAuthVerify
            (redPallasBindingVerify H_bind) issuance maxActions 2 0 1 orchardQueryOf id
            (toIdealizedKS H_bind A halg).LA orchardValueBases k harm))))
      · rcases conservationViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
            (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
            (by decide)
            (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
            (orchard_ledger_no_overflow hmax) k x.1 hcons with hfib | hbad
        · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
              k x.1 table).isSome} :=
            (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
              k x.1 ▸ hfib
          exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
        · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add
    (knowledgeFailureUnion_measure_le H_bind A halg hquery hB profiles) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) k

/-- **Balance conservation for the proof-emitting adversary, at the combined deployed
basis.** As the integrity form
(`orchardBalanceIntegrityExtraction_measure_le_of_dlogProfiles`), for the conservation
violation alone. -/
theorem orchardBalanceConservationExtraction_measure_le_of_dlogProfiles
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    (hquery : Function.Injective query) {B : VestaG} (hB : B ≠ 0)
    (profiles : ∀ (t : Fin k) (n : Fin maxActions),
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
        (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * worstKnowledgeError A profiles +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k) ⊆
      (⋃ q : Fin k × Fin maxActions,
        (fun x => runsAt A q.2 x.1.2) ⁻¹' runKnowledgeFailure A q.1 q.2) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id k
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      rcases runExtractionFailure_subset H_bind A q.1 q.2 hq with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)
      · exact Or.inr (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)))
    · rcases conservationViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          (by decide)
          (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
          (orchard_ledger_no_overflow hmax) k x.1 hx with hfib | hbad
      · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
            k x.1 table).isSome} :=
          (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
            k x.1 ▸ hfib
        exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
      · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add
    (knowledgeFailureUnion_measure_le H_bind A halg hquery hB profiles) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) k

/-- **Shielded balance cap for the proof-emitting adversary, at the combined deployed
basis.** As the conservation form, for the shielded pool exceeding the minted issuance
at some prefix below `k`. -/
theorem orchardShieldedBalanceCapExtraction_measure_le_of_dlogProfiles
    (halg : ∀ j, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis
      (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    (hquery : Function.Injective query) {B : VestaG} (hB : B ≠ 0)
    (profiles : ∀ (t : Fin k) (n : Fin maxActions),
      ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementDlogProfile
        (A.families t n) (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n)) B) :
    (toIdealizedKS H_bind A halg).deployedExperiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * worstKnowledgeError A profiles +
        (combinedDLRAdvantage H_bind A halg issuance +
          ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  have hsub : extractionFailureEvent H_bind A ∪
      (toIdealizedKS H_bind A halg).deployedViolationEvent issuance maxActions
        (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k) ⊆
      (⋃ q : Fin k × Fin maxActions,
        (fun x => runsAt A q.2 x.1.2) ⁻¹' runKnowledgeFailure A q.1 q.2) ∪
      (combinedDLREvent H_bind A halg issuance ∪
        {x : (A.ι × Runs A) × (OrchardQuery MSG → Fq) | x.2 ∈ badFiberAt 2 1
          (kappaComposite 2 0 1 orchardQueryOf
            (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id k
            ((toIdealizedKS H_bind A halg).LA x.1)) orchardValueBases}) := by
    rintro x (hx | hx)
    · obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      rcases runExtractionFailure_subset H_bind A q.1 q.2 hq with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)
      · exact Or.inr (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, h⟩)))
    · rcases shieldedBalanceCapViolationAt_subset_dischargeAt 2 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
          (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
          (by decide)
          (fun j => (toIdealizedKS H_bind A halg).algebraic j orchardValueBases)
          (orchard_ledger_no_overflow hmax) k x.1 hx with hfib | hbad
      · have hmem : x.2 ∈ {table | ((toIdealizedKS H_bind A halg).valueDLRFinder
            k x.1 table).isSome} :=
          (toIdealizedKS H_bind A halg).conservationRelFiberAt_orchardValueBases
            k x.1 ▸ hfib
        exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
      · exact Or.inr (Or.inr hbad)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add
    (knowledgeFailureUnion_measure_le H_bind A halg hquery hB profiles) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add (le_refl _) ?_)
  exact challengeTableExperiment_badFiberAt_measure_le 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (toIdealizedKS H_bind A halg).coins
    (fun j => (toIdealizedKS H_bind A halg).queryBound j orchardValueBases) k

end Endpoints

end Zcash.Security.Ledger.OrchardExtractionExperiment
