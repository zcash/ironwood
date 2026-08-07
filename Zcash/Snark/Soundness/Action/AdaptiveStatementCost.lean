import Zcash.Snark.Soundness.AGM.CostedOracle
import Zcash.Snark.Soundness.Action.AdaptiveStatementCached
import Zcash.Snark.Soundness.Action.AdaptiveStatementReads
import Zcash.Snark.Soundness.Composition.AssembleGroupCost

/-!
# Certified adaptive-statement work accounting

This module replaces the two free natural-number work declarations in
`AdaptiveStatementDlogProfile` with executable accounting objects:

* `AdaptiveStatementAdversaryCostCertificate` supplies a staged costed oracle program, proves that
  its erasure is the original online-AGM adversary, and proves a structural path bound;
* `adaptiveStatementFinderReductionProgram` and
  `adaptiveStatementExtractorReductionProgram` execute group-valued postprocessing through
  reified Vesta primitives, using the one-execution cache from `AdaptiveStatementCached`.

The executable programs charge the group-operation work of each stage that actually runs, while
the public bound retains conservative slack for quotient and terminal proof construction.  It
includes programmed-basis evaluation, canonical instance evaluation, verifier assembly, the
identity/terminal path, and the final witness projection.  Equality tests,
annotation/source-list scans, field operations, and direct-coordinate decode work are not DLOG
group operations; the latter remains in its separate model and is derived at the capstone from a
required family source-length invariant. Random-oracle queries are also kept separate: one
adversary run plus the canonical `11 + k` challenge reads. A private composition object carries one
closed program that constructs the basis, specializes the exact adversary path with its annotations
and group nodes, builds a proof-carrying cache, and consumes that cache in postprocessing. Lean
derives the counter decomposition from this syntax. Fidelity remains explicit both for the supplied
adversary and for unreified host computations inside the complete shallow program.
-/

namespace Zcash.Snark

open Keygen

local instance adaptiveStatementCostVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- A basis-indexed staged program whose erasure is the supplied adaptive-statement adversary.
`staged` is the explicit host-language fidelity boundary described by
`CostedLabeledOracleComp.StagedGroupWorkFaithful`; the remaining fields are checked entirely by
Lean. -/
structure AdaptiveStatementAdversaryCostCertificate {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (workLimit : Nat) where
  program :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      CostedLabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
  erase_eq : ∀ basis, (program basis).erase = family.adversary basis
  staged : ∀ basis, (program basis).StagedGroupWorkFaithful
  workBound : ∀ basis, (program basis).GroupWorkBound workLimit

namespace AdaptiveStatementAdversaryCostCertificate

/-- Pointwise adversary group work read from the costed syntax. -/
def proverGroupWork {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  (certificate.program basis).groupWork O

theorem proverGroupWork_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    certificate.proverGroupWork basis O ≤ workLimit :=
  certificate.workBound basis O

/-- Erasure gives exactly the output used by the original adaptive game. -/
theorem run_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.program basis).run O = family.runOutput basis O := by
  unfold CostedLabeledOracleComp.run runOutput
  rw [certificate.erase_eq]

/-- Materialize the one-execution cache from the exact erased costed program, including its
annotation log.  This is the value-level bridge used by the composed reduction; it does not
reinvoke `family.adversary` through a parallel host path. -/
def certifiedCachedRun {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : CachedRun pp family basis :=
  family.cachedRunOfExecution basis O
    ((certificate.program basis).erase.runWithAnnotations O)

/-- The exact adversary path, including its group nodes, closed at one oracle table and mapped to
the cache consumed by postprocessing.  Both the cache and its work trace come from this program. -/
def certifiedCachedRunProgram {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    CostedVestaComp {cache : CachedRun pp family basis //
      cache = certificate.certifiedCachedRun basis O} :=
  CostedVestaComp.map (fun execution =>
      ⟨family.cachedRunOfExecution basis O execution.1,
        congrArg (family.cachedRunOfExecution basis O) execution.2⟩)
    ((certificate.program basis).materializeWithAnnotationsCertified O)

@[simp] theorem certifiedCachedRunProgram_run {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.certifiedCachedRunProgram basis O).run.1 =
      certificate.certifiedCachedRun basis O := by
  exact (certificate.certifiedCachedRunProgram basis O).run.2

@[simp] theorem certifiedCachedRunProgram_run_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.certifiedCachedRunProgram basis O).run =
      ⟨certificate.certifiedCachedRun basis O, rfl⟩ := by
  apply Subtype.ext
  exact certificate.certifiedCachedRunProgram_run basis O

@[simp] theorem certifiedCachedRunProgram_groupWork {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.certifiedCachedRunProgram basis O).groupWork =
      certificate.proverGroupWork basis O := by
  rw [certifiedCachedRunProgram, CostedVestaComp.groupWork_map]
  unfold CostedVestaComp.groupWork proverGroupWork
  rw [CostedLabeledOracleComp.groupWork_materializeWithAnnotationsCertified]

@[simp] theorem certifiedCachedRun_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    certificate.certifiedCachedRun basis O = family.cachedRun basis O := by
  unfold certifiedCachedRun ComputedAdaptiveActionStatementFSFamily.cachedRun
    ComputedAdaptiveActionStatementFSFamily.cachedRunOfExecution
  rw [certificate.erase_eq]

theorem certifiedCachedRun_pairCount_lt {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    let cache := certificate.certifiedCachedRun basis O
    deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder := by
  rw [certificate.certifiedCachedRun_eq]
  exact family.cachedRun_pairCount_lt hchar basis O

theorem certifiedCachedRun_semanticStageFacts {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    let cache := certificate.certifiedCachedRun basis O
    family.provenanceRelationFinderOfCachedRun basis cache = none →
      family.SemanticStageFacts basis cache.toRunView := by
  rw [certificate.certifiedCachedRun_eq]
  exact family.semanticStageFacts_of_cachedProvenance_none basis O

theorem certifiedCachedRun_inputs_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.certifiedCachedRun basis O).output.inputs =
      (family.runOutput basis O).inputs := by
  rw [certificate.certifiedCachedRun_eq]
  exact congrArg AdaptiveActionStatementOutput.inputs
    (family.cachedRun_output_eq basis O)

end AdaptiveStatementAdversaryCostCertificate

/-- Number of fixed augmented-basis entries evaluated by one full-width representation. -/
def adaptiveStatementBasisWidth (pp : ProofParams) : Nat :=
  2 ^ (AdaptiveActionStatementShape pp).k + 2

/-! ## Concrete MSM encodings

These lists are the operands consumed by the reified Vesta MSM primitive.  Their lengths, and not
caller-supplied natural numbers, determine reduction work.
-/

/-- Concrete terms for a generator-only commitment. -/
def vestaCommitGenTerms {n : Nat} (g : Fin n → VestaG) (coeffs : Fin n → Fp) :
    List (Fp × VestaG) :=
  List.ofFn fun i => (coeffs i, g i)

@[simp] theorem vestaCommitGenTerms_length {n : Nat} (g : Fin n → VestaG)
    (coeffs : Fin n → Fp) :
    (vestaCommitGenTerms g coeffs).length = n := by
  simp [vestaCommitGenTerms]

theorem vestaCommitGenTerms_sum {n : Nat} (g : Fin n → VestaG)
    (coeffs : Fin n → Fp) :
    ((vestaCommitGenTerms g coeffs).map fun term => term.1 • term.2).sum =
      commitGen g coeffs := by
  simp [vestaCommitGenTerms, commitGen, List.sum_ofFn]

/-- Concrete terms for an augmented-basis representation. -/
def vestaAugmentedRepresentationTerms {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) : List (Fp × VestaG) :=
  List.ofFn (fun i : Fin (2 ^ k) =>
      (coeffs (AugmentedIndex.gen i), basis (AugmentedIndex.gen i))) ++
    [(coeffs AugmentedIndex.u, basis AugmentedIndex.u),
     (coeffs AugmentedIndex.w, basis AugmentedIndex.w)]

@[simp] theorem vestaAugmentedRepresentationTerms_length {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) :
    (vestaAugmentedRepresentationTerms basis coeffs).length = 2 ^ k + 2 := by
  simp [vestaAugmentedRepresentationTerms]

theorem vestaAugmentedRepresentationTerms_sum {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) :
    ((vestaAugmentedRepresentationTerms basis coeffs).map
      fun term => term.1 • term.2).sum = representationEval basis coeffs := by
  rw [representationEval_augmented_components]
  simp [vestaAugmentedRepresentationTerms, List.sum_ofFn]
  abel

/-- Concrete terms for evaluating the verifier's assembled MSM. -/
def vestaAssembledMsmTerms (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) : List (Fp × VestaG) :=
  List.ofFn (fun i => (msm.gScalars i, urs.g i)) ++
    [(msm.wScalar, urs.w), (msm.uScalar, urs.u)] ++ msm.other

@[simp] theorem vestaAssembledMsmTerms_length (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) :
    (vestaAssembledMsmTerms urs msm).length = 2 ^ urs.k + 2 + msm.other.length := by
  simp [vestaAssembledMsmTerms]
  omega

theorem vestaAssembledMsmTerms_sum (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) :
    ((vestaAssembledMsmTerms urs msm).map fun term => term.1 • term.2).sum =
      msm.eval urs := by
  simp [vestaAssembledMsmTerms, Zcash.Arithmetic.Msm.eval,
    List.sum_ofFn]
  abel

/-- A basis function recovered from reified MSM results, together with the equation identifying
it with the basis expected by the surrounding reduction. -/
structure AdaptiveStatementBasisCache (pp : ProofParams)
    (expected : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) where
  basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG
  basis_eq : basis = expected

/-- Reify every slot of an augmented basis.  The returned function is assembled from the actual
MSM results, so a continuation consuming `cache.basis` is data-dependent on every charged node. -/
def costedAdaptiveStatementBasisCache (pp : ProofParams)
    (expected : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (terms : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) →
      List (Fp × VestaG))
    (heval : ∀ i, (terms i |>.map fun term => term.1 • term.2).sum = expected i) :
    CostedVestaComp (AdaptiveStatementBasisCache pp expected) :=
  CostedVestaComp.bind
    (CostedVestaComp.evalMsmsCertified
      (List.ofFn fun i => terms (AugmentedIndex.gen i))) fun generators =>
  CostedVestaComp.bind
    (CostedVestaComp.vestaMsmCertified (terms AugmentedIndex.u)) fun u =>
  CostedVestaComp.bind
    (CostedVestaComp.vestaMsmCertified (terms AugmentedIndex.w)) fun w =>
  CostedVestaComp.pure
    { basis := fun i =>
        match i with
        | Sum.inl j => generators.1.getD j 0
        | Sum.inr j => if j = 0 then u.1 else w.1
      basis_eq := by
        funext i
        rcases i with i | j
        · rw [generators.2]
          have hi := i.isLt
          change i.val < 2 ^ (Zcash.Circuits.Action.actionCircuit).domainExponent at hi
          simp [List.getD, heval, hi]
          apply congrArg expected
          congr 1
        · fin_cases j <;>
            simp [u.2, w.2, heval, AugmentedIndex.u, AugmentedIndex.w] }

@[simp] theorem costedAdaptiveStatementBasisCache_run
    (pp : ProofParams)
    (expected : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (terms : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) →
      List (Fp × VestaG))
    (heval : ∀ i, (terms i |>.map fun term => term.1 • term.2).sum = expected i) :
    (costedAdaptiveStatementBasisCache pp expected terms heval).run =
      { basis := expected, basis_eq := rfl } := by
  generalize (costedAdaptiveStatementBasisCache pp expected terms heval).run = result
  rcases result with ⟨actual, hactual⟩
  subst actual
  rfl

@[simp] theorem costedAdaptiveStatementBasisCache_groupWork
    (pp : ProofParams)
    (expected : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (terms : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) →
      List (Fp × VestaG))
    (heval : ∀ i, (terms i |>.map fun term => term.1 • term.2).sum = expected i)
    (hlength : ∀ i, (terms i).length = 2) :
    (costedAdaptiveStatementBasisCache pp expected terms heval).groupWork =
      2 * adaptiveStatementBasisWidth pp := by
  simp [costedAdaptiveStatementBasisCache, hlength, adaptiveStatementBasisWidth,
    List.sum_ofFn, Nat.mul_add, Nat.mul_comm]

/-- Proof-carrying programmed-basis construction used by the DLOG reduction. -/
def costedAdaptiveStatementProgrammedBasisCache (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    CostedVestaComp (AdaptiveStatementBasisCache pp (fun i => x i • B + y i • C)) :=
  costedAdaptiveStatementBasisCache pp (fun i => x i • B + y i • C)
    (fun i => [(x i, B), (y i, C)]) (by intro i; simp)

@[simp] theorem costedAdaptiveStatementProgrammedBasisCache_run
    (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    (costedAdaptiveStatementProgrammedBasisCache pp B C x y).run =
      { basis := fun i => x i • B + y i • C, basis_eq := rfl } := by
  apply costedAdaptiveStatementBasisCache_run

@[simp] theorem costedAdaptiveStatementProgrammedBasisCache_groupWork
    (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    (costedAdaptiveStatementProgrammedBasisCache pp B C x y).groupWork =
      2 * adaptiveStatementBasisWidth pp := by
  apply costedAdaptiveStatementBasisCache_groupWork
  intro i
  rfl

/-- Canonical two-term materialization of an already-selected basis.  This gives the generic
basis-indexed execution the same data-coupled interface as the programmed DLOG execution. -/
def costedAdaptiveStatementSelectedBasisCache (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    CostedVestaComp (AdaptiveStatementBasisCache pp basis) :=
  costedAdaptiveStatementBasisCache pp basis
    (fun i => [(1, basis i), (0, basis i)]) (by intro i; simp)

@[simp] theorem costedAdaptiveStatementSelectedBasisCache_run
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (costedAdaptiveStatementSelectedBasisCache pp basis).run =
      { basis := basis, basis_eq := rfl } := by
  apply costedAdaptiveStatementBasisCache_run

@[simp] theorem costedAdaptiveStatementSelectedBasisCache_groupWork
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (costedAdaptiveStatementSelectedBasisCache pp basis).groupWork =
      2 * adaptiveStatementBasisWidth pp := by
  apply costedAdaptiveStatementBasisCache_groupWork
  intro i
  rfl

/-- The canonical instance MSM operands before flattening.  Retaining this matrix shape lets the
costed reduction turn the reified results back into the exact proof/column commitment function
consumed by verifier assembly. -/
def adaptiveStatementCanonicalInstanceTermMatrix {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    List (List (List (Fp × VestaG))) :=
  List.ofFn fun p => List.ofFn fun column =>
    vestaAugmentedRepresentationTerms basis
      (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).coeffs

theorem adaptiveStatementCanonicalInstanceTermMatrix_eval {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (adaptiveStatementCanonicalInstanceTermMatrix family basis output).map (fun row =>
      row.map fun terms => (terms.map fun term => term.1 • term.2).sum) =
      List.ofFn fun p => List.ofFn fun column =>
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).point := by
  unfold adaptiveStatementCanonicalInstanceTermMatrix
  simp only [List.map_ofFn]
  rw [List.ofFn_inj]
  funext p
  simp only [Function.comp_apply, List.map_ofFn]
  rw [List.ofFn_inj]
  funext column
  exact (vestaAugmentedRepresentationTerms_sum basis
    (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).coeffs
  ).trans (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).hEq

/-- Reified canonical commitment values in the same matrix shape expected by the verifier. -/
structure AdaptiveStatementCanonicalInstanceCache {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) where
  values : List (List VestaG)
  values_eq : values = List.ofFn fun p => List.ofFn fun column =>
    (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).point

namespace AdaptiveStatementCanonicalInstanceCache

/-- Total verifier-facing commitment function recovered from the reified matrix.  Configured
columns read the computed values; unconfigured columns use the protocol's canonical blind point. -/
def commitment {pp : ProofParams} {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)}
    (cache : AdaptiveStatementCanonicalInstanceCache family basis output) :
    Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG :=
  fun p column => (cache.values.getD p []).getD column (basis AugmentedIndex.w)

theorem commitment_eq {pp : ProofParams} {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)}
    (cache : AdaptiveStatementCanonicalInstanceCache family basis output) :
    cache.commitment = adaptiveActionStatementInstanceCommitment pp basis output.inputs := by
  funext p column
  unfold commitment
  rw [cache.values_eq]
  have hp : p.val < pp.numProofs := by
    simpa [AdaptiveActionStatementShape] using p.isLt
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · simp only [AdaptiveActionStatementShape,
      CircuitShape.withProofParams_numInstanceColumns,
      Halo2.TopLevelCircuit.shape_numInstanceColumns] at hcolumn
    simp [List.getD, hp, hcolumn,
      canonicalAdaptiveStatementInstanceRepresentation]
    apply congrArg (fun q =>
      adaptiveActionStatementInstanceCommitment pp basis output.inputs q column)
    apply Fin.ext
    rfl
  · have hbounded := congrFun
      (congrFun (adaptiveActionStatementInstanceCommitment_eq_bounded pp basis output.inputs) p)
      column
    simp only [AdaptiveActionStatementShape,
      CircuitShape.withProofParams_numInstanceColumns,
      Halo2.TopLevelCircuit.shape_numInstanceColumns] at hcolumn
    rw [hbounded]
    simp [boundedAdaptiveStatementInstanceCommitment, List.getD, hp, hcolumn,
      ursOfAugmentedBasis]

end AdaptiveStatementCanonicalInstanceCache

/-- Compute the canonical instance commitment cache through certified MSM nodes. -/
def costedAdaptiveStatementCanonicalInstanceCache {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    CostedVestaComp (AdaptiveStatementCanonicalInstanceCache family basis output) :=
  CostedVestaComp.map (fun evaluated =>
    { values := evaluated.1
      values_eq := evaluated.2.trans
        (adaptiveStatementCanonicalInstanceTermMatrix_eval family basis output) })
    (CostedVestaComp.evalMsmMatrixCertified
      (adaptiveStatementCanonicalInstanceTermMatrix family basis output))

@[simp] theorem costedAdaptiveStatementCanonicalInstanceCache_run_commitment
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (costedAdaptiveStatementCanonicalInstanceCache family basis output).run.commitment =
      adaptiveActionStatementInstanceCommitment pp basis output.inputs :=
  (costedAdaptiveStatementCanonicalInstanceCache family basis output).run.commitment_eq

@[simp] theorem costedAdaptiveStatementCanonicalInstanceCache_groupWork
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (costedAdaptiveStatementCanonicalInstanceCache family basis output).groupWork =
      (AdaptiveActionStatementShape pp).numProofs *
        (AdaptiveActionStatementShape pp).numInstanceColumns *
          adaptiveStatementBasisWidth pp := by
  simp [costedAdaptiveStatementCanonicalInstanceCache,
    adaptiveStatementCanonicalInstanceTermMatrix, adaptiveStatementBasisWidth,
    List.sum_ofFn, Nat.mul_assoc]

/-- Acceptance driven by the same reified MSM, with an intrinsic equation to the ordinary
executable check.  The equation lets later costed branches consume the reified verdict without
re-running `accepts?V` in a host-language `pure` payload. -/
def costedAcceptsVCertified {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    CostedVestaComp
      {result : Option (PLift (family.acceptsV basis view)) //
        result = family.accepts?V basis view} :=
  let shape := AdaptiveActionStatementShape pp
  let urs := ursOfAugmentedBasis shape.k basis
  match hassemble : assemble? (adaptiveActionStatementVk pp basis)
      instanceCache.commitment
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := shape.k) view.pre view.rounds) with
  | none => CostedVestaComp.pure ⟨none, by
      have hassembleOriginal : assemble? (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
          view.output.toAlgebraicWfProof.proof.1
          (chRecord (k := shape.k) view.pre view.rounds) = none := by
        simpa only [instanceCache.commitment_eq] using hassemble
      have hreject : ¬family.acceptsV basis view := by
        unfold acceptsV DeployedAccepts
        rw [hassembleOriginal]
        simp
      simp [accepts?V, hreject]⟩
  | some msm =>
      CostedVestaComp.bind
        (CostedVestaComp.vestaMsmCertified (vestaAssembledMsmTerms urs msm)) fun evaluated =>
      if hzero : evaluated.1 = 0 then
        let hassembleOriginal : assemble? (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
            view.output.toAlgebraicWfProof.proof.1
            (chRecord (k := shape.k) view.pre view.rounds) = some msm := by
          simpa only [instanceCache.commitment_eq] using hassemble
        let haccepts : family.acceptsV basis view := by
          unfold acceptsV DeployedAccepts
          rw [hassembleOriginal]
          rw [evaluated.2, vestaAssembledMsmTerms_sum] at hzero
          exact hzero
        CostedVestaComp.pure ⟨some ⟨haccepts⟩, by
          simp [accepts?V, haccepts]⟩
      else
        CostedVestaComp.pure ⟨none, by
          have hassembleOriginal : assemble? (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
              view.output.toAlgebraicWfProof.proof.1
              (chRecord (k := shape.k) view.pre view.rounds) = some msm := by
            simpa only [instanceCache.commitment_eq] using hassemble
          have heval : msm.eval urs ≠ 0 := by
            intro hz
            apply hzero
            rw [evaluated.2, vestaAssembledMsmTerms_sum, hz]
          have hreject : ¬family.acceptsV basis view := by
            unfold acceptsV DeployedAccepts
            rw [hassembleOriginal]
            exact heval
          simp [accepts?V, hreject]⟩

/-- The selected verifier acceptance check executed through a concrete reified MSM. -/
def costedAcceptsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    CostedVestaComp (Option (PLift (family.acceptsV basis view))) :=
  CostedVestaComp.map Subtype.val (family.costedAcceptsVCertified basis view instanceCache)

@[simp] theorem costedAcceptsVCertified_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsVCertified basis view instanceCache).run =
      ⟨family.accepts?V basis view, rfl⟩ := by
  apply Subtype.ext
  exact (family.costedAcceptsVCertified basis view instanceCache).run.property

@[simp] theorem costedAcceptsVCertified_groupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsVCertified basis view instanceCache).groupWork =
      deployedAssembleGroupOps (adaptiveActionStatementVk pp basis)
        instanceCache.commitment
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := by
  unfold costedAcceptsVCertified deployedAssembleGroupOps
  dsimp only
  split
  · rename_i hassemble
    simp [hassemble]
  · rename_i msm hassemble
    simp only [CostedVestaComp.groupWork_bind,
      CostedVestaComp.groupWork_vestaMsmCertified,
      CostedVestaComp.run_vestaMsmCertified]
    rw [vestaAssembledMsmTerms_length]
    split <;> simp [hassemble, ursOfAugmentedBasis]

theorem costedAcceptsVCertified_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsVCertified basis view instanceCache).groupWork ≤
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  rw [family.costedAcceptsVCertified_groupWork basis view instanceCache]
  exact deployedAssembleGroupOps_le _ _ _ _

@[simp] theorem costedAcceptsV_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsV basis view instanceCache).run = family.accepts?V basis view := by
  simp [costedAcceptsV]

/-- Operational acceptance work is the term count of the actual assembled MSM. -/
theorem costedAcceptsV_groupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsV basis view instanceCache).groupWork =
      deployedAssembleGroupOps (adaptiveActionStatementVk pp basis)
        instanceCache.commitment
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := by
  simp [costedAcceptsV, family.costedAcceptsVCertified_groupWork basis view instanceCache]

theorem costedAcceptsV_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis view.output) :
    (family.costedAcceptsV basis view instanceCache).groupWork ≤
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  rw [family.costedAcceptsV_groupWork basis view instanceCache]
  exact deployedAssembleGroupOps_le _ _ _ _

/-- Result of the operational four-stage finder.  The retained implication is group-free proof
data used by the extractor when the relation branch is empty. -/
structure AdaptiveStatementOperationalFinderResult {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  value : Option (AlgebraicRelationWitness (F := Fp) basis)
  calls : Nat
  instanceCache : AdaptiveStatementCanonicalInstanceCache family basis cache.output
  provenance_none : value = none →
    family.provenanceRelationFinderOfCachedRun basis cache = none

/-- Data-bearing verdict of the group-free provenance stage. -/
inductive AdaptiveStatementProvenanceVerdict {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  | found (relation : AlgebraicRelationWitness (F := Fp) basis)
      (hfound : family.provenanceRelationFinderOfCachedRun basis cache = some relation)
  | clear (hnone : family.provenanceRelationFinderOfCachedRun basis cache = none)

/-- Provenance verdict together with the already-established facts consumed after a clear pass. -/
structure AdaptiveStatementProvenancePlan {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  facts : family.provenanceRelationFinderOfCachedRun basis cache = none →
    family.SemanticStageFacts basis cache.toRunView
  verdict : AdaptiveStatementProvenanceVerdict family basis cache

/-- Evaluate provenance once and retain its equation for the operational program. -/
def adaptiveStatementProvenancePlan {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (facts : family.provenanceRelationFinderOfCachedRun basis cache = none →
      family.SemanticStageFacts basis cache.toRunView) :
    AdaptiveStatementProvenancePlan family basis cache :=
  { facts := facts
    verdict :=
      match hprovenance : family.provenanceRelationFinderOfCachedRun basis cache with
      | some relation => .found relation hprovenance
      | none => .clear hprovenance }

/-- Operational quotient, identity, and terminal stages after provenance has been discharged. -/
def adaptiveStatementFinderAfterProvenanceProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (instanceCache : AdaptiveStatementCanonicalInstanceCache family basis cache.output)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.SemanticStageFacts basis cache.toRunView)
    (hprovenance : family.provenanceRelationFinderOfCachedRun basis cache = none) :
    CostedVestaComp (AdaptiveStatementOperationalFinderResult family basis cache) :=
  match family.statementQuotientRelationFinderV basis cache.toRunView with
  | some relation => CostedVestaComp.pure
      { value := some relation
        calls := 2
        instanceCache := instanceCache
        provenance_none := fun _ => hprovenance }
  | none =>
      CostedVestaComp.bind
        (family.costedAcceptsVCertified basis cache.toRunView instanceCache)
        fun acceptance =>
      match family.identityRelationFinderWithAcceptanceV basis cache.toRunView hcharV
          acceptance.1 none (fun _ => facts) with
      | some relation => CostedVestaComp.pure
          { value := some relation
            calls := 3
            instanceCache := instanceCache
            provenance_none := fun _ => hprovenance }
      | none =>
          CostedVestaComp.bind
            (family.costedAcceptsVCertified basis cache.toRunView instanceCache)
            fun acceptance =>
          CostedVestaComp.pure
            { value := (family.terminalRelationFinderWithAcceptanceV basis cache.toRunView
                hcharV acceptance.1)
              calls := 4
              instanceCache := instanceCache
              provenance_none := fun _ => hprovenance }

@[simp] theorem adaptiveStatementFinderAfterProvenanceProgram_run_pair {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV)
    (instanceCache) (facts) (hprovenance) :
    let result := (adaptiveStatementFinderAfterProvenanceProgram family basis cache instanceCache hcharV
      facts hprovenance).run
    (result.value, result.calls) =
      family.relationFinderAfterCachedProvenance basis cache hcharV facts := by
  cases hquotient : family.statementQuotientRelationFinderV basis cache.toRunView with
  | some relation =>
      simp [adaptiveStatementFinderAfterProvenanceProgram,
        relationFinderAfterCachedProvenance, hquotient]
  | none =>
      cases hidentity : family.identityRelationFinderWithAcceptanceV basis cache.toRunView
          hcharV (family.accepts?V basis cache.toRunView) none (fun _ => facts) with
      | some relation =>
          simp [adaptiveStatementFinderAfterProvenanceProgram,
            relationFinderAfterCachedProvenance, identityRelationFinderV,
            hquotient, hidentity]
      | none =>
          simp [adaptiveStatementFinderAfterProvenanceProgram,
            relationFinderAfterCachedProvenance, identityRelationFinderV,
            terminalRelationFinderV, hquotient, hidentity]

theorem adaptiveStatementFinderAfterProvenanceProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV)
    (instanceCache) (facts) (hprovenance) :
    (adaptiveStatementFinderAfterProvenanceProgram family basis cache instanceCache hcharV facts
      hprovenance).groupWork ≤
        2 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementFinderAfterProvenanceProgram
  split
  · simp
  · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
      costedAcceptsVCertified_run]
    split
    · simp
      have haccept : deployedAssembleGroupOps
          (adaptiveActionStatementVk pp basis)
          instanceCache.commitment
          cache.toRunView.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k)
            cache.toRunView.pre cache.toRunView.rounds) ≤
            assembleGroupOpsBudget (AdaptiveActionStatementShape pp) :=
        deployedAssembleGroupOps_le _ _ _ _
      exact haccept.trans (by omega)
    · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
        costedAcceptsVCertified_run]
      simp
      have haccept : deployedAssembleGroupOps
          (adaptiveActionStatementVk pp basis)
          instanceCache.commitment
          cache.toRunView.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k)
            cache.toRunView.pre cache.toRunView.rounds) ≤
            assembleGroupOpsBudget (AdaptiveActionStatementShape pp) :=
        deployedAssembleGroupOps_le _ _ _ _
      exact (Nat.add_le_add haccept haccept).trans (by omega)

/-- Operational four-stage finder over one cached run.  Canonical instance commitments and each
verifier equation are executed through reified MSM nodes; the verifier result itself selects the
identity and terminal branches.  The remaining computations inspect field coordinates, lists, or
proof-erased evidence only. -/
def adaptiveStatementFinderReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (plan : AdaptiveStatementProvenancePlan family basis cache) :
    CostedVestaComp (AdaptiveStatementOperationalFinderResult family basis cache) :=
  CostedVestaComp.bind
    (costedAdaptiveStatementCanonicalInstanceCache family basis cache.output) fun instanceCache =>
  match plan.verdict with
  | .found relation _ => CostedVestaComp.pure
      { value := some relation
        calls := 1
        instanceCache := instanceCache
        provenance_none := by simp }
  | .clear hprovenance =>
      adaptiveStatementFinderAfterProvenanceProgram family basis cache instanceCache hcharV
        (plan.facts hprovenance) hprovenance

@[simp] theorem adaptiveStatementFinderReductionProgram_run_pair {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    let result :=
      (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run
    (result.value, result.calls) =
      family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts := by
  cases plan with
  | mk facts verdict =>
    cases verdict with
    | found relation hprovenance =>
      rw [family.relationFinderWithCallsOfCachedRun_of_some basis cache hcharV facts
        relation hprovenance]
      simp [adaptiveStatementFinderReductionProgram]
    | clear hprovenance =>
      rw [family.relationFinderWithCallsOfCachedRun_of_none basis cache hcharV facts
        hprovenance]
      unfold adaptiveStatementFinderReductionProgram
      simp [adaptiveStatementFinderAfterProvenanceProgram_run_pair]

@[simp] theorem adaptiveStatementFinderReductionProgram_run_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run.value =
      (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).1 := by
  exact congrArg Prod.fst
    (adaptiveStatementFinderReductionProgram_run_pair family basis cache hcharV plan)

@[simp] theorem adaptiveStatementFinderReductionProgram_run_calls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run.calls =
      (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).2 := by
  exact congrArg Prod.snd
    (adaptiveStatementFinderReductionProgram_run_pair family basis cache hcharV plan)

/-- Operational witness extraction over the same finder program.  A retained relation returns no
witness; otherwise a third reified verifier execution drives the post-finder outcome. -/
def adaptiveStatementKnowledgeExtractorWithAcceptanceV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (acceptance : Option (PLift (family.acceptsV basis view)))
    (facts : family.SemanticStageFacts basis view)
    (finderResult : Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Option (ActionTerminal.ActionBundleWitness view.output.inputs) :=
  match finderResult with
  | some _ => none
  | none =>
      match family.adaptiveStatementKnowledgeOutcomeCoreWithAcceptanceV basis view hcharV
          acceptance facts with
      | some (Sum.inl witness) => some witness
      | _ => none

@[simp] theorem adaptiveStatementKnowledgeExtractorWithAcceptanceV_accepts {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (view) (hcharV) (facts)
    (finderResult) :
    family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis view hcharV
        (family.accepts?V basis view) facts finderResult =
      family.adaptiveStatementKnowledgeExtractorV basis view hcharV finderResult
        (fun _ => facts) := by
  cases finderResult <;> rfl

def adaptiveStatementExtractorReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (plan : AdaptiveStatementProvenancePlan family basis cache) :
    CostedVestaComp (Option (ActionTerminal.ActionBundleWitness cache.output.inputs)) :=
  match plan.verdict with
  | .found _ _ =>
      CostedVestaComp.bind
        (adaptiveStatementFinderReductionProgram family basis cache hcharV plan) fun _ =>
      CostedVestaComp.pure none
  | .clear hprovenance =>
      let facts := plan.facts hprovenance
      CostedVestaComp.bind
        (adaptiveStatementFinderReductionProgram family basis cache hcharV plan) fun finder =>
      match finder.value with
      | some _ => CostedVestaComp.pure none
      | none =>
          CostedVestaComp.bind
            (family.costedAcceptsVCertified basis cache.toRunView finder.instanceCache)
            fun acceptance =>
          CostedVestaComp.pure
            (family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis cache.toRunView
              hcharV acceptance.1 facts none)

@[simp] theorem adaptiveStatementExtractorReductionProgram_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV plan).run =
      match plan.verdict with
      | .found _ _ => none
      | .clear hprovenance =>
          family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis cache.toRunView
            hcharV (family.accepts?V basis cache.toRunView) (plan.facts hprovenance)
            (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).1 := by
  cases plan with
  | mk facts verdict =>
    cases verdict with
    | found relation hprovenance =>
      unfold adaptiveStatementExtractorReductionProgram
      simp
    | clear hprovenance =>
      unfold adaptiveStatementExtractorReductionProgram
      rw [CostedVestaComp.run_bind,
        adaptiveStatementFinderReductionProgram_run_value]
      split <;> simp_all [adaptiveStatementKnowledgeExtractorWithAcceptanceV]
      all_goals rfl

@[simp] theorem adaptiveStatementExtractorReductionProgram_run_provenancePlan
    {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (facts) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV
      (adaptiveStatementProvenancePlan family basis cache facts)).run =
      family.adaptiveStatementKnowledgeExtractorV basis cache.toRunView hcharV
        (family.relationFinderWithCallsOfCachedRun basis cache hcharV facts).1
        (fun hnone => facts
          (family.relationFinderWithCallsOfCachedRun_none_provenance basis cache hcharV facts
            hnone)) := by
  rw [adaptiveStatementExtractorReductionProgram_run]
  unfold adaptiveStatementProvenancePlan
  split
  · rename_i verdict relation hfound hplan
    simp only [family.relationFinderWithCallsOfCachedRun_of_some basis cache hcharV facts
      relation hfound]
    rfl
  · simp_all [relationFinderWithCallsOfCachedRun]

theorem adaptiveStatementFinderReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns *
            adaptiveStatementBasisWidth pp +
        2 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementCanonicalInstanceCache_groupWork]
  cases plan.verdict with
  | found => simp
  | clear hprovenance =>
      exact Nat.add_le_add_left
        (adaptiveStatementFinderAfterProvenanceProgram_groupWork_le family basis cache hcharV
          (costedAdaptiveStatementCanonicalInstanceCache family basis cache.output).run
          (plan.facts hprovenance) hprovenance) _

theorem adaptiveStatementExtractorReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV plan).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns *
            adaptiveStatementBasisWidth pp +
        3 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementExtractorReductionProgram
  have hfinder := adaptiveStatementFinderReductionProgram_groupWork_le
    family basis cache hcharV plan
  simp only [AdaptiveActionStatementShape,
    CircuitShape.withProofParams_numProofs,
    CircuitShape.withProofParams_numInstanceColumns,
    Halo2.TopLevelCircuit.shape_numInstanceColumns] at hfinder ⊢
  cases plan.verdict with
  | found =>
    rw [CostedVestaComp.groupWork_bind]
    simp
    exact hfinder.trans (by omega)
  | clear =>
    rw [CostedVestaComp.groupWork_bind]
    split
    · simp
      exact hfinder.trans (by omega)
    · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
        costedAcceptsVCertified_run]
      simp only [CostedVestaComp.groupWork_pure, Nat.add_zero]
      have haccept := deployedAssembleGroupOps_le
        (adaptiveActionStatementVk pp basis)
        ((adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run).instanceCache.commitment
        cache.toRunView.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k)
          cache.toRunView.pre cache.toRunView.rounds)
      simp only [AdaptiveActionStatementShape] at haccept
      exact (Nat.add_le_add hfinder haccept).trans (by omega)

/-- Conservative structural envelope for the complete relation finder.  It intentionally retains
the previously published slack for quotient and terminal proof construction; the executable
program below is proved to fit it. -/
def adaptiveStatementFinderReductionGroupWork (pp : ProofParams) : Nat :=
  let shape := AdaptiveActionStatementShape pp
  let width := adaptiveStatementBasisWidth pp
  2 * width +
    shape.numProofs * shape.numInstanceColumns * width +
    (2 * width + shape.numQuotientPieces) +
    assembleGroupOpsBudget shape +
    (4 * width + assembleGroupOpsBudget shape)

/-- Conservative structural envelope for relation finding plus witness projection. -/
def adaptiveStatementReductionGroupWork (pp : ProofParams) : Nat :=
  adaptiveStatementFinderReductionGroupWork pp +
    (4 * adaptiveStatementBasisWidth pp +
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp))

theorem adaptiveStatementFinderReductionGroupWork_le (pp : ProofParams) :
    adaptiveStatementFinderReductionGroupWork pp ≤
      adaptiveStatementReductionGroupWork pp :=
  Nat.le_add_right _ _

/-- Closed shape formula for the worst-case reduction group-operation envelope. -/
theorem adaptiveStatementReductionGroupWork_eq (pp : ProofParams) :
    adaptiveStatementReductionGroupWork pp =
      let shape := AdaptiveActionStatementShape pp
      let width := adaptiveStatementBasisWidth pp
      2 * width +
        shape.numProofs * shape.numInstanceColumns * width +
        (2 * width + shape.numQuotientPieces) +
        assembleGroupOpsBudget shape +
        (4 * width + assembleGroupOpsBudget shape) +
        (4 * width + assembleGroupOpsBudget shape) := by
  rfl

/-- Internal representation of one instrumented execution.  Its constructor is private so callers
cannot attach an unrelated work object to a value. -/
private inductive AdaptiveStatementInstrumentationSeal where
  | seal

/-- Value returned by the one composed execution.  The adversary output and reduction result are
projections of the same closed costed program, so neither can be paired with a detached counter. -/
structure AdaptiveStatementCostedExecutionResult {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (α : Type*) where
  adversaryOutput :
    AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)
  value : α

private inductive AdaptiveStatementCostedExecutionCore (pp : ProofParams)
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (α : Type*) where
  | mk (marker : AdaptiveStatementInstrumentationSeal)
      (adversaryProgram : CostedLabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)))
      (oracle : family.Coins)
      (program : CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis α))

/-- One cached execution whose adversary metadata, oracle path, returned values, and total work are
projections of a single private composition object. -/
abbrev AdaptiveStatementCostedExecution {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (α : Type*) :=
  AdaptiveStatementCostedExecutionCore pp family basis α

namespace AdaptiveStatementCostedExecution

variable {pp : ProofParams} {family : ComputedAdaptiveActionStatementFSFamily pp}
  {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG} {α : Type*}

/-- The exact costed adversary invoked by this execution. -/
def adversaryProgram : AdaptiveStatementCostedExecution family basis α →
    CostedLabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis)
      (AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
  | .mk _ program _ _ => program

/-- The oracle table selecting both the adversary path and its group-work path. -/
def oracle : AdaptiveStatementCostedExecution family basis α → family.Coins
  | .mk _ _ O _ => O

/-- The one value-threaded program that evaluates the basis, specializes the adversary path,
constructs its cache, and consumes that cache in reduction postprocessing. -/
def program : AdaptiveStatementCostedExecution family basis α →
    CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis α)
  | .mk _ _ _ program => program

/-- Output of the adversary program carried by this same composition object. -/
def adversaryOutput (execution : AdaptiveStatementCostedExecution family basis α) :
    AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis) :=
  execution.program.run.adversaryOutput

def value (execution : AdaptiveStatementCostedExecution family basis α) : α :=
  execution.program.run.value

/-- Adversary work is evaluated from the carried syntax on the carried oracle path; it cannot be
supplied as a detached natural number. -/
def proverGroupWork (execution : AdaptiveStatementCostedExecution family basis α) : Nat :=
  execution.adversaryProgram.groupWork execution.oracle

/-- Complete group work is read directly from the same program that returns the two values. -/
def groupWork (execution : AdaptiveStatementCostedExecution family basis α) : Nat :=
  execution.program.groupWork

end AdaptiveStatementCostedExecution

/-- Relation-finder postprocessing over an explicitly supplied one-execution cache. Every
executable branch consumes `cache` itself. -/
def cachedRelationFinderReductionProgramAtReifiedBasisFromCache {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis)
    (cache : CachedRun pp family reified.basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp reified.basis)
      (adaptiveActionStatementInstanceCommitment pp reified.basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.provenanceRelationFinderOfCachedRun reified.basis cache = none →
      family.SemanticStageFacts reified.basis cache.toRunView) :
    CostedVestaComp (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  let plan := adaptiveStatementProvenancePlan family reified.basis cache facts
  let program := CostedVestaComp.map AdaptiveStatementOperationalFinderResult.value
    (adaptiveStatementFinderReductionProgram family reified.basis cache hcharV plan)
  CostedVestaComp.map (fun value => reified.basis_eq ▸ value) program

/-- Witness-extractor postprocessing over the same explicitly supplied cache. -/
def cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis) (O : family.Coins)
    (cache : CachedRun pp family reified.basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp reified.basis)
      (adaptiveActionStatementInstanceCommitment pp reified.basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.provenanceRelationFinderOfCachedRun reified.basis cache = none →
      family.SemanticStageFacts reified.basis cache.toRunView)
    (hinputs : cache.output.inputs = (family.runOutput reified.basis O).inputs) :
    CostedVestaComp
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  let plan := adaptiveStatementProvenancePlan family reified.basis cache facts
  let program := CostedVestaComp.map (fun value => hinputs ▸ value)
    (adaptiveStatementExtractorReductionProgram family reified.basis cache hcharV plan)
  CostedVestaComp.map (fun value => reified.basis_eq ▸ value) program

/-- Relation-finder postprocessing at a basis recovered from reified MSM values. -/
def cachedRelationFinderReductionProgramAtReifiedBasis {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis) (O : family.Coins) :
    CostedVestaComp (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  let cache := family.cachedRun reified.basis O
  let hcharV := family.cachedRun_pairCount_lt hchar reified.basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none reified.basis O
  let plan := adaptiveStatementProvenancePlan family reified.basis cache facts
  let program := CostedVestaComp.map AdaptiveStatementOperationalFinderResult.value
    (adaptiveStatementFinderReductionProgram family reified.basis cache hcharV plan)
  CostedVestaComp.map (fun value => reified.basis_eq ▸ value) program

/-- Witness-extractor postprocessing at a basis recovered from reified MSM values. -/
def cachedKnowledgeExtractorReductionProgramAtReifiedBasis {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis) (O : family.Coins) :
    CostedVestaComp
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  let cache := family.cachedRun reified.basis O
  let hcharV := family.cachedRun_pairCount_lt hchar reified.basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none reified.basis O
  let plan := adaptiveStatementProvenancePlan family reified.basis cache facts
  let hinputs : cache.output.inputs = (family.runOutput reified.basis O).inputs :=
    congrArg AdaptiveActionStatementOutput.inputs
      (family.cachedRun_output_eq reified.basis O)
  let program := CostedVestaComp.map (fun value => hinputs ▸ value)
    (adaptiveStatementExtractorReductionProgram family reified.basis cache hcharV plan)
  CostedVestaComp.map (fun value => reified.basis_eq ▸ value) program

theorem cachedRelationFinderReductionProgramAtReifiedBasisFromCache_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O)
    (cache : CachedRun pp family reified.basis)
    (hcache : cache = family.cachedRun reified.basis O) (hcharV) (facts) :
    family.cachedRelationFinderReductionProgramAtReifiedBasisFromCache
        basis reified cache hcharV facts =
      family.cachedRelationFinderReductionProgramAtReifiedBasis hchar basis reified O := by
  subst cache
  rfl

theorem cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O)
    (cache : CachedRun pp family reified.basis)
    (hcache : cache = family.cachedRun reified.basis O) (hcharV) (facts) (hinputs) :
    family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache
        basis reified O cache hcharV facts hinputs =
      family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis hchar basis reified O := by
  subst cache
  rfl

/-- Complete relation reduction: construct a basis through charged MSMs, then consume exactly the
recovered function in the adversary and finder. -/
def cachedRelationFinderReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    CostedVestaComp (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  CostedVestaComp.bind (costedAdaptiveStatementSelectedBasisCache pp basis) fun reified =>
    family.cachedRelationFinderReductionProgramAtReifiedBasis hchar basis reified O

/-- Complete witness reduction with the same charged, data-coupled basis construction. -/
def cachedKnowledgeExtractorReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    CostedVestaComp
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  CostedVestaComp.bind (costedAdaptiveStatementSelectedBasisCache pp basis) fun reified =>
    family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis hchar basis reified O

@[simp] theorem cachedRelationFinderReductionProgramAtReifiedBasis_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O) :
    (family.cachedRelationFinderReductionProgramAtReifiedBasis hchar basis reified O).run =
      family.cachedRelationFinder hchar basis O := by
  rcases reified with ⟨reifiedBasis, hbasis⟩
  subst reifiedBasis
  simp [cachedRelationFinderReductionProgramAtReifiedBasis,
    cachedRelationFinder, cachedRelationFinderWithCalls]

@[simp] theorem cachedKnowledgeExtractorReductionProgramAtReifiedBasis_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O) :
    (family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis hchar basis reified O).run =
      family.cachedKnowledgeExtractor hchar basis O := by
  rcases reified with ⟨reifiedBasis, hbasis⟩
  subst reifiedBasis
  unfold cachedKnowledgeExtractorReductionProgramAtReifiedBasis cachedKnowledgeExtractor
    cachedKnowledgeExecution
  dsimp only
  rw [CostedVestaComp.run_map, CostedVestaComp.run_map,
    adaptiveStatementExtractorReductionProgram_run_provenancePlan]

@[simp] theorem cachedRelationFinderReductionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (O) :
    (family.cachedRelationFinderReductionProgram hchar basis O).run =
      family.cachedRelationFinder hchar basis O := by
  simp [cachedRelationFinderReductionProgram]

@[simp] theorem cachedKnowledgeExtractorReductionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (O) :
    (family.cachedKnowledgeExtractorReductionProgram hchar basis O).run =
      family.cachedKnowledgeExtractor hchar basis O := by
  simp [cachedKnowledgeExtractorReductionProgram]

theorem cachedRelationFinderReductionProgramAtReifiedBasis_groupWork_le
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O) :
    (family.cachedRelationFinderReductionProgramAtReifiedBasis hchar basis reified O).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns * adaptiveStatementBasisWidth pp +
        2 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold cachedRelationFinderReductionProgramAtReifiedBasis
  simp only [CostedVestaComp.groupWork_map]
  exact adaptiveStatementFinderReductionProgram_groupWork_le family reified.basis
    (family.cachedRun reified.basis O) (family.cachedRun_pairCount_lt hchar reified.basis O)
    (adaptiveStatementProvenancePlan family reified.basis (family.cachedRun reified.basis O)
      (family.semanticStageFacts_of_cachedProvenance_none reified.basis O))

theorem cachedKnowledgeExtractorReductionProgramAtReifiedBasis_groupWork_le
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis) (reified : AdaptiveStatementBasisCache pp basis) (O) :
    (family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis hchar basis reified O).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns * adaptiveStatementBasisWidth pp +
        3 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold cachedKnowledgeExtractorReductionProgramAtReifiedBasis
  simp only [CostedVestaComp.groupWork_map]
  exact adaptiveStatementExtractorReductionProgram_groupWork_le family reified.basis
    (family.cachedRun reified.basis O) (family.cachedRun_pairCount_lt hchar reified.basis O)
    (adaptiveStatementProvenancePlan family reified.basis (family.cachedRun reified.basis O)
      (family.semanticStageFacts_of_cachedProvenance_none reified.basis O))

/-- The exact DLOG-programmed relation reduction.  Unlike the generic selected-basis wrapper, its
charged MSM operands are the reduction coins `(x,y)` and challenge points `(B,C)`. -/
def programmedCachedRelationFinderReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp)
    (O : family.Coins) :
    CostedVestaComp
      (Option (AlgebraicRelationWitness (F := Fp) (fun i => x i • B + y i • C))) :=
  CostedVestaComp.bind (costedAdaptiveStatementProgrammedBasisCache pp B C x y) fun reified =>
    family.cachedRelationFinderReductionProgramAtReifiedBasis hchar
      (fun i => x i • B + y i • C) reified O

/-- The exact DLOG-programmed witness reduction. -/
def programmedCachedKnowledgeExtractorReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp)
    (O : family.Coins) :
    CostedVestaComp (Option (ActionTerminal.ActionBundleWitness
      (family.runOutput (fun i => x i • B + y i • C) O).inputs)) :=
  CostedVestaComp.bind (costedAdaptiveStatementProgrammedBasisCache pp B C x y) fun reified =>
    family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis hchar
      (fun i => x i • B + y i • C) reified O

@[simp] theorem programmedCachedRelationFinderReductionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B C : VestaG) (x y) (O) :
    (family.programmedCachedRelationFinderReductionProgram hchar B C x y O).run =
      family.cachedRelationFinder hchar (fun i => x i • B + y i • C) O := by
  simp [programmedCachedRelationFinderReductionProgram]

@[simp] theorem programmedCachedKnowledgeExtractorReductionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B C : VestaG) (x y) (O) :
    (family.programmedCachedKnowledgeExtractorReductionProgram hchar B C x y O).run =
      family.cachedKnowledgeExtractor hchar (fun i => x i • B + y i • C) O := by
  simp [programmedCachedKnowledgeExtractorReductionProgram]

theorem programmedCachedRelationFinderReductionProgram_groupWork_le
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B C : VestaG) (x y) (O) :
    (family.programmedCachedRelationFinderReductionProgram hchar B C x y O).groupWork ≤
      adaptiveStatementFinderReductionGroupWork pp := by
  unfold programmedCachedRelationFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork]
  have hprogram :=
    family.cachedRelationFinderReductionProgramAtReifiedBasis_groupWork_le hchar
      (fun i => x i • B + y i • C)
      (costedAdaptiveStatementProgrammedBasisCache pp B C x y).run O
  refine (Nat.add_le_add_left hprogram _).trans ?_
  simp only [adaptiveStatementFinderReductionGroupWork]
  omega

theorem programmedCachedKnowledgeExtractorReductionProgram_groupWork_le
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B C : VestaG) (x y) (O) :
    (family.programmedCachedKnowledgeExtractorReductionProgram hchar B C x y O).groupWork ≤
      adaptiveStatementReductionGroupWork pp := by
  unfold programmedCachedKnowledgeExtractorReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork]
  have hprogram :=
    family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis_groupWork_le hchar
      (fun i => x i • B + y i • C)
      (costedAdaptiveStatementProgrammedBasisCache pp B C x y).run O
  refine (Nat.add_le_add_left hprogram _).trans ?_
  simp only [adaptiveStatementReductionGroupWork,
    adaptiveStatementFinderReductionGroupWork]
  omega

/-- The points produced by textbook DLOG programming are exactly the scalar basis used by the
probability reduction. -/
theorem adaptiveStatementProgrammedBasis_eq_scalarBasis {pp : ProofParams}
    (B : VestaG) (z : Fp)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    (fun i => x i • B + y i • (z • B)) =
      scalarBasis B (programmedLogs z x y) := by
  funext i
  exact (programmedEmbedding B z x y).programmed i |>.symm

theorem programmedCachedRelationFinderReductionProgram_run_isSome_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B : VestaG) (z : Fp) (x y) (O) :
    (family.programmedCachedRelationFinderReductionProgram hchar B (z • B) x y O).run.isSome =
      (family.cachedRelationFinder hchar (scalarBasis B (programmedLogs z x y)) O).isSome := by
  rw [programmedCachedRelationFinderReductionProgram_run]
  exact congrArg (fun basis => (family.cachedRelationFinder hchar basis O).isSome)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

theorem programmedCachedRelationFinderReductionProgram_run_heq_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B : VestaG) (z : Fp) (x y) (O) :
    HEq (family.programmedCachedRelationFinderReductionProgram hchar B (z • B) x y O).run
      (family.cachedRelationFinder hchar (scalarBasis B (programmedLogs z x y)) O) := by
  rw [programmedCachedRelationFinderReductionProgram_run]
  exact congr_arg_heq (fun basis => family.cachedRelationFinder hchar basis O)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

theorem programmedCachedKnowledgeExtractorReductionProgram_run_isSome_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B : VestaG) (z : Fp) (x y) (O) :
    (family.programmedCachedKnowledgeExtractorReductionProgram hchar B (z • B) x y O).run.isSome =
      (family.cachedKnowledgeExtractor hchar
        (scalarBasis B (programmedLogs z x y)) O).isSome := by
  rw [programmedCachedKnowledgeExtractorReductionProgram_run]
  exact congrArg (fun basis => (family.cachedKnowledgeExtractor hchar basis O).isSome)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

theorem programmedCachedKnowledgeExtractorReductionProgram_run_heq_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (B : VestaG) (z : Fp) (x y) (O) :
    HEq (family.programmedCachedKnowledgeExtractorReductionProgram hchar B (z • B) x y O).run
      (family.cachedKnowledgeExtractor hchar
        (scalarBasis B (programmedLogs z x y)) O) := by
  rw [programmedCachedKnowledgeExtractorReductionProgram_run]
  exact congr_arg_heq (fun basis => family.cachedKnowledgeExtractor hchar basis O)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

/-! ## One value-threaded execution programs

These continuations consume the proof-carrying cache returned by
`certifiedCachedRunProgram`.  The cache used by postprocessing is therefore the actual value
produced by the selected adversary path, not a second host recomputation known only to be equal.
-/

private def certifiedRelationFinderExecutionContinuation {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis) (O : family.Coins)
    (certifiedCache : {cache : CachedRun pp family reified.basis //
      cache = certificate.certifiedCachedRun reified.basis O}) :
    CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis
      (Option (AlgebraicRelationWitness (F := Fp) basis))) :=
  let cache := certifiedCache.1
  let PairCountProperty := fun candidate : CachedRun pp family reified.basis =>
    deployedX4PairCount (adaptiveActionStatementVk pp reified.basis)
      (adaptiveActionStatementInstanceCommitment pp reified.basis candidate.output.inputs)
      candidate.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) candidate.pre candidate.rounds) <
        Zcash.Arithmetic.scalarFieldOrder
  let SemanticProperty := fun candidate : CachedRun pp family reified.basis =>
    family.provenanceRelationFinderOfCachedRun reified.basis candidate = none →
      family.SemanticStageFacts reified.basis candidate.toRunView
  let hcharV : PairCountProperty cache :=
    Eq.mpr (congrArg PairCountProperty certifiedCache.2)
      (certificate.certifiedCachedRun_pairCount_lt hchar reified.basis O)
  let facts : SemanticProperty cache :=
    Eq.mpr (congrArg SemanticProperty certifiedCache.2)
      (certificate.certifiedCachedRun_semanticStageFacts reified.basis O)
  CostedVestaComp.map (fun value =>
      { adversaryOutput := reified.basis_eq ▸ cache.output
        value := value })
    (family.cachedRelationFinderReductionProgramAtReifiedBasisFromCache
      basis reified cache hcharV facts)

private def certifiedKnowledgeExtractorExecutionContinuation {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (reified : AdaptiveStatementBasisCache pp basis) (O : family.Coins)
    (certifiedCache : {cache : CachedRun pp family reified.basis //
      cache = certificate.certifiedCachedRun reified.basis O}) :
    CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs))) :=
  let cache := certifiedCache.1
  let PairCountProperty := fun candidate : CachedRun pp family reified.basis =>
    deployedX4PairCount (adaptiveActionStatementVk pp reified.basis)
      (adaptiveActionStatementInstanceCommitment pp reified.basis candidate.output.inputs)
      candidate.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) candidate.pre candidate.rounds) <
        Zcash.Arithmetic.scalarFieldOrder
  let SemanticProperty := fun candidate : CachedRun pp family reified.basis =>
    family.provenanceRelationFinderOfCachedRun reified.basis candidate = none →
      family.SemanticStageFacts reified.basis candidate.toRunView
  let InputsProperty := fun candidate : CachedRun pp family reified.basis =>
    candidate.output.inputs = (family.runOutput reified.basis O).inputs
  let hcharV : PairCountProperty cache :=
    Eq.mpr (congrArg PairCountProperty certifiedCache.2)
      (certificate.certifiedCachedRun_pairCount_lt hchar reified.basis O)
  let facts : SemanticProperty cache :=
    Eq.mpr (congrArg SemanticProperty certifiedCache.2)
      (certificate.certifiedCachedRun_semanticStageFacts reified.basis O)
  let hinputs : InputsProperty cache :=
    Eq.mpr (congrArg InputsProperty certifiedCache.2)
      (certificate.certifiedCachedRun_inputs_eq reified.basis O)
  CostedVestaComp.map (fun value =>
      { adversaryOutput := reified.basis_eq ▸ cache.output
        value := value })
    (family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache
      basis reified O cache hcharV facts hinputs)

/-- Compose a charged basis constructor, the exact selected adversary path, its cache, and finder
postprocessing into one closed syntax tree. -/
def certifiedRelationFinderExecutionProgramWithBasis {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (basisProgram : CostedVestaComp (AdaptiveStatementBasisCache pp basis)) :
    CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis
      (Option (AlgebraicRelationWitness (F := Fp) basis))) :=
  CostedVestaComp.bind basisProgram fun reified =>
    CostedVestaComp.bind (certificate.certifiedCachedRunProgram reified.basis O) fun cache =>
      certifiedRelationFinderExecutionContinuation
        family hchar certificate basis reified O cache

/-- Knowledge-extractor counterpart of `certifiedRelationFinderExecutionProgramWithBasis`. -/
def certifiedKnowledgeExtractorExecutionProgramWithBasis {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (basisProgram : CostedVestaComp (AdaptiveStatementBasisCache pp basis)) :
    CostedVestaComp (AdaptiveStatementCostedExecutionResult family basis
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs))) :=
  CostedVestaComp.bind basisProgram fun reified =>
    CostedVestaComp.bind (certificate.certifiedCachedRunProgram reified.basis O) fun cache =>
      certifiedKnowledgeExtractorExecutionContinuation
        family hchar certificate basis reified O cache

def certifiedCachedRelationFinderExecutionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :=
  family.certifiedRelationFinderExecutionProgramWithBasis hchar certificate basis O
    (costedAdaptiveStatementSelectedBasisCache pp basis)

def certifiedCachedKnowledgeExtractorExecutionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :=
  family.certifiedKnowledgeExtractorExecutionProgramWithBasis hchar certificate basis O
    (costedAdaptiveStatementSelectedBasisCache pp basis)

def certifiedProgrammedCachedRelationFinderExecutionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :=
  family.certifiedRelationFinderExecutionProgramWithBasis hchar certificate
    (fun i => x i • B + y i • C) O
    (costedAdaptiveStatementProgrammedBasisCache pp B C x y)

def certifiedProgrammedCachedKnowledgeExtractorExecutionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :=
  family.certifiedKnowledgeExtractorExecutionProgramWithBasis hchar certificate
    (fun i => x i • B + y i • C) O
    (costedAdaptiveStatementProgrammedBasisCache pp B C x y)

@[simp] theorem certifiedCachedRelationFinderExecutionProgram_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.certifiedCachedRelationFinderExecutionProgram
      hchar certificate basis O).run =
      { adversaryOutput := family.runOutput basis O
        value := family.cachedRelationFinder hchar basis O } := by
  unfold certifiedCachedRelationFinderExecutionProgram
    certifiedRelationFinderExecutionProgramWithBasis
  rw [CostedVestaComp.run_bind, costedAdaptiveStatementSelectedBasisCache_run,
    CostedVestaComp.run_bind, certificate.certifiedCachedRunProgram_run_eq]
  simp [certifiedRelationFinderExecutionContinuation,
    cachedRelationFinderReductionProgramAtReifiedBasisFromCache,
    cachedRelationFinder, cachedRelationFinderWithCalls]

@[simp] theorem certifiedCachedKnowledgeExtractorExecutionProgram_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.certifiedCachedKnowledgeExtractorExecutionProgram
      hchar certificate basis O).run =
      { adversaryOutput := family.runOutput basis O
        value := family.cachedKnowledgeExtractor hchar basis O } := by
  unfold certifiedCachedKnowledgeExtractorExecutionProgram
    certifiedKnowledgeExtractorExecutionProgramWithBasis
  rw [CostedVestaComp.run_bind, costedAdaptiveStatementSelectedBasisCache_run,
    CostedVestaComp.run_bind, certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedKnowledgeExtractorExecutionContinuation,
    CostedVestaComp.run_map]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache_eq
    hchar basis { basis := basis, basis_eq := rfl } O
    (certificate.certifiedCachedRun basis O)
    (certificate.certifiedCachedRun_eq basis O)]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis_run]
  simp

@[simp] theorem certifiedProgrammedCachedRelationFinderExecutionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.certifiedProgrammedCachedRelationFinderExecutionProgram
      hchar certificate B C x y O).run =
      { adversaryOutput := family.runOutput (fun i => x i • B + y i • C) O
        value := family.cachedRelationFinder hchar (fun i => x i • B + y i • C) O } := by
  unfold certifiedProgrammedCachedRelationFinderExecutionProgram
    certifiedRelationFinderExecutionProgramWithBasis
  rw [CostedVestaComp.run_bind, costedAdaptiveStatementProgrammedBasisCache_run,
    CostedVestaComp.run_bind, certificate.certifiedCachedRunProgram_run_eq]
  simp [certifiedRelationFinderExecutionContinuation,
    cachedRelationFinderReductionProgramAtReifiedBasisFromCache,
    cachedRelationFinder, cachedRelationFinderWithCalls]

@[simp] theorem certifiedProgrammedCachedKnowledgeExtractorExecutionProgram_run
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
      hchar certificate B C x y O).run =
      { adversaryOutput := family.runOutput (fun i => x i • B + y i • C) O
        value := family.cachedKnowledgeExtractor hchar (fun i => x i • B + y i • C) O } := by
  unfold certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
    certifiedKnowledgeExtractorExecutionProgramWithBasis
  rw [CostedVestaComp.run_bind, costedAdaptiveStatementProgrammedBasisCache_run,
    CostedVestaComp.run_bind, certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedKnowledgeExtractorExecutionContinuation,
    CostedVestaComp.run_map]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache_eq
    hchar (fun i => x i • B + y i • C)
    { basis := fun i => x i • B + y i • C, basis_eq := rfl } O
    (certificate.certifiedCachedRun (fun i => x i • B + y i • C) O)
    (certificate.certifiedCachedRun_eq (fun i => x i • B + y i • C) O)]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis_run]
  simp

/-- Costed complete cached relation finder at one oracle table. -/
def costedCachedRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
  AdaptiveStatementCostedExecution family basis
      (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal
    (certificate.program basis) O
    (family.certifiedCachedRelationFinderExecutionProgram hchar certificate basis O)

/-- Costed complete cached witness extractor at one oracle table. -/
def costedCachedKnowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    AdaptiveStatementCostedExecution family basis
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal
    (certificate.program basis) O
    (family.certifiedCachedKnowledgeExtractorExecutionProgram hchar certificate basis O)

/-- Complete DLOG-programmed relation execution.  The private composition carries the exact
programmed-basis adversary call and the exact reified postprocessor, so total work is computed
from those two programs rather than joined by an external staging assertion. -/
def costedProgrammedCachedRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp)
    (O : family.Coins) :
    AdaptiveStatementCostedExecution family (fun i ↦ x i • B + y i • C)
      (Option (AlgebraicRelationWitness (F := Fp) (fun i ↦ x i • B + y i • C))) :=
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal
    (certificate.program (fun i ↦ x i • B + y i • C)) O
    (family.certifiedProgrammedCachedRelationFinderExecutionProgram
      hchar certificate B C x y O)

/-- Complete DLOG-programmed knowledge-extractor execution. -/
def costedProgrammedCachedKnowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp)
    (O : family.Coins) :
    AdaptiveStatementCostedExecution family (fun i ↦ x i • B + y i • C)
      (Option (ActionTerminal.ActionBundleWitness
        (family.runOutput (fun i ↦ x i • B + y i • C) O).inputs)) :=
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal
    (certificate.program (fun i ↦ x i • B + y i • C)) O
    (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
      hchar certificate B C x y O)

@[simp] theorem costedCachedRelationFinder_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).value =
      family.cachedRelationFinder hchar basis O := by
  change (family.certifiedCachedRelationFinderExecutionProgram
    hchar certificate basis O).run.value = _
  rw [family.certifiedCachedRelationFinderExecutionProgram_run]

@[simp] theorem costedCachedKnowledgeExtractor_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).value =
      family.cachedKnowledgeExtractor hchar basis O := by
  change (family.certifiedCachedKnowledgeExtractorExecutionProgram
    hchar certificate basis O).run.value = _
  rw [family.certifiedCachedKnowledgeExtractorExecutionProgram_run]

@[simp] theorem costedCachedRelationFinder_adversaryProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).adversaryProgram =
      certificate.program basis := rfl

@[simp] theorem costedCachedKnowledgeExtractor_adversaryProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).adversaryProgram =
      certificate.program basis := rfl

@[simp] theorem costedCachedRelationFinder_adversaryOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).adversaryOutput =
      family.runOutput basis O := by
  change (family.certifiedCachedRelationFinderExecutionProgram
    hchar certificate basis O).run.adversaryOutput = _
  rw [family.certifiedCachedRelationFinderExecutionProgram_run]

@[simp] theorem costedCachedKnowledgeExtractor_adversaryOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).adversaryOutput =
      family.runOutput basis O := by
  change (family.certifiedCachedKnowledgeExtractorExecutionProgram
    hchar certificate basis O).run.adversaryOutput = _
  rw [family.certifiedCachedKnowledgeExtractorExecutionProgram_run]

@[simp] theorem costedProgrammedCachedRelationFinder_adversaryOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.costedProgrammedCachedRelationFinder
      hchar certificate B C x y O).adversaryOutput =
      family.runOutput (fun i => x i • B + y i • C) O := by
  change (family.certifiedProgrammedCachedRelationFinderExecutionProgram
    hchar certificate B C x y O).run.adversaryOutput = _
  rw [family.certifiedProgrammedCachedRelationFinderExecutionProgram_run]

@[simp] theorem costedProgrammedCachedKnowledgeExtractor_adversaryOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.costedProgrammedCachedKnowledgeExtractor
      hchar certificate B C x y O).adversaryOutput =
      family.runOutput (fun i => x i • B + y i • C) O := by
  change (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
    hchar certificate B C x y O).run.adversaryOutput = _
  rw [family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram_run]

@[simp] theorem costedCachedRelationFinder_proverGroupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).proverGroupWork =
      certificate.proverGroupWork basis O := rfl

@[simp] theorem costedCachedKnowledgeExtractor_proverGroupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).proverGroupWork =
      certificate.proverGroupWork basis O := rfl

@[simp] theorem costedProgrammedCachedRelationFinder_value_isSome_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B : VestaG) (z : Fp) (x y) (O) :
    (family.costedProgrammedCachedRelationFinder hchar certificate B (z • B) x y O).value.isSome =
      (family.cachedRelationFinder hchar (scalarBasis B (programmedLogs z x y)) O).isSome := by
  change (family.certifiedProgrammedCachedRelationFinderExecutionProgram
    hchar certificate B (z • B) x y O).run.value.isSome = _
  rw [family.certifiedProgrammedCachedRelationFinderExecutionProgram_run]
  exact congrArg (fun selectedBasis =>
      (family.cachedRelationFinder hchar selectedBasis O).isSome)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

@[simp] theorem costedProgrammedCachedKnowledgeExtractor_value_isSome_scalarBasis
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B : VestaG) (z : Fp) (x y) (O) :
    (family.costedProgrammedCachedKnowledgeExtractor hchar certificate B (z • B) x y O).value.isSome =
      (family.cachedKnowledgeExtractor hchar
        (scalarBasis B (programmedLogs z x y)) O).isSome := by
  change (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
    hchar certificate B (z • B) x y O).run.value.isSome = _
  rw [family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram_run]
  exact congrArg (fun selectedBasis =>
      (family.cachedKnowledgeExtractor hchar selectedBasis O).isSome)
    (adaptiveStatementProgrammedBasis_eq_scalarBasis B z x y)

theorem certifiedCachedRelationFinderExecutionProgram_groupWork_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis) (O) :
    (family.certifiedCachedRelationFinderExecutionProgram
        hchar certificate basis O).groupWork =
      certificate.proverGroupWork basis O +
        (family.cachedRelationFinderReductionProgram hchar basis O).groupWork := by
  unfold certifiedCachedRelationFinderExecutionProgram
    certifiedRelationFinderExecutionProgramWithBasis
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork,
    costedAdaptiveStatementSelectedBasisCache_run,
    CostedVestaComp.groupWork_bind,
    certificate.certifiedCachedRunProgram_groupWork,
    certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedRelationFinderExecutionContinuation,
    CostedVestaComp.groupWork_map]
  rw [family.cachedRelationFinderReductionProgramAtReifiedBasisFromCache_eq
    hchar basis { basis := basis, basis_eq := rfl } O
    (certificate.certifiedCachedRun basis O)
    (certificate.certifiedCachedRun_eq basis O)]
  unfold cachedRelationFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork,
    costedAdaptiveStatementSelectedBasisCache_run]
  omega

theorem certifiedCachedKnowledgeExtractorExecutionProgram_groupWork_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis) (O) :
    (family.certifiedCachedKnowledgeExtractorExecutionProgram
        hchar certificate basis O).groupWork =
      certificate.proverGroupWork basis O +
        (family.cachedKnowledgeExtractorReductionProgram hchar basis O).groupWork := by
  unfold certifiedCachedKnowledgeExtractorExecutionProgram
    certifiedKnowledgeExtractorExecutionProgramWithBasis
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork,
    costedAdaptiveStatementSelectedBasisCache_run,
    CostedVestaComp.groupWork_bind,
    certificate.certifiedCachedRunProgram_groupWork,
    certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedKnowledgeExtractorExecutionContinuation,
    CostedVestaComp.groupWork_map]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache_eq
    hchar basis { basis := basis, basis_eq := rfl } O
    (certificate.certifiedCachedRun basis O)
    (certificate.certifiedCachedRun_eq basis O)]
  unfold cachedKnowledgeExtractorReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork,
    costedAdaptiveStatementSelectedBasisCache_run]
  omega

theorem certifiedProgrammedCachedRelationFinderExecutionProgram_groupWork_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.certifiedProgrammedCachedRelationFinderExecutionProgram
        hchar certificate B C x y O).groupWork =
      certificate.proverGroupWork (fun i => x i • B + y i • C) O +
        (family.programmedCachedRelationFinderReductionProgram hchar B C x y O).groupWork := by
  unfold certifiedProgrammedCachedRelationFinderExecutionProgram
    certifiedRelationFinderExecutionProgramWithBasis
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork,
    costedAdaptiveStatementProgrammedBasisCache_run,
    CostedVestaComp.groupWork_bind,
    certificate.certifiedCachedRunProgram_groupWork,
    certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedRelationFinderExecutionContinuation,
    CostedVestaComp.groupWork_map]
  rw [family.cachedRelationFinderReductionProgramAtReifiedBasisFromCache_eq hchar
    (fun i => x i • B + y i • C)
    { basis := fun i => x i • B + y i • C, basis_eq := rfl } O
    (certificate.certifiedCachedRun (fun i => x i • B + y i • C) O)
    (certificate.certifiedCachedRun_eq (fun i => x i • B + y i • C) O)]
  unfold programmedCachedRelationFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork,
    costedAdaptiveStatementProgrammedBasisCache_run]
  omega

theorem certifiedProgrammedCachedKnowledgeExtractorExecutionProgram_groupWork_eq
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
        hchar certificate B C x y O).groupWork =
      certificate.proverGroupWork (fun i => x i • B + y i • C) O +
        (family.programmedCachedKnowledgeExtractorReductionProgram hchar B C x y O).groupWork := by
  unfold certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
    certifiedKnowledgeExtractorExecutionProgramWithBasis
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork,
    costedAdaptiveStatementProgrammedBasisCache_run,
    CostedVestaComp.groupWork_bind,
    certificate.certifiedCachedRunProgram_groupWork,
    certificate.certifiedCachedRunProgram_run_eq]
  simp only [certifiedKnowledgeExtractorExecutionContinuation,
    CostedVestaComp.groupWork_map]
  rw [family.cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache_eq hchar
    (fun i => x i • B + y i • C)
    { basis := fun i => x i • B + y i • C, basis_eq := rfl } O
    (certificate.certifiedCachedRun (fun i => x i • B + y i • C) O)
    (certificate.certifiedCachedRun_eq (fun i => x i • B + y i • C) O)]
  unfold programmedCachedKnowledgeExtractorReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementProgrammedBasisCache_groupWork,
    costedAdaptiveStatementProgrammedBasisCache_run]
  omega

theorem cachedRelationFinderReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) (basis) (O) :
    (family.cachedRelationFinderReductionProgram hchar basis O).groupWork ≤
      adaptiveStatementFinderReductionGroupWork pp := by
  unfold cachedRelationFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork]
  have hprogram :=
    family.cachedRelationFinderReductionProgramAtReifiedBasis_groupWork_le hchar basis
      (costedAdaptiveStatementSelectedBasisCache pp basis).run O
  refine (Nat.add_le_add_left hprogram _).trans ?_
  simp only [adaptiveStatementFinderReductionGroupWork]
  omega

theorem cachedKnowledgeExtractorReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) (basis) (O) :
    (family.cachedKnowledgeExtractorReductionProgram hchar basis O).groupWork ≤
      adaptiveStatementReductionGroupWork pp := by
  unfold cachedKnowledgeExtractorReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementSelectedBasisCache_groupWork]
  have hprogram :=
    family.cachedKnowledgeExtractorReductionProgramAtReifiedBasis_groupWork_le hchar basis
      (costedAdaptiveStatementSelectedBasisCache pp basis).run O
  refine (Nat.add_le_add_left hprogram _).trans ?_
  simp only [adaptiveStatementReductionGroupWork,
    adaptiveStatementFinderReductionGroupWork]
  omega

theorem costedCachedRelationFinder_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  change (family.certifiedCachedRelationFinderExecutionProgram
    hchar certificate basis O).groupWork ≤ _
  rw [family.certifiedCachedRelationFinderExecutionProgram_groupWork_eq]
  exact Nat.add_le_add (certificate.proverGroupWork_le basis O)
    (family.cachedRelationFinderReductionProgram_groupWork_le hchar basis O |>.trans
      (adaptiveStatementFinderReductionGroupWork_le pp))

theorem costedCachedKnowledgeExtractor_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  change (family.certifiedCachedKnowledgeExtractorExecutionProgram
    hchar certificate basis O).groupWork ≤ _
  rw [family.certifiedCachedKnowledgeExtractorExecutionProgram_groupWork_eq]
  exact Nat.add_le_add (certificate.proverGroupWork_le basis O)
    (family.cachedKnowledgeExtractorReductionProgram_groupWork_le hchar basis O)

theorem costedProgrammedCachedRelationFinder_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.costedProgrammedCachedRelationFinder hchar certificate B C x y O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  change (family.certifiedProgrammedCachedRelationFinderExecutionProgram
    hchar certificate B C x y O).groupWork ≤ _
  rw [family.certifiedProgrammedCachedRelationFinderExecutionProgram_groupWork_eq]
  exact Nat.add_le_add (certificate.proverGroupWork_le _ O)
    ((family.programmedCachedRelationFinderReductionProgram_groupWork_le
      hchar B C x y O).trans (adaptiveStatementFinderReductionGroupWork_le pp))

theorem costedProgrammedCachedKnowledgeExtractor_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (B C : VestaG) (x y) (O) :
    (family.costedProgrammedCachedKnowledgeExtractor hchar certificate B C x y O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  change (family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
    hchar certificate B C x y O).groupWork ≤ _
  rw [family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram_groupWork_eq]
  exact Nat.add_le_add (certificate.proverGroupWork_le _ O)
    (family.programmedCachedKnowledgeExtractorReductionProgram_groupWork_le hchar B C x y O)

/-- One adversary execution plus one materialization of the canonical challenge vectors. -/
def adaptiveStatementCachedRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  family.Q + 11 + (AdaptiveActionStatementShape pp).k

/-- The cached query number is connected to the executable read set, rather than serving only as
an argument label on the advantage function. -/
theorem relationFinderReads_card_le_cachedRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementCachedRandomOracleQueries family := by
  simpa only [adaptiveStatementCachedRandomOracleQueries, Nat.add_assoc] using
    family.relationFinderReads_card_le basis O

/-- Cached group work is at most twice the adversary target whenever the complete structural
reduction program fits that same target. -/
theorem costedCachedKnowledgeExtractor_two_mul_bound {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (hreduction : adaptiveStatementReductionGroupWork pp ≤ workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      2 * workLimit := by
  refine (family.costedCachedKnowledgeExtractor_groupWork_le hchar certificate basis O).trans ?_
  omega

/-- External fidelity obligations for every complete execution used by the endpoint.  The syntax,
value flow, and numeric bounds are checked by Lean; these judgments state that group-valued work
inside generic host callbacks and pure continuations (for example verifier-key construction,
family hashing, and fixed-representation production) performs no additional Vesta group law
outside the reified nodes.  Lean has no operational semantics for those arbitrary functions, so
this is the irreducible shallow-embedding boundary. -/
def AdaptiveStatementExecutionStagingCoverage {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (workLimit : Nat)
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) : Prop :=
  (∀ basis O,
      (family.costedCachedRelationFinder hchar certificate basis O).program.StagedGroupWorkFaithful ∧
      (family.costedCachedKnowledgeExtractor
        hchar certificate basis O).program.StagedGroupWorkFaithful) ∧
    ∀ (C : VestaG)
      (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) O,
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B C x y O).program.StagedGroupWorkFaithful ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B C x y O).program.StagedGroupWorkFaithful

/-- DLOG advantage interface for the conditionally certified one-execution finder. Unlike the
legacy profile, there are no caller-selected prover or reduction group-work numbers: those come
from the staged adversary and complete reified reduction programs. Here “certified” does not mean
assumption-free: fidelity of both the supplied adversary program and the complete shallowly
embedded executions remains explicit. Exact reduction composition and direct-decode coverage are
derived outside this profile. -/
structure CertifiedAdaptiveStatementDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (workLimit : Nat)
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) where
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  finderAdvantageLE : TextbookDLWithCoinsAdvantageLE B (family.cachedRelationFinder hchar)
    (advantage (adaptiveStatementCachedRandomOracleQueries family)
      (workLimit + adaptiveStatementReductionGroupWork pp))
  executionStaging :
    AdaptiveStatementExecutionStagingCoverage family hchar B workLimit certificate

/-- The complete textbook-DLOG executions carry the exact adversary program and oracle path,
consume the programmed basis they compute, return the original reduction values, and fit the work
label used by the certified hardness premise.  The value and work conjuncts are proved from the
composition object; the two fidelity conjuncts are the explicit shallow-embedding boundary. -/
def AdaptiveStatementProgrammedReductionCoverage {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (workLimit : Nat)
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) : Prop :=
  ∀ (z : Fp) (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) O,
    (family.costedProgrammedCachedRelationFinder hchar certificate B (z • B) x y O).adversaryProgram =
        certificate.program (fun i ↦ x i • B + y i • (z • B)) ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).adversaryProgram =
        certificate.program (fun i ↦ x i • B + y i • (z • B)) ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).oracle = O ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).oracle = O ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).program =
        family.certifiedProgrammedCachedRelationFinderExecutionProgram
          hchar certificate B (z • B) x y O ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).program =
        family.certifiedProgrammedCachedKnowledgeExtractorExecutionProgram
          hchar certificate B (z • B) x y O ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).program.StagedGroupWorkFaithful ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).program.StagedGroupWorkFaithful ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).adversaryOutput =
        family.runOutput (fun i ↦ x i • B + y i • (z • B)) O ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).adversaryOutput =
        family.runOutput (fun i ↦ x i • B + y i • (z • B)) O ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).value.isSome =
        (family.cachedRelationFinder hchar (scalarBasis B (programmedLogs z x y)) O).isSome ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).value.isSome =
        (family.cachedKnowledgeExtractor hchar
          (scalarBasis B (programmedLogs z x y)) O).isSome ∧
      (family.costedProgrammedCachedRelationFinder
        hchar certificate B (z • B) x y O).groupWork ≤
        workLimit + adaptiveStatementReductionGroupWork pp ∧
      (family.costedProgrammedCachedKnowledgeExtractor
        hchar certificate B (z • B) x y O).groupWork ≤
        workLimit + adaptiveStatementReductionGroupWork pp

theorem CertifiedAdaptiveStatementDlogProfile.programmedReductionCoverage
    {pp : ProofParams} {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar}
    {B : VestaG} {workLimit : Nat}
    {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate) :
  AdaptiveStatementProgrammedReductionCoverage family hchar B workLimit certificate := by
  intro z x y O
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    (profile.executionStaging.2 (z • B) x y O).1,
    (profile.executionStaging.2 (z • B) x y O).2,
    family.costedProgrammedCachedRelationFinder_adversaryOutput
      hchar certificate B (z • B) x y O,
    family.costedProgrammedCachedKnowledgeExtractor_adversaryOutput
      hchar certificate B (z • B) x y O,
    family.costedProgrammedCachedRelationFinder_value_isSome_scalarBasis
      hchar certificate B z x y O,
    family.costedProgrammedCachedKnowledgeExtractor_value_isSome_scalarBasis
      hchar certificate B z x y O,
    family.costedProgrammedCachedRelationFinder_groupWork_le
      hchar certificate B (z • B) x y O,
    family.costedProgrammedCachedKnowledgeExtractor_groupWork_le
      hchar certificate B (z • B) x y O⟩

theorem CertifiedAdaptiveStatementDlogProfile.finderAdvantageLE_current {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate) :
    TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar)
      (profile.advantage (adaptiveStatementCachedRandomOracleQueries family)
        (workLimit + adaptiveStatementReductionGroupWork pp)) := by
  exact family.cachedRelationFinder_fun_eq hchar ▸ profile.finderAdvantageLE

theorem CertifiedAdaptiveStatementDlogProfile.queryCoverage {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (_profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate)
    (basis) (O) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementCachedRandomOracleQueries family :=
  family.relationFinderReads_card_le_cachedRandomOracleQueries basis O

theorem CertifiedAdaptiveStatementDlogProfile.extractorGroupWorkCoverage {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (_profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate)
    (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp :=
  family.costedCachedKnowledgeExtractor_groupWork_le hchar certificate basis O

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
