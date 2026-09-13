import Zcash.Snark.ZeroKnowledge.ActionGateDegree
import Zcash.Snark.ZeroKnowledge.ActionBoundaryProfile
import Zcash.Snark.ZeroKnowledge.VestaSimulation
import Zcash.Snark.ZeroKnowledge.ActionCommitments
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate

/-!
# Simulation with the actual Action compiler key

The verifying key is constructed by Action key generation. Its shape, query order,
domain, and permutation layout follow from `ActionDerivedKey` and the checked
fifteen-column compression certificate. This removes independent key-layout, sigma
naming, copy-query, and product-dimension premises from the Action reference bound.

The entire degree and masking profiles follow from the actual compiler and source
activation trace. Original row and copy equations remain the valid-witness premise;
nonidentity of the URS blinding point remains the public-parameter condition. These
theorems compare the complete typed reference view and its encoded attempt on
independent wide-reduced private and verifier tapes. The typed view also supports
observations of the full Fiat–Shamir transcript and recovered raw hash digests.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS omegaOf)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability

/-- Actual Action key generation supplies the reference's three public commitment families. -/
theorem actionReferenceKey_publicCommitmentsMatch {G : Type}
    [AddCommGroup G] [Module Fp G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) :
    PlonkPublicCommitmentsMatch urs
      (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionPublicPolynomials inputs) (actionCircuit.instanceCommitment urs inputs) := by
  let hpacked := actionCircuit_newFixedCols_eq_fifteen
  exact actionCompilerPublicCommitmentsMatch urs hk
    (actionCircuit_referenceShape actions urs.k hk hpacked)
    (actionReferenceKey_queryLayout (actions := actions) urs hk hpacked) inputs

/-- The complete Action verifier opening agrees with the reference using the compiler-derived key. -/
theorem actionReferenceKey_opening_eq_public {G : Type}
    [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions)
    (hpoints : Function.Injective (plonkQueryPoint (omegaOf 11) ch.x)) :
    let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
    let pub := actionPublicPolynomials inputs
    let actual := plonkVerifierOpening urs vk pub (actionCircuit.instanceCommitment urs inputs) ch view
    let reference := plonkPublicOpening urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
      (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
    (actual.1.eval urs, actual.2) = (reference.1.eval urs, reference.2) := by
  let hpacked := actionCircuit_newFixedCols_eq_fifteen
  exact actionCompilerOpening_eq_public urs hk
    (actionCircuit_referenceShape actions urs.k hk hpacked)
    (actionReferenceKey_queryLayout (actions := actions) urs hk hpacked) inputs ch view hpositive hpoints

/-- The concrete Action compiler simulates the full typed view, before applying an attempt observer. -/
theorem wideActionCompilerTypedReference_simulation_error_bound {actions : ℕ} [Fintype VestaG]
    (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : PlonkOriginalRowsValid
      (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionPublicPolynomials inputs) witness)
    (hW : urs.w ≠ 0) :
    let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
    let pub := actionPublicPolynomials inputs
    let copies := plonkKeygenCopies actionCircuit actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) vk.permutationChunks
      (actionReferenceKey_copyChunkWidths (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE
        (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
          (plonkTotalColumnConstructor vk pub witness) [] vk pub)
        (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
        (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
          (plonkTotalColumnConstructor vk pub witness) [] vk pub) (plonkSimulationErrorBound actions) := by
  let hpacked := actionCircuit_newFixedCols_eq_fifteen
  intro vk pub copies hvalues
  have hdomain := actionReferenceKey_domain (actions := actions) urs hk hpacked
  have hnaming := actionReferenceKey_sigmaNaming (actions := actions) urs hk hpacked
  have hshape := actionReferenceKey_productShape (actions := actions) urs hk hpacked
  have hcopy := plonkKeygenCopyWitness_of_values vk actionCircuit actionCircuit_permutationColumnCount_eq
    (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide))
    (actionReferenceKey_copyChunkWidths (actions := actions) urs hk hpacked)
    (actionReferenceKey_copySigmaIndices (actions := actions) urs hk hpacked) hnaming.1 hnaming.2
    (actionReferenceKey_copyQueries (actions := actions) urs hk hpacked) (actionInstanceRows inputs) witness hvalues
  obtain ⟨hinstance, hfixed, hsigma⟩ := plonkPublicPolynomialsFromRows_degree
    (actionInstanceRows inputs) (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  have h := wideOriginalValidPlonkVerifier_simulation_error_bound urs hk vk pub witness
    (actionReferenceKey_degreeProfile (actions := actions) urs hk hpacked)
    (actionReferenceKey_maskingProfile urs hk hpacked inputs) hvalid copies hcopy
    hdomain.1 hdomain.2 (actionReferenceKey_queryLayout (actions := actions) urs hk hpacked).blinding
    hshape.1 hshape.2 hinstance hfixed hsigma (vestaBlinding_bijective urs.w hW)
  exact h

/-- The concrete Action compiler instantiates encoded simulation for valid original rows and copies. -/
theorem wideActionCompilerReference_simulation_error_bound {actions : ℕ} [Fintype VestaG]
    (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : PlonkOriginalRowsValid
      (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionPublicPolynomials inputs) witness)
    (hW : urs.w ≠ 0) :
    let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
    let pub := actionPublicPolynomials inputs
    let copies := plonkKeygenCopies actionCircuit actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) vk.permutationChunks
      (actionReferenceKey_copyChunkWidths (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE (freshEncodedPlonkReferenceAttempt urs hk vk pub witness)
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (freshEncodedPlonkReferenceAttempt urs hk vk pub witness) (plonkSimulationErrorBound actions) := by
  intro vk pub copies hvalues
  have h := wideActionCompilerTypedReference_simulation_error_bound urs hk inputs witness hvalid hW hvalues
  rw [freshEncodedPlonkReferenceAttempt_law]
  exact ⟨eventBias_map h.1 encodedPlonkAttempt, eventBias_map h.2 encodedPlonkAttempt⟩

end Zcash.Snark.ZeroKnowledge
