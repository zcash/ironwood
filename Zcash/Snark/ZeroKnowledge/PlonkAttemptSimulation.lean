import Zcash.Snark.ZeroKnowledge.PlonkAttempt
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSimulation

/-!
# Joint simulation of a complete encoded attempt

The compiler-derived reference prover and its public simulator are observed through
the same message schedule and codecs. The observation retains emitted bytes, received
challenges, the complete verifier tape, and the attempt's status. Post-processing the
joint proof law therefore retains the numerical bound, including failed attempts.

This result is unconditioned. `PlonkCompilerSuccess` supplies the successful-view
comparison with the normalization cost. The whole-prover retry policy and the
remaining concrete circuit/key and protocol-construction conditions are unchanged.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf scalarFieldOrder URS)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The compiler-derived joint bound also covers every encoded prefix and attempt outcome. -/
theorem wideObservedCompilerKeygenPlonk_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (htopPrefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hpermutation : top.permutationColumnCount = 15)
    (hused : Halo2.usedRows top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (hindices : plonkCopySigmaIndices vk.permutationChunks)
    (hdelta : vk.delta = deltaFp) (hstride : vk.chunkLen = 7)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (instances : Fin actions → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (hmask : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true)
    (hvalid : PlonkOriginalRowsValid vk
      (plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)) witness)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hW : Function.Bijective (fun r : Fp => r • urs.w))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE
      ((freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub).map
          (plonkAttemptObservation pointCodec scalarCodec))
      ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map
        (plonkAttemptObservation pointCodec scalarCodec))
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
    PMFEventBiasLE
      ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map
        (plonkAttemptObservation pointCodec scalarCodec))
      ((freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub).map
          (plonkAttemptObservation pointCodec scalarCodec))
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  intro pub copies hvalues
  have h := wideCompilerKeygenPlonkVerifier_simulation_error_bound urs hk vk top
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked hW hvalues
  exact ⟨eventBias_map h.1 (plonkAttemptObservation pointCodec scalarCodec),
    eventBias_map h.2 (plonkAttemptObservation pointCodec scalarCodec)⟩

end Zcash.Snark.ZeroKnowledge
