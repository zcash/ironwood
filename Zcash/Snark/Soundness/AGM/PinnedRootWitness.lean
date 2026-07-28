import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots

/-!
# The strict-prefix root premise is satisfiable

This module exhibits a `DeployedRootOnlineTrace`. A constant-output family over a degenerate shape,
with a constant batch witness, has five empty deployed root sets; the sixth, at `x₃`, is computed
from strict earlier-prefix answers alone. The probability layer's reprogramming equality then
follows from the trace's fresh-query property.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero Msm.eval Msm.appendTerm Msm.scale Msm.add)

open scoped ENNReal

local instance vestaInhabitedPinnedRootWitness : Inhabited VestaG := ⟨0⟩

/-- The degenerate shape of the witness family: no proofs, no queries, a one-element basis. -/
def witnessShape : Shape :=
  { k := 0, numProofs := 0, numAdviceColumns := 0, numLookups := 0, numPermutationSets := 0,
    numPermutationColumns := 0, numQuotientPieces := 0, numInstanceQueries := 0,
    numAdviceQueries := 0, numFixedQueries := 0, numPointSets := 0 }

/-- The zero verifying key at the witness shape. -/
def witnessVk : VerifyingKey witnessShape Fp VestaG :=
  { omega := 0, n := 0, blindingFactors := 0, delta := 0, chunkLen := 0, gates := [],
    instanceQueryLayout := [], adviceQueryLayout := [], fixedQueryLayout := [],
    fixedCommitment := fun _ => 0, permutationCommonCommitment := fun _ => 0,
    permutationChunks := [], lookupInputExprs := fun _ => [],
    lookupTableExprs := fun _ => [] }

/-- The zero instance commitments at the witness shape. -/
def witnessIc : Fin witnessShape.numProofs → ℕ → VestaG := fun _ _ => 0

/-- The zero proof string at the witness shape. -/
def witnessPs : ProofString witnessShape Fp VestaG :=
  { adviceCommitments := fun _ _ => 0, lookupPermutedInput := fun _ _ => 0,
    lookupPermutedTable := fun _ _ => 0, permutationProduct := fun _ _ => 0,
    lookupProduct := fun _ _ => 0, vanishingRandom := 0, hPieces := fun _ => 0,
    instanceEvals := fun _ _ => 0, adviceEvals := fun _ _ => 0,
    fixedEvals := fun _ => 0, vanishingRandomEval := 0,
    permutationCommonEvals := fun _ => 0,
    permutationSetEvals := fun _ _ => ⟨0, 0, none⟩,
    lookupEvals := fun _ _ => ⟨0, 0, 0, 0, 0⟩, multiopenQPrime := 0,
    multiopenU := fun _ => 0, ipaS := 0, ipaRounds := fun _ => (0, 0),
    ipaC := 0, ipaF := 0 }

/-- **The keystone evaluation**: the assembled multiopen commitment of the zero data is the zero
point, for every basis and every challenge record. Only the two vanishing queries survive the
degenerate shape, and both carry the zero commitment and zero evaluation. -/
theorem multiopenCommitment_witness_zero
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) (ν : Fin 11 → Fp) :
    multiopenCommitment (ursOfAugmentedBasis witnessShape.k basis).g
      (ursOfAugmentedBasis witnessShape.k basis).w (ursOfAugmentedBasis witnessShape.k basis).u
      witnessVk witnessIc witnessPs (chRecord ν (fun _ => 0)) = 0 := by
  simp [multiopenCommitment, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, openedPair, assembleOpening, compressSet, Msm.eval, Msm.zero,
    accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx]

/-- The zero algebraic point over any basis. -/
def witnessPoint (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    AlgebraicPoint (F := Fp) basis :=
  ⟨0, ⟨0, by simp [representationEval]⟩⟩

/-- The zero algebraic proof string: every group element is the zero point with the zero
representation. -/
def witnessAps (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    AlgebraicProofString witnessShape basis :=
  { adviceCommitments := fun _ _ => witnessPoint basis,
    lookupPermutedInput := fun _ _ => witnessPoint basis,
    lookupPermutedTable := fun _ _ => witnessPoint basis,
    permutationProduct := fun _ _ => witnessPoint basis,
    lookupProduct := fun _ _ => witnessPoint basis,
    vanishingRandom := witnessPoint basis, hPieces := fun _ => witnessPoint basis,
    instanceEvals := fun _ _ => 0, adviceEvals := fun _ _ => 0,
    fixedEvals := fun _ => 0, vanishingRandomEval := 0,
    permutationCommonEvals := fun _ => 0,
    permutationSetEvals := fun _ _ => ⟨0, 0, none⟩,
    lookupEvals := fun _ _ => ⟨0, 0, 0, 0, 0⟩,
    multiopenQPrime := witnessPoint basis,
    multiopenU := fun _ => 0, ipaS := witnessPoint basis,
    ipaRounds := fun _ => (witnessPoint basis, witnessPoint basis),
    ipaC := 0, ipaF := 0 }

/-- Erasing the zero algebraic proof string gives the zero proof string. -/
theorem witnessAps_erase (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessAps basis).erase = witnessPs := rfl

/-- The zero well-formed algebraic proof: the aggregate coordinates are zero, matched by the
keystone evaluation. -/
def witnessProof (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    AlgebraicWfProof basis witnessVk witnessIc :=
  { algebraicProof := witnessAps basis
    wellFormed := fun p => p.elim0
    aMulti := fun _ _ => 0
    multiU := fun _ => 0
    multiBlind := fun _ => 0
    multiopen_repr := fun ν => by
      rw [witnessAps_erase]
      simpa [commit, Finset.sum_const_zero] using
        (multiopenCommitment_witness_zero basis ν).symm
    s := fun _ => 0
    sU := 0
    sBlind := 0
    ipaS_repr := by
      simp [commit, witnessAps, witnessPoint] }

/-- The constant-output witness family: the adversary ignores the oracle and returns the zero
proof. -/
def witnessFamily : ComputedAlgebraicFSFamily witnessShape :=
  { init := []
    vk := fun _ => witnessVk
    instanceCommitment := fun _ => witnessIc
    adversary := fun basis => .pure (witnessProof basis)
    Q := 0
    queryBound := fun _ => .pure _ 0 }

/-! ## The zero batch

Every deployed root set is built from the batch's coordinate columns. At the witness data the
`x₄` pair list is empty, so the single batch column is the prover's `q′` — the zero point — and
the all-zero coordinates satisfy the power-batch equations.
-/

/-- The witness data emits no multiopen `u` values, so the `x₄` pair count is zero. -/
theorem deployedX4PairCount_witness (ν : Fin 11 → Fp) :
    deployedX4PairCount witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0)) = 0 := by
  simp [deployedX4PairCount, deployedX4Pairs, witnessPs, witnessShape]

/-- The witness proof string's `q′` is the zero point. -/
theorem witnessPs_multiopenQPrime : witnessPs.multiopenQPrime = 0 := rfl

/-! ## Canonical coordinates

The witness proof's aggregate coordinates are the zero functions, and the assembly they must
match is zero too: the assembled MSM contributes no generator or `u` scalar, and its only
appended term carries the zero point, whose looked-up representation has zero coefficients.
-/

/-- The assembled MSM contributes no generator scalars at the witness data. -/
theorem multiopenMsm_witness_gScalars (ν : Fin 11 → Fp) :
    (multiopenMsm witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0))).gScalars = fun _ => 0 := by
  simp [multiopenMsm, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, assembleOpening, compressSet, Msm.zero,
    accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx]

/-- The assembled MSM contributes no `u` scalar at the witness data. -/
theorem multiopenMsm_witness_uScalar (ν : Fin 11 → Fp) :
    (multiopenMsm witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0))).uScalar = 0 := by
  simp [multiopenMsm, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, assembleOpening, compressSet, Msm.zero,
    accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx]

/-- **Every appended assembly point is covered.** The assembly appends only the `q′` term, whose
point is zero — and the zero point is in the proof's own assembly source. -/
theorem multiopenAssemblyCovered_witness
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    MultiopenAssemblyCovered witnessVk witnessIc (witnessAps basis) [] := by
  intro nu pr hpr
  refine ⟨witnessPoint basis, ?_, ?_⟩
  · simp [AlgebraicProofString.multiopenAssemblySource, witnessAps]
  · have h2 : pr.2 = 0 := by
      revert hpr
      simp [multiopenMsm, assembleQueries, witnessVk, witnessShape, witnessIc,
        vanishingQueries, columnQueries, permutationCommonQueries,
        vanishingHCommitment, constructIntermediateSets, assembleOpening, compressSet, Msm.zero,
        accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
        Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx]
      rintro rfl
      rfl
    simp [witnessPoint, h2]

/-- The assembled MSM contributes no `w` scalar at the witness data. -/
theorem multiopenMsm_witness_wScalar (ν : Fin 11 → Fp) :
    (multiopenMsm witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0))).wScalar = 0 := by
  simp [multiopenMsm, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, assembleOpening, compressSet, Msm.zero,
    accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx]

/-- A represented term list whose points all have zero coefficients contributes no generator
part. -/
theorem repsGPart_eq_zero {basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG}
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis))
    (h : ∀ t ∈ reps, t.2.coeffs = fun _ => 0) : repsGPart reps = 0 := by
  funext i
  simp only [repsGPart, Pi.zero_apply]
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [h t ht]; simp

/-- The same list contributes no `U` part. -/
theorem repsU_eq_zero {basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG}
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis))
    (h : ∀ t ∈ reps, t.2.coeffs = fun _ => 0) : repsU reps = 0 := by
  simp only [repsU]
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [h t ht]; simp

/-- The same list contributes no `W` part. -/
theorem repsW_eq_zero {basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG}
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis))
    (h : ∀ t ∈ reps, t.2.coeffs = fun _ => 0) : repsW reps = 0 := by
  simp only [repsW]
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [h t ht]; simp

/-- The witness assembly source is the zero point twice: the emitted vanishing randomness and
the `q′` commitment. -/
theorem witnessAps_multiopenAssemblySource
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessAps basis).multiopenAssemblySource []
      = [witnessPoint basis, witnessPoint basis] := rfl

/-- Every point of the witness assembly source has zero coefficients. -/
theorem witnessAps_source_coeffs (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    ∀ ap ∈ (witnessAps basis).multiopenAssemblySource [], ap.coeffs = fun _ => 0 := by
  intro ap hap
  rw [witnessAps_multiopenAssemblySource] at hap
  rcases List.mem_cons.mp hap with rfl | hap2
  · rfl
  · rcases List.mem_cons.mp hap2 with rfl | hap3
    · rfl
    · simp at hap3

/-- Every represented term of the witness assembly is a looked-up source point, so it carries
zero coefficients. -/
theorem witnessReps_coeffs (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (ν : Fin 11 → Fp) :
    ∀ t ∈ (RepresentedMultiopen.ofCoveredList witnessVk witnessIc
      witnessPs ν ((witnessAps basis).multiopenAssemblySource [])
      (multiopenAssemblyCovered_witness basis ν)).reps, t.2.coeffs = fun _ => 0 := by
  intro t ht
  simp only [RepresentedMultiopen.ofCoveredList] at ht
  obtain ⟨pr, hpr, rfl⟩ := List.mem_pmap.mp ht
  exact witnessAps_source_coeffs basis _ (List.mem_of_find?_eq_some (Option.some_get _).symm)

/-- The witness proof declares zero aggregate coordinates. -/
theorem witnessProof_aMulti (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessProof basis).aMulti = fun _ _ => 0 := rfl

/-- The witness proof declares a zero `U` coordinate. -/
theorem witnessProof_multiU (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessProof basis).multiU = fun _ => 0 := rfl

/-- The witness proof declares a zero blinding coordinate. -/
theorem witnessProof_multiBlind (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessProof basis).multiBlind = fun _ => 0 := rfl

/-- The witness proof's algebraic proof string is the zero one. -/
theorem witnessProof_algebraicProof (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessProof basis).algebraicProof = witnessAps basis := rfl

/-- The witness proof's underlying proof string is the zero proof string. -/
theorem witnessProof_proof_fst (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    (witnessProof basis).proof.1 = witnessPs := rfl

/-- **The witness proof uses canonical online multiopen coordinates.** Both sides are zero: the
proof declares zero aggregates, and the assembly contributes no scalars and only zero-coefficient
represented terms. -/
theorem witnessProof_canonical (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    CanonicalOnlineMultiopenCoordinates (witnessProof basis) [] where
  covered := multiopenAssemblyCovered_witness basis
  aMulti_eq := fun ν => by
    simp only [witnessProof_proof_fst, witnessProof_algebraicProof, witnessProof_aMulti,
      multiopenMsm_witness_gScalars ν, repsGPart_eq_zero _ (witnessReps_coeffs basis ν)]
    simp
  multiU_eq := fun ν => by
    simp only [witnessProof_proof_fst, witnessProof_algebraicProof, witnessProof_multiU,
      multiopenMsm_witness_uScalar ν, repsU_eq_zero _ (witnessReps_coeffs basis ν)]
    simp
  multiBlind_eq := fun ν => by
    simp only [witnessProof_proof_fst, witnessProof_algebraicProof, witnessProof_multiBlind,
      multiopenMsm_witness_wScalar ν, repsW_eq_zero _ (witnessReps_coeffs basis ν)]
    simp
  s_eq := rfl
  sU_eq := rfl
  sBlind_eq := rfl

/-- A count known to vanish admits no index: the vacuity every per-member field discharges. -/
theorem absurd_lt_of_eq_zero {n i : ℕ} (h : n = 0) (hi : i < n) : False := by omega

/-! ## The witness batch data -/

/-- The witness family's verifying key. -/
theorem witnessFamily_vk (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    witnessFamily.vk basis = witnessVk := rfl

/-- The witness family's instance commitments. -/
theorem witnessFamily_instanceCommitment
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    witnessFamily.instanceCommitment basis = witnessIc := rfl

/-- The witness family's run always erases to the zero proof string. -/
theorem witnessFamily_run_erase (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ((witnessFamily.adversary basis).run O).algebraicProof.erase = witnessPs := rfl

/-- The wrapped run of the witness family returns the zero proof. -/
theorem witnessFamily_wrapped_run (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ((wrappedAdversary witnessFamily basis).run O).1 = witnessProof basis := by
  rw [wrappedAdversary_run_fst]
  rfl

/-- The `x₄` pair count vanishes at the witness family's wrapped run. Stated at the run itself
so the per-member vacuity fields, whose index hypothesis depends on this very count, can consume
it without a dependent rewrite. -/
theorem witnessFamily_pairCount_at_run
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    deployedX4PairCount (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
      ((wrappedAdversary witnessFamily basis).run O).1.proof.1
      (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)) = 0 := by
  rw [witnessFamily_wrapped_run]
  exact deployedX4PairCount_witness _


/-- **An all-zero power batch exists whenever every column commitment vanishes.** The zero
coordinates commit to the zero point, and every power sum of zeros is zero. -/
def zeroPowerBatch {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) {n : ℕ} (cols : Fin n → G) (hcols : ∀ i, cols i = 0) (challenge : Fp) :
    AlgebraicPowerBatch urs cols (fun _ => 0) 0 0 challenge where
  coeffs := fun _ _ => 0
  uComp := fun _ => 0
  wComp := fun _ => 0
  commitment := by
    intro i
    rw [hcols i]
    simp [commit]
  reconstruct := by funext j; simp
  reconstructU := by simp
  reconstructW := by simp

/-- With no `x₄` pairs, the batch's only column is the prover's `q′`: the zero point. -/
theorem x4BatchCommitments_witness (ν : Fin 11 → Fp)
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (i : Fin (deployedX4PairCount witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0)) + 1)) :
    x4BatchCommitments (ursOfAugmentedBasis witnessShape.k basis) rfl witnessVk witnessIc
      witnessPs (chRecord (k := witnessShape.k) ν (fun _ => 0)) i = 0 := by
  have hi : ¬ ((i : ℕ) < deployedX4PairCount witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0))) := by
    have h0 := deployedX4PairCount_witness ν
    omega
  simp only [x4BatchCommitments, if_neg hi, witnessPs_multiopenQPrime]

/-- The witness `x₄` power batch: all coordinates zero. -/
def witnessX4Batch (ν : Fin 11 → Fp)
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) :
    AlgebraicPowerBatch (ursOfAugmentedBasis witnessShape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis witnessShape.k basis) rfl witnessVk witnessIc
        witnessPs (chRecord (k := witnessShape.k) ν (fun _ => 0)))
      (fun _ => 0) 0 0 (chRecord (k := witnessShape.k) ν (fun _ => 0)).x4 :=
  zeroPowerBatch _ _ (x4BatchCommitments_witness ν basis) _

/-- The all-zero power batch against aggregates given by hypothesis rather than syntactically.
Taking the aggregates as equations keeps the use site rewrite-free, so the constructed batch's
coordinates stay definitionally zero. -/
def zeroPowerBatchOf {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) {n : ℕ} (cols : Fin n → G) (hcols : ∀ i, cols i = 0)
    (agg : Fin (2 ^ urs.k) → Fp) (aggU aggW : Fp)
    (hagg : agg = fun _ => 0) (haggU : aggU = 0) (haggW : aggW = 0) (challenge : Fp) :
    AlgebraicPowerBatch urs cols agg aggU aggW challenge where
  coeffs := fun _ _ => 0
  uComp := fun _ => 0
  wComp := fun _ => 0
  commitment := by
    intro i
    rw [hcols i]
    simp [commit]
  reconstruct := by
    subst hagg
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero]
  reconstructU := by subst haggU; simp
  reconstructW := by subst haggW; simp

/-- All-zero deployed batches with the aggregates supplied as equations. -/
def zeroDeployedBatchesOf {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (agg : Fin (2 ^ urs.k) → Fp) (aggU aggW : Fp)
    (hagg : agg = fun _ => 0) (haggU : aggU = 0) (haggW : aggW = 0)
    (hcount : deployedX4PairCount vk instanceCommitment ps ch = 0)
    (hcols : ∀ i, x4BatchCommitments urs hk vk instanceCommitment ps ch i = 0) :
    DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch agg aggU aggW where
  x4 := zeroPowerBatchOf urs _ hcols agg aggU aggW hagg haggU haggW ch.x4
  x1 := fun i hi => absurd hi (by omega)

/-- **All-zero deployed batches whenever the pair count vanishes and every `x₄` column
commitment is zero.** With no pairs the per-member family is vacuous, so only the `x₄` batch
carries data — and that is the all-zero power batch. Stating it over variables keeps the pair
count an opaque atom, which is what lets the vacuity discharge by `omega`. -/
def zeroDeployedBatches {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount vk instanceCommitment ps ch = 0)
    (hcols : ∀ i, x4BatchCommitments urs hk vk instanceCommitment ps ch i = 0) :
    DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch (fun _ => 0) 0 0 where
  x4 := zeroPowerBatch urs _ hcols ch.x4
  x1 := fun i hi => absurd hi (by omega)


/-- The wrapped run's aggregate coordinates are zero. -/
theorem witnessFamily_run_aMulti (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ((wrappedAdversary witnessFamily basis).run O).1.aMulti
        (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O)) = fun _ => 0 := by
  rw [witnessFamily_wrapped_run]; rfl

/-- The wrapped run's `U` coordinate is zero. -/
theorem witnessFamily_run_multiU (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ((wrappedAdversary witnessFamily basis).run O).1.multiU
        (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O)) = 0 := by
  rw [witnessFamily_wrapped_run]; rfl

/-- The wrapped run's blinding coordinate is zero. -/
theorem witnessFamily_run_multiBlind (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ((wrappedAdversary witnessFamily basis).run O).1.multiBlind
        (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O)) = 0 := by
  rw [witnessFamily_wrapped_run]; rfl

/-- Every `x₄` batch column at the wrapped run is the zero point. -/
theorem x4BatchCommitments_witness_at_run
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) (i) :
    x4BatchCommitments (ursOfAugmentedBasis witnessShape.k basis) rfl
      (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
      ((wrappedAdversary witnessFamily basis).run O).1.proof.1
      (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)) i = 0 := by
  revert i
  rw [witnessFamily_wrapped_run]
  exact x4BatchCommitments_witness _ basis

/-- **The witness family's batch witness.** Everything is zero or vacuous: the canonical
coordinates are the proved ones, the batches are the all-zero deployed batches, and every
per-member field is empty because the `x₄` pair count vanishes. -/
def witnessBatchWitness
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    DeployedBatchWitness witnessFamily basis
      ((wrappedAdversary witnessFamily basis).run O) where
  fixedRepresentations := []
  canonical := by
    rw [wrappedAdversary_run_fst]
    exact witnessProof_canonical basis
  membersCovered := by
    rw [witnessFamily_wrapped_run]
    intro nu i hi
    exact absurd (absurd_lt_of_eq_zero (deployedX4PairCount_witness nu) hi) not_false
  batches :=
    zeroDeployedBatchesOf _ rfl _ _ _ _ _ _ _
      (witnessFamily_run_aMulti basis O) (witnessFamily_run_multiU basis O)
      (witnessFamily_run_multiBlind basis O)
      (witnessFamily_pairCount_at_run basis O)
      (x4BatchCommitments_witness_at_run basis O)
  memberCoeffs := fun i hi =>
    absurd (absurd_lt_of_eq_zero (witnessFamily_pairCount_at_run basis O) hi) not_false
  memberU := fun i hi =>
    absurd (absurd_lt_of_eq_zero (witnessFamily_pairCount_at_run basis O) hi) not_false
  memberW := fun i hi =>
    absurd (absurd_lt_of_eq_zero (witnessFamily_pairCount_at_run basis O) hi) not_false

/-- The witness family's outcome provider: always the batch branch, never a relation. -/
def witnessOutcome : DeployedRootOutcomeProvider witnessFamily :=
  fun basis O => PSum.inl (witnessBatchWitness basis O)

/-! ## Reprogramming moves exactly one read

The witness adversary ignores the oracle, so its eleven squeeze points are fixed. Their prefix
lengths are pairwise distinct, hence so are the points — and reprogramming the answer at one of
them leaves every other read untouched. This is the causal fact the invariance premise needs.
-/

/-- The witness family's adversary is constant. -/
theorem witnessFamily_run (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (X : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    (witnessFamily.adversary basis).run X = witnessProof basis := rfl

/-- **The eleven squeeze points are pairwise distinct.** Their prefix lengths are
`1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15` — all different, so no two points coincide. -/
theorem witnessProof_prefixesPre_injective
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) {i j : Fin 11} (hij : i ≠ j) :
    algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) i
      ≠ algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) j := by
  intro hEq
  have hli := preIpaSqueezePoints_length_eq witnessFamily.init
    (witnessProof basis).proof.1 (witnessProof basis).proof.2 i
  have hlj := preIpaSqueezePoints_length_eq witnessFamily.init
    (witnessProof basis).proof.1 (witnessProof basis).proof.2 j
  have : preIpaLen witnessShape witnessFamily.init.length i
      = preIpaLen witnessShape witnessFamily.init.length j := by
    rw [← hli, ← hlj]
    exact congrArg (fun t : BTranscript Fp VestaG _ => t.val.length) hEq
  revert this
  fin_cases i <;> fin_cases j <;> simp_all [preIpaLen, witnessShape, witnessFamily]

/-- **Reprogramming at one squeeze point moves only that read.** The proof is constant, so the
points do not shift, and the points are pairwise distinct — so the other ten answers survive. -/
theorem witnessFamily_reads_update
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp)
    (i : Fin 11) (v : Fp) :
    wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run
        (Function.update O (algebraicFullPrefixesPre witnessFamily.init
          (witnessProof basis) i) v))
      = Function.update (wrappedPreIpaReads
          ((wrappedAdversary witnessFamily basis).run O)) i v := by
  funext j
  rw [wrappedPreIpaReads_run, wrappedPreIpaReads_run]
  by_cases hj : j = i
  · subst hj
    simp [runReads, runProof, witnessFamily_run, Function.update_apply]
    intro h
    exact absurd rfl h
  · have hne := witnessProof_prefixesPre_injective basis hj
    simp [runReads, runProof, witnessFamily_run, Function.update_apply, hj]
    intro h
    exact absurd h hne

/-! ## The witness evaluations vanish -/

/-- The multiopen value of the zero data is zero, at every challenge record. -/
theorem multiopenValue_witness_zero (ch : Challenges witnessShape.k Fp) :
    multiopenValue witnessVk witnessIc witnessPs ch = 0 := by
  simp [multiopenValue, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, openedPair, assembleOpening, compressSet, Msm.zero,
    accumulateCommitment, List.ofFn_zero, multiopenCombine, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx,
    multiopenEval]

/-- The recomputed base evaluation of the zero data is zero, at every challenge record. -/
theorem deployedBaseEval_witness_zero (ch : Challenges witnessShape.k Fp) :
    deployedBaseEval witnessVk witnessIc witnessPs ch = 0 := by
  simp [deployedBaseEval, assembleQueries, witnessVk, witnessPs, witnessShape, witnessIc,
    vanishingQueries, columnQueries, permutationCommonQueries, vanishingHCommitment,
    constructIntermediateSets, compressSet, Msm.zero,
    accumulateCommitment, List.ofFn_zero, Msm.appendTerm, Msm.scale,
    Msm.add, expectedHEval, allExpressions, subProofExpressions, List.findIdx,
    multiopenEval]

/-! ## Every deployed root set collapses

With no `x₄` pairs the per-set index type is empty, so every polynomial folded over it is zero, and
the zero coordinates flatten the two IPA shift polynomials too. Only the `x₃` set keeps content: the
point set `deployedAllPts`, read off the `x` squeeze and so fixed before the `x₃` answer prices it.
-/

/-- The per-set index type is empty at the witness data. -/
theorem isEmpty_fin_pairCount_witness (ν : Fin 11 → Fp) :
    IsEmpty (Fin (deployedX4PairCount witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0)))) := by
  rw [deployedX4PairCount_witness]
  infer_instance

section RootSetCollapse

variable {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
variable (urs : URS G) (hk : witnessShape.k = urs.k)
  (vk : VerifyingKey witnessShape Fp G) (ic : Fin witnessShape.numProofs → ℕ → G)
  (ps : ProofString witnessShape Fp G) (ch : Challenges witnessShape.k Fp)

/-- **The `x₁` member-separation set is empty at the witness shape**, which has no point sets.
Stated over arbitrary data: only the shape matters. -/
theorem deployedX1AllRootSet_witnessShape
    {agg : Fin (2 ^ urs.k) → Fp} {aggU aggW : Fp}
    (b : DeployedAlgebraicBatches urs hk vk ic ps ch agg aggU aggW) :
    deployedX1AllRootSet urs hk vk ic ps ch b = ∅ := by
  ext x
  simp [deployedX1AllRootSet, witnessShape]

/-- **The `x₂` node-binding set is empty when the pair count vanishes**: its polynomial folds
over an empty index type. -/
theorem deployedX2RootSet_of_pairCount_zero
    {agg : Fin (2 ^ urs.k) → Fp} {aggU aggW : Fp}
    (b : DeployedAlgebraicBatches urs hk vk ic ps ch agg aggU aggW)
    (hcount : deployedX4PairCount vk ic ps ch = 0) :
    deployedX2RootSet urs hk vk ic ps ch b = ∅ := by
  haveI : IsEmpty (Fin (deployedX4PairCount vk ic ps ch)) := by
    rw [hcount]; infer_instance
  ext x
  simp only [deployedX2RootSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨node, -, hx⟩
  rw [show nodeBindingErrorPolynomial (deployedAllPts vk ic ps ch)
      (deployedAlgebraicSetPoints vk ic ps ch)
      (deployedAlgebraicSetColumns urs hk vk ic ps ch b.x4)
      (deployedAlgebraicSetInterpolants vk ic ps ch) node = 0 from by
      simp [nodeBindingErrorPolynomial, powerErrorPolynomial, Finset.univ_eq_empty]] at hx
  simp [szBadSet] at hx

/-- **The `x₄` value-batch set is empty** when its coordinates and evaluations both vanish. -/
theorem deployedX4RootSet_of_zero
    {agg : Fin (2 ^ urs.k) → Fp} {aggU aggW : Fp}
    (b : DeployedAlgebraicBatches urs hk vk ic ps ch agg aggU aggW)
    (hc : b.x4.coeffs = fun _ _ => 0) (hev : x4BatchEvals vk ic ps ch = fun _ => 0) :
    deployedX4RootSet urs hk vk ic ps ch b = ∅ := by
  ext x
  simp [deployedX4RootSet, algebraicBatchErrorPolynomial, hc, hev, commitGen, szBadSet]

/-- **The `x₃` set is exactly the deployed point set** when the coordinates vanish: the
cleared-quotient polynomial contributes nothing, leaving `deployedAllPts` — which is read off the
`x` squeeze and so is fixed before the `x₃` answer it is priced against. -/
theorem deployedX3RootSet_of_zero
    {agg : Fin (2 ^ urs.k) → Fp} {aggU aggW : Fp}
    (b : DeployedAlgebraicBatches urs hk vk ic ps ch agg aggU aggW)
    (hc : b.x4.coeffs = fun _ _ => 0)
    (hcount : deployedX4PairCount vk ic ps ch = 0) :
    deployedX3RootSet urs hk vk ic ps ch b = ↑(deployedAllPts vk ic ps ch) := by
  haveI : IsEmpty (Fin (deployedX4PairCount vk ic ps ch)) := by
    rw [hcount]; infer_instance
  rw [deployedX3RootSet,
    show deployedX3ErrorPolynomial urs hk vk ic ps ch b.x4 = 0 from by
      simp [deployedX3ErrorPolynomial, clearedQuotientErrorPolynomial,
        deployedAlgebraicQPrime, hc, coeffsToPoly, Finset.univ_eq_empty]]
  simp [szBadSet]

end RootSetCollapse

section DegenerateRootSets

variable {basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG}

/-- The `ξ` shift polynomial vanishes: every coordinate it is built from is zero. -/
theorem ipaShiftXiPolynomial_witness (ν : Fin 11 → Fp) :
    ipaShiftXiPolynomial
      (commitGen (evalVector witnessShape.k ((chRecord (k := witnessShape.k) ν (fun _ => 0)).x3))
          ((witnessProof basis).aMulti ν) -
        multiopenValue witnessVk witnessIc witnessPs (chRecord ν (fun _ => 0)))
      (commitGen (evalVector witnessShape.k ((chRecord (k := witnessShape.k) ν (fun _ => 0)).x3))
        (witnessProof basis).s) = 0 := by
  rw [multiopenValue_witness_zero]
  simp [ipaShiftXiPolynomial, witnessProof, commitGen]

/-- The `z` shift polynomial vanishes for the same reason. -/
theorem ipaShiftZPolynomial_witness (ν : Fin 11 → Fp) :
    ipaShiftZPolynomial
      (commitGen (evalVector witnessShape.k ((chRecord (k := witnessShape.k) ν (fun _ => 0)).x3))
          ((witnessProof basis).aMulti ν) -
        multiopenValue witnessVk witnessIc witnessPs (chRecord ν (fun _ => 0)))
      ((witnessProof basis).multiU ν) (witnessProof basis).sU
      (commitGen (evalVector witnessShape.k ((chRecord (k := witnessShape.k) ν (fun _ => 0)).x3))
        (witnessProof basis).s)
      ((chRecord (k := witnessShape.k) ν (fun _ => 0)).xi) = 0 := by
  rw [multiopenValue_witness_zero]
  simp [ipaShiftZPolynomial, witnessProof, commitGen]

/-- With no pairs, every `x₄` batch evaluation is the base evaluation — which vanishes. -/
theorem x4BatchEvals_witness (ν : Fin 11 → Fp) :
    x4BatchEvals witnessVk witnessIc witnessPs (chRecord (k := witnessShape.k) ν (fun _ => 0))
      = fun _ => 0 := by
  funext j
  have hi : ¬ ((j : ℕ) < deployedX4PairCount witnessVk witnessIc witnessPs
      (chRecord (k := witnessShape.k) ν (fun _ => 0))) := by
    have h0 := deployedX4PairCount_witness ν
    omega
  simp only [x4BatchEvals, if_neg hi]
  exact deployedBaseEval_witness_zero _

/-- The `x₄` batch evaluations vanish at the wrapped run. -/
theorem x4BatchEvals_witness_at_run
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    x4BatchEvals (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
      ((wrappedAdversary witnessFamily basis).run O).1.proof.1
      (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)) = fun _ => 0 := by
  rw [witnessFamily_wrapped_run]
  exact x4BatchEvals_witness _

/-- The `ξ` shift polynomial vanishes at the wrapped run. -/
theorem ipaShiftXiPolynomial_witness_at_run
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ipaShiftXiPolynomial
      (commitGen (evalVector witnessShape.k
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)).x3)
          (((wrappedAdversary witnessFamily basis).run O).1.aMulti
            (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O))) -
        multiopenValue (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
          ((wrappedAdversary witnessFamily basis).run O).1.proof.1
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)))
      (commitGen (evalVector witnessShape.k
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)).x3)
        ((wrappedAdversary witnessFamily basis).run O).1.s) = 0 := by
  rw [witnessFamily_wrapped_run]
  exact ipaShiftXiPolynomial_witness _

/-- The `z` shift polynomial vanishes at the wrapped run. -/
theorem ipaShiftZPolynomial_witness_at_run
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    ipaShiftZPolynomial
      (commitGen (evalVector witnessShape.k
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)).x3)
          (((wrappedAdversary witnessFamily basis).run O).1.aMulti
            (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O))) -
        multiopenValue (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
          ((wrappedAdversary witnessFamily basis).run O).1.proof.1
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)))
      (((wrappedAdversary witnessFamily basis).run O).1.multiU
        (wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O)))
      ((wrappedAdversary witnessFamily basis).run O).1.sU
      (commitGen (evalVector witnessShape.k
          (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)).x3)
        ((wrappedAdversary witnessFamily basis).run O).1.s)
      (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)).xi = 0 := by
  rw [witnessFamily_wrapped_run]
  exact ipaShiftZPolynomial_witness _

/-! ## Blindness of the assembly to the later squeezes

The deployed query assembly reads the challenge record only through `θ, β, γ, y, x`, the answers
absorbed before the multiopen squeezes. Replacing a later field therefore leaves the assembly, and
hence the point sets, definitionally unchanged — the causal content the `x₃` event needs.
-/

/-- The query assembly never reads `x₃`. -/
theorem assembleQueries_x3_blind {G : Type*} [Field Fp] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (v : Fp) :
    assembleQueries vk ic ps {ch with x3 := v} = assembleQueries vk ic ps ch := rfl

/-- Hence the deployed point sets never read `x₃`. -/
theorem deployedAllPts_x3_blind {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (v : Fp) :
    deployedAllPts vk ic ps {ch with x3 := v} = deployedAllPts vk ic ps ch := rfl

/-- The deployed point sets depend on a challenge record only through the fields used before the
multiopen squeezes. -/
theorem deployedAllPts_congr_preMultiopen
    {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch ch' : Challenges shape.k Fp)
    (htheta : ch.theta = ch'.theta) (hbeta : ch.beta = ch'.beta)
    (hgamma : ch.gamma = ch'.gamma) (hy : ch.y = ch'.y) (hx : ch.x = ch'.x) :
    deployedAllPts vk ic ps ch = deployedAllPts vk ic ps ch' := by
  rcases ch with ⟨theta, beta, gamma, y, x, x1, x2, x3, x4, xi, z, rounds⟩
  rcases ch' with
    ⟨theta', beta', gamma', y', x', x1', x2', x3', x4', xi', z', rounds'⟩
  simp only at htheta hbeta hgamma hy hx
  subst theta'; subst beta'; subst gamma'; subst y'; subst x'
  rfl

/-- Reprogramming the `x₃` read is exactly a record update of the `x₃` field. -/
theorem chRecord_update_seven (ν : Fin 11 → Fp) (v : Fp) :
    chRecord (k := witnessShape.k) (Function.update ν 7 v) (fun _ => 0)
      = {chRecord (k := witnessShape.k) ν (fun _ => 0) with x3 := v} := by
  simp [chRecord]

/-! ## Strict-prefix causality and its invariance corollary -/

/-- **Every deployed root set at the witness family, evaluated.** Five of the six are empty; the
`x₃` event's set is exactly the deployed point set, which the assembly reads off the `x` squeeze
alone. -/
theorem deployedRootBad_witness (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp)
    (i : Fin 6) :
    deployedRootBad witnessFamily witnessOutcome basis
        ((wrappedAdversary witnessFamily basis).run O) O i
      = if i.val = 3 then
          ↑(deployedAllPts (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
            ((wrappedAdversary witnessFamily basis).run O).1.proof.1
            (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)))
        else ∅ := by
  fin_cases i <;> simp only [deployedRootBad, witnessOutcome]
  · rw [ipaShiftXiPolynomial_witness_at_run]; simp [szBadSet]
  · rw [ipaShiftZPolynomial_witness_at_run]; simp [szBadSet]
  · simpa using deployedX4RootSet_of_zero _ rfl _ _ _ _ _ rfl
      (x4BatchEvals_witness_at_run basis O)
  · simpa using deployedX3RootSet_of_zero _ rfl _ _ _ _ _ rfl
      (witnessFamily_pairCount_at_run basis O)
  · simpa using deployedX2RootSet_of_pairCount_zero _ rfl _ _ _ _ _
      (witnessFamily_pairCount_at_run basis O)
  · simpa using deployedX1AllRootSet_witnessShape _ rfl _ _ _ _ _

end DegenerateRootSets

/-! ## An executable causal trace

The only nonempty root set is the `x₃` event, and its point-set data uses exactly the five
pre-multiopen challenges `θ`, `β`, `γ`, `y`, and `x`. The stage below reads those five squeeze
points and computes the set directly, so no classical truth-table enumeration is needed to turn
prefix determination into a program.
-/

/-- The five squeeze points whose answers determine the witness family's `x₃` root set. -/
def witnessPreMultiopenPoint
    (b : AugmentedIndex (2 ^ witnessShape.k) → VestaG) (j : Fin 5) :
    BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) :=
  algebraicFullPrefixesPre witnessFamily.init (witnessProof b) ⟨j, by omega⟩

/-- Rebuild the challenge record prefix consumed by `deployedAllPts`. -/
def witnessPreMultiopenRecord (answers : Fin 5 → Fp) : Challenges witnessShape.k Fp :=
  { theta := answers 0
    beta := answers 1
    gamma := answers 2
    y := answers 3
    x := answers 4
    x1 := 0
    x2 := 0
    x3 := 0
    x4 := 0
    xi := 0
    z := 0
    ipaRound := fun _ => 0 }

/-- The executable pre-`x₃` root-set computation for the witness family. -/
def witnessRootStage
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) (i : Fin 6) :
    OracleComp
      (BTranscript Fp VestaG
        (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k))
      Fp (Set Fp) :=
  if i.val = 3 then
    (OracleComp.readFin (F := Fp) (witnessPreMultiopenPoint basis)).bind fun answers =>
      .pure (↑(deployedAllPts witnessVk witnessIc witnessPs
        (witnessPreMultiopenRecord answers)) : Set Fp)
  else
    .pure ∅

/-- Reading one of the stage's five points returns the corresponding wrapped-run challenge. -/
theorem witnessPreMultiopenPoint_read
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp)
    (j : Fin 5) :
    O (witnessPreMultiopenPoint basis j) =
      wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O) ⟨j, by omega⟩ := by
  rw [wrappedPreIpaReads_run]
  rfl

/-- The five stage reads compute the same deployed point set as the wrapped run. -/
theorem witnessPreMultiopenAllPts
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    deployedAllPts witnessVk witnessIc witnessPs
        (witnessPreMultiopenRecord (fun j => O (witnessPreMultiopenPoint basis j))) =
      deployedAllPts witnessVk witnessIc witnessPs
        (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)) :=
  deployedAllPts_congr_preMultiopen witnessVk witnessIc witnessPs _ _
    (witnessPreMultiopenPoint_read basis O 0)
    (witnessPreMultiopenPoint_read basis O 1)
    (witnessPreMultiopenPoint_read basis O 2)
    (witnessPreMultiopenPoint_read basis O 3)
    (witnessPreMultiopenPoint_read basis O 4)

/-- The five queried answers reproduce the final run's pre-multiopen challenge prefix. -/
theorem witnessRootStage_agrees
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    (witnessRootStage basis i).run O =
      deployedRootBad witnessFamily witnessOutcome basis
        ((wrappedAdversary witnessFamily basis).run O) O i := by
  rw [deployedRootBad_witness]
  by_cases h3 : i.val = 3
  · rw [witnessRootStage, if_pos h3, OracleComp.run_bind, OracleComp.run_readFin,
      OracleComp.run_pure, if_pos h3]
    rw [witnessPreMultiopenAllPts]
    rw [witnessFamily_wrapped_run]
    change (↑(deployedAllPts witnessVk witnessIc witnessPs _) : Set Fp) =
      ↑(deployedAllPts witnessVk witnessIc (witnessAps basis).erase _)
    rw [witnessAps_erase]
  · rw [witnessRootStage, if_neg h3, OracleComp.run_pure, if_neg h3]

/-- The `x₃` squeeze point is not among the five points queried by `witnessRootStage`. -/
theorem witnessRootStage_fresh
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG) (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp) :
    deployedRootPoint witnessFamily ((wrappedAdversary witnessFamily basis).run O) i ∉
      (witnessRootStage basis i).queries O := by
  by_cases h3 : i.val = 3
  · have hi : i = 3 := Fin.ext h3
    subst i
    change deployedRootPoint witnessFamily
        ((wrappedAdversary witnessFamily basis).run O) (3 : Fin 6) ∉
      List.ofFn (witnessPreMultiopenPoint basis)
    intro hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
    have hpoint : deployedRootPoint witnessFamily
        ((wrappedAdversary witnessFamily basis).run O) (3 : Fin 6) =
        algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) 7 := by
      unfold deployedRootPoint
      rw [witnessFamily_wrapped_run]
      rfl
    rw [hpoint] at hj
    fin_cases j <;> exact witnessProof_prefixesPre_injective basis (by decide) hj
  · rw [witnessRootStage, if_neg h3]
    exact List.not_mem_nil

/-- A fully executable staged root trace for the degenerate witness family. -/
def witnessRootTrace : DeployedRootOnlineTrace witnessFamily witnessOutcome where
  stage := witnessRootStage
  agrees := witnessRootStage_agrees
  fresh := witnessRootStage_fresh

/-- The update point of event `i` is the squeeze point at its challenge index. -/
theorem deployedRootPoint_witness (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp)
    (i : Fin 6) :
    deployedRootPoint witnessFamily ((wrappedAdversary witnessFamily basis).run O) i
      = algebraicFullPrefixesPre witnessFamily.init (witnessProof basis)
          (deployedRootChallengeIndex i) := by
  unfold deployedRootPoint
  rw [witnessFamily_wrapped_run]
  exact rfl

/-- Reprogramming the `x₃` answer leaves the deployed point set alone: the reads move only at
index `7`, which is exactly an `x₃` record update, and the assembly never reads `x₃`. -/
theorem deployedAllPts_witness_update
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessFamily.init.length 10 + 3 * witnessShape.k) → Fp)
    (v : Fp) :
    deployedAllPts (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
        ((wrappedAdversary witnessFamily basis).run (Function.update O
          (algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) 7) v)).1.proof.1
        (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run (Function.update O
          (algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) 7) v)))
      = deployedAllPts (witnessFamily.vk basis) (witnessFamily.instanceCommitment basis)
        ((wrappedAdversary witnessFamily basis).run O).1.proof.1
        (wrappedPreIpaRecord ((wrappedAdversary witnessFamily basis).run O)) := by
  rw [witnessFamily_wrapped_run, witnessFamily_wrapped_run]
  show deployedAllPts _ _ _ (chRecord (wrappedPreIpaReads
      ((wrappedAdversary witnessFamily basis).run (Function.update O
        (algebraicFullPrefixesPre witnessFamily.init (witnessProof basis) 7) v)))
      (fun _ => 0)) = _
  rw [witnessFamily_reads_update basis O 7 v, chRecord_update_seven]
  exact deployedAllPts_x3_blind _ _ _ _ v

/-- **The deployed strict-prefix root premise is satisfiable.** The witness adversary is constant.
At the sole nonempty event (`x₃`), all challenge fields consumed by the point-set assembly are
read at prefixes strictly shorter than the `x₃` prefix. -/
theorem deployedRootPrefixDetermined_witness :
    DeployedRootPrefixDetermined witnessFamily witnessOutcome := by
  intro basis i O O' hagree
  by_cases h3 : i.val = 3
  · have hi : i = 3 := Fin.ext h3
    subst i
    rw [deployedRootBad_witness, deployedRootBad_witness]
    have hread (j : Fin 11)
        (hlen : preIpaLen witnessShape 0 j < preIpaLen witnessShape 0 7) :
        wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O) j =
          wrappedPreIpaReads ((wrappedAdversary witnessFamily basis).run O') j := by
      rw [wrappedPreIpaReads_run, wrappedPreIpaReads_run]
      apply hagree
      change (preIpaSqueezePoints witnessFamily.init
          (runProof witnessFamily basis O).proof.1 j).length < _
      rw [preIpaSqueezePoints_length_eq witnessFamily.init _
        (runProof witnessFamily basis O).proof.2 j]
      simpa only [show witnessFamily.init.length = 0 by rfl] using hlen
    rw [witnessFamily_wrapped_run, witnessFamily_wrapped_run]
    refine congrArg (fun s : Finset Fp => (↑s : Set Fp)) ?_
    apply deployedAllPts_congr_preMultiopen
    · simpa only [wrappedPreIpaRecord, chRecord] using
        hread 0 (by decide)
    · simpa only [wrappedPreIpaRecord, chRecord] using
        hread 1 (by decide)
    · simpa only [wrappedPreIpaRecord, chRecord] using
        hread 2 (by decide)
    · simpa only [wrappedPreIpaRecord, chRecord] using
        hread 3 (by decide)
    · simpa only [wrappedPreIpaRecord, chRecord] using
        hread 4 (by decide)
  · rw [deployedRootBad_witness, deployedRootBad_witness]
    simp only [if_neg h3]

/-- The witness family with its online multiopen and member-coverage evidence packaged. -/
def witnessOnlineMemberFamily :
    ComputedOnlineMemberFSFamily witnessShape where
  toComputedOnlineMultiopenFSFamily :=
    { toComputedAlgebraicFSFamily := witnessFamily
      fixedRepresentations := fun _ => []
      canonical := by
        intro basis O
        rw [witnessFamily_run]
        exact witnessProof_canonical basis }
  membersCovered := by
    intro basis O
    rw [witnessFamily_run]
    intro nu i hi
    exact absurd (absurd_lt_of_eq_zero (deployedX4PairCount_witness nu) hi) not_false

/-- **An inhabitant of the actual deployed-root family interface.** This packages the zero online
family, its concrete batch outcome, and the executable five-query root trace above; satisfiability
is therefore proved for the strong constructor premise, not merely for its weaker invariance
consequence. -/
def witnessDeployedRootFamily :
    ComputedDeployedRootFSFamily witnessShape where
  toComputedOnlineMemberFSFamily := witnessOnlineMemberFamily
  outcome := witnessOutcome
  rootTrace := witnessRootTrace

/-- The weaker self-reprogramming equation follows from the strict-prefix witness above. -/
theorem deployedRootSqueezeInvariance_witness :
    DeployedRootSqueezeInvariance witnessFamily witnessOutcome :=
  deployedRootSqueezeInvariance_of_prefixDetermined _ _
    deployedRootPrefixDetermined_witness

end Zcash.Snark
