import Zcash.Snark.Soundness.FiatShamir.Adversary.Algebraic

/-!
# Online AGM data for rewind-free multiopen unbatching

An arbitrary aggregate `aMulti` could pick a fresh representation after seeing a later challenge.
This file refines `ComputedAlgebraicFSFamily` so the aggregate coordinates are the deterministic
MSM coordinates of the representation-carrying commitments actually assembled.  These are ghost
conditions on the AGM adversary; nothing is added to the transcript.  Chronology itself lives in
`DeployedPinnedRoots` as the squeeze-reprogramming invariance.
-/

namespace Zcash.Snark

open Classical

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

/-! ## The representation-carrying points available to multiopen -/

/-- All prover-emitted commitments fixed before `x1`, in deployed transcript order.  Scalar
evaluations are omitted: they are already visible in the ordinary transcript prefix and carry no
AGM representation. -/
def AlgebraicProofString.preX1Points (aps : AlgebraicProofString shape basis) :
    List (AlgebraicPoint (F := Fp) basis) :=
  (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
  [aps.vanishingRandom] ++ List.ofFn aps.hPieces

theorem AlgebraicProofString.preX1Points_length
    (aps : AlgebraicProofString shape basis) :
    aps.preX1Points.length =
      shape.numProofs * shape.numAdviceColumns +
      shape.numProofs * shape.numLookups +
      shape.numProofs * shape.numLookups +
      shape.numProofs * shape.numPermutationSets +
      shape.numProofs * shape.numLookups + 1 + shape.numQuotientPieces := by
  simp [AlgebraicProofString.preX1Points, Function.comp_def]
  omega

/-- The represented points available before the `x1` batching challenge.  `fixed` holds
verifier-known representations per public basis; `qPrime` is excluded — it is emitted only after
`x2`. -/
def AlgebraicProofString.preX1AssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  aps.preX1Points ++ fixed

theorem AlgebraicProofString.preX1AssemblySource_length
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    (aps.preX1AssemblySource fixed).length = aps.preX1Points.length + fixed.length := by
  simp [AlgebraicProofString.preX1AssemblySource]

/-- The represented points from which the final multiopen MSM may be assembled.  This extends the
strict pre-`x1` source by the later `qPrime` commitment. -/
def AlgebraicProofString.multiopenAssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  aps.preX1AssemblySource fixed ++ [aps.multiopenQPrime]

/-- Every represented quotient-piece commitment occurs in the strict pre-`x1` source. -/
theorem AlgebraicProofString.hPiece_mem_preX1AssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (i : Fin shape.numQuotientPieces) :
    aps.hPieces i ∈ aps.preX1AssemblySource fixed := by
  simp [AlgebraicProofString.preX1AssemblySource, AlgebraicProofString.preX1Points]

/-- Compatibility form for consumers of the complete multiopen assembly source. -/
theorem AlgebraicProofString.hPiece_mem_multiopenAssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (i : Fin shape.numQuotientPieces) :
    aps.hPieces i ∈ aps.multiopenAssemblySource fixed := by
  simp only [AlgebraicProofString.multiopenAssemblySource, List.mem_append]
  exact Or.inl (aps.hPiece_mem_preX1AssemblySource fixed i)

/-! ## Canonical aggregate coordinates -/

/-- Every non-URS point appended by the verifier's multiopen MSM is one of the represented points
that was available at the proper transcript prefix. -/
def MultiopenAssemblyCovered (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs -> Nat -> VestaG)
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop :=
  forall nu : Fin 11 -> Fp, forall pr,
    pr ∈ (multiopenMsm vk instanceCommitment aps.erase (chRecord nu (fun _ => 0))).other ->
      ∃ ap ∈ aps.multiopenAssemblySource fixed, ap.point = pr.2

/-- Construct the aggregate coordinates by looking up every appended MSM point in the fixed
representation source.  This removes the unconstrained choice of `aMulti`: its dependence on
`x1,...,x4` is exactly the verifier's public MSM scalar dependence. -/
def AlgebraicWfProof.ofOnlineMultiopenRepresented
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcover : MultiopenAssemblyCovered vk instanceCommitment aps fixed) :
    AlgebraicWfProof basis vk instanceCommitment :=
  AlgebraicWfProof.ofRepresented aps hwf fun nu =>
    RepresentedMultiopen.ofCoveredList vk instanceCommitment aps.erase nu
      (aps.multiopenAssemblySource fixed) (hcover nu)

/-- An `AlgebraicWfProof` uses canonical online multiopen coordinates.  The equalities mention
`ofCoveredList` deliberately: an existential representation is not enough for unbatching. -/
structure CanonicalOnlineMultiopenCoordinates
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop where
  covered : MultiopenAssemblyCovered vk instanceCommitment p.algebraicProof fixed
  aMulti_eq : forall nu,
    p.aMulti nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).gScalars +
        repsGPart
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  multiU_eq : forall nu,
    p.multiU nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).uScalar +
        repsU
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  multiBlind_eq : forall nu,
    p.multiBlind nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).wScalar +
        repsW
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  s_eq : p.s = p.algebraicProof.ipaS.gPart
  sU_eq : p.sU = p.algebraicProof.ipaS.coeffs AugmentedIndex.u
  sBlind_eq : p.sBlind = p.algebraicProof.ipaS.coeffs AugmentedIndex.w

/-- The smart constructor above satisfies the canonical-coordinate interface definitionally. -/
theorem AlgebraicWfProof.ofOnlineMultiopenRepresented_canonical
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcover : MultiopenAssemblyCovered vk instanceCommitment aps fixed) :
    CanonicalOnlineMultiopenCoordinates
      (AlgebraicWfProof.ofOnlineMultiopenRepresented aps hwf fixed hcover) fixed := by
  refine
    { covered := hcover
      aMulti_eq := ?_
      multiU_eq := ?_
      multiBlind_eq := ?_
      s_eq := rfl
      sU_eq := rfl
      sBlind_eq := rfl }
  · intro nu
    rfl
  · intro nu
    rfl
  · intro nu
    rfl

/-! ## Refined computed family -/

/-- A computed AGM family whose multiopen coordinates are canonical.  Exact deployed chronology
is added only at the root-family layer, where all data affecting each priced bad set is visible.
Extending, rather than modifying, `ComputedAlgebraicFSFamily` keeps all existing IPA/DLOG theorems
available through `toFamily`. -/
structure ComputedOnlineMultiopenFSFamily (shape : Shape)
    extends ComputedAlgebraicFSFamily shape where
  fixedRepresentations : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
    List (AlgebraicPoint (F := Fp) basis)
  canonical : forall basis O,
    CanonicalOnlineMultiopenCoordinates ((adversary basis).run O)
      (fixedRepresentations basis)

namespace ComputedOnlineMultiopenFSFamily

/-- Forget the canonical multiopen-coordinate evidence. -/
abbrev toFamily (family : ComputedOnlineMultiopenFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

end ComputedOnlineMultiopenFSFamily

end Zcash.Snark
