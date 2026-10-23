import Zcash.Snark.Fixtures.MultiAction.Honest.StaticChecks
import Zcash.Snark.Soundness.Composition.ZeroStraightLine

/-!
# Captured-data straight-line interface test, with eleven live IPA rounds

This interface fixture runs the zero prover against captured scalar/layout data at `k = 11`.
Commitments remain zero because sampled AGM bases need not represent captured points.
-/
namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The captured shape with its sub-proofs removed: same domain `k = 11`, same column, point-set
and query arities, no instances. -/
def capturedZeroShape : Shape := { shape with numProofs := 0 }

/-- The captured verifying key's scalar and layout data at the instance-free shape, with zero
group commitment families. -/
def capturedZeroVk : VerifyingKey capturedZeroShape Fp VestaG where
  omega := vk.omega
  n := vk.n
  blindingFactors := vk.blindingFactors
  delta := vk.delta
  chunkLen := vk.chunkLen
  gates := vk.gates
  instanceQueryLayout := vk.instanceQueryLayout
  adviceQueryLayout := vk.adviceQueryLayout
  fixedQueryLayout := vk.fixedQueryLayout
  fixedCommitment := fun _ => 0
  permutationCommonCommitment := fun _ => 0
  permutationChunks := vk.permutationChunks
  lookupInputExprs := vk.lookupInputExprs
  lookupTableExprs := vk.lookupTableExprs

/-- The instance-free key's fixed-column commitments vanish. -/
theorem capturedZeroVk_fixed : ∀ i, capturedZeroVk.fixedCommitment i = 0 := fun _ => rfl

/-- The instance-free key's common permutation commitments vanish. -/
theorem capturedZeroVk_perm : ∀ i, capturedZeroVk.permutationCommonCommitment i = 0 := fun _ => rfl

/-- The instantiating shape has no sub-proofs. -/
theorem capturedZeroShape_numProofs : capturedZeroShape.numProofs = 0 := rfl

/-- The instantiating shape keeps the captured domain: eleven IPA rounds. -/
theorem capturedZeroShape_k : capturedZeroShape.k = 11 := rfl

/-- The instantiating shape keeps the captured point-set and query arities. -/
theorem capturedZeroShape_arities :
    capturedZeroShape.numPointSets = shape.numPointSets ∧
      capturedZeroShape.numAdviceQueries = shape.numAdviceQueries ∧
      capturedZeroShape.numFixedQueries = shape.numFixedQueries ∧
      capturedZeroShape.numInstanceQueries = shape.numInstanceQueries ∧
      capturedZeroShape.numQuotientPieces = shape.numQuotientPieces :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The instantiating key keeps the captured scalar and layout data. -/
theorem capturedZeroVk_data :
    capturedZeroVk.omega = vk.omega ∧ capturedZeroVk.n = vk.n ∧
      capturedZeroVk.gates = vk.gates ∧
      capturedZeroVk.instanceQueryLayout = vk.instanceQueryLayout ∧
      capturedZeroVk.adviceQueryLayout = vk.adviceQueryLayout ∧
      capturedZeroVk.fixedQueryLayout = vk.fixedQueryLayout ∧
      capturedZeroVk.permutationChunks = vk.permutationChunks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The captured key's straight-line deployed family.**  Six staged root events, an empty
constraint-`x` stage, and a staged IPA trace over the captured domain's eleven rounds. -/
def capturedZeroStraightLineFamily :
    ComputedStraightLineDeployedFSFamily capturedZeroShape :=
  zeroStraightLineDeployedFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl

/-- The captured key's deployed constraint family, one interface below. -/
def capturedZeroDeployedConstraintFamily :
    ComputedDeployedConstraintFSFamily capturedZeroShape :=
  zeroDeployedConstraintFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl

/-- The captured key's deployed root family, two interfaces below. -/
def capturedZeroDeployedRootFamily :
    ComputedDeployedRootFSFamily capturedZeroShape :=
  zeroDeployedRootFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm

/-- The instance-free key preserves the captured scalar and layout profile. -/
theorem capturedZeroVk_profile : CapturedVerifierKeyProfile capturedZeroVk := by
  constructor <;> rfl

instance capturedZeroVkFieldSupport : VerifyingKey.FieldSupport capturedZeroVk :=
  capturedZeroVk_profile.fieldSupport

instance capturedZeroVkWellFormed : VerifyingKey.WellFormed capturedZeroVk :=
  capturedZeroVk_profile.wellFormed

/-- **The constraint-`x` squeeze schedule at budget zero.**  The stage's root set is empty on
every table, so the event costs nothing and its pinning is the staged trace's. -/
def capturedZeroConstraintSchedule :
    DeployedConstraintXSqueezeSchedule capturedZeroStraightLineFamily.toRootFamily 0 where
  measure_le := fun basis O => by
    rw [show deployedConstraintXBadSet capturedZeroStraightLineFamily.toRootFamily basis O = ∅ from
      zeroConstraintXBadSet_empty capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl
        basis O]
    simp
  pinned := capturedZeroStraightLineFamily.pinnedX

/-! ## The full family at the full captured shape

The total constraint-`x` event lets the zero prover exercise every stage with both sub-proofs live.
This remains a fixture-local interface test, pinned by the fixture census.
-/

/-- The captured key at the full captured shape — `numProofs = 2` live — with zero group
commitment families. -/
def capturedLiveZeroVk : VerifyingKey shape Fp VestaG where
  omega := vk.omega
  n := vk.n
  blindingFactors := vk.blindingFactors
  delta := vk.delta
  chunkLen := vk.chunkLen
  gates := vk.gates
  instanceQueryLayout := vk.instanceQueryLayout
  adviceQueryLayout := vk.adviceQueryLayout
  fixedQueryLayout := vk.fixedQueryLayout
  fixedCommitment := fun _ => 0
  permutationCommonCommitment := fun _ => 0
  permutationChunks := vk.permutationChunks
  lookupInputExprs := vk.lookupInputExprs
  lookupTableExprs := vk.lookupTableExprs

/-- The live key's fixed-column commitments vanish. -/
theorem capturedLiveZeroVk_fixed : ∀ i, capturedLiveZeroVk.fixedCommitment i = 0 := fun _ => rfl

/-- The live key's common permutation commitments vanish. -/
theorem capturedLiveZeroVk_perm :
    ∀ i, capturedLiveZeroVk.permutationCommonCommitment i = 0 := fun _ => rfl

/-- **The deployed root family at the full captured shape**: six staged root events with both
sub-proofs live. -/
def capturedLiveZeroRootFamily : ComputedDeployedRootFSFamily shape :=
  zeroDeployedRootFamily capturedLiveZeroVk capturedLiveZeroVk_fixed capturedLiveZeroVk_perm

/-- **The staged IPA trace at the full captured shape**: the constant walk over the captured
domain's eleven rounds, with the multiopen value free. -/
def capturedLiveZeroIpaTrace :
    StraightLineIpaOnlineTrace capturedLiveZeroRootFamily.toFamily :=
  zeroConstStraightLineIpaTrace capturedLiveZeroVk capturedLiveZeroVk_fixed
    capturedLiveZeroVk_perm

/-- **The full straight-line family with both sub-proofs live**: every interface
obligation discharged at the captured key's scalar data over `numProofs = 2`, `k = 11`.  Smoke
test only. -/
def capturedLiveZeroStraightLineFamily :
    ComputedStraightLineDeployedFSFamily shape :=
  zeroConstStraightLineDeployedFamily capturedLiveZeroVk capturedLiveZeroVk_fixed
    capturedLiveZeroVk_perm

/-- The live key preserves the captured scalar and layout profile. -/
theorem capturedLiveZeroVk_profile : CapturedVerifierKeyProfile capturedLiveZeroVk := by
  constructor <;> rfl

instance capturedLiveZeroVkFieldSupport : VerifyingKey.FieldSupport capturedLiveZeroVk :=
  capturedLiveZeroVk_profile.fieldSupport

instance capturedLiveZeroVkWellFormed : VerifyingKey.WellFormed capturedLiveZeroVk :=
  capturedLiveZeroVk_profile.wellFormed

/-- **The straight-line interface is inhabited at the full captured shape** — the non-vacuity
smoke test of the total pre-`x` constraint event. -/
theorem straightLineInterface_nonempty_at_captured_shape :
    Nonempty (ComputedStraightLineDeployedFSFamily shape) :=
  ⟨capturedLiveZeroStraightLineFamily⟩

end Zcash.Snark.Fixture2
