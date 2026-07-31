import Zcash.Snark.Soundness.Composition.StraightLineConstraint

/-!
# The algebraic decode behind the straight-line constraint event

The Action terminal projects the exact `DeployedAlgebraicDecode` retained by the executable
constraint outcome. Callers identify run artifacts with circuit artifacts.
-/

namespace Zcash.Snark

open Classical

local instance vestaInhabitedStraightLineDecodeSupply : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- Re-round a decode.  No decode field reads the record's IPA rounds, so a decode at one round
vector is a decode at any other; every field transports by `rfl`.  Deployed acceptance is *not*
round-blind — the final IPA equation reads `ch.ipaRound` — which is why the root layer's
zero-round record and an accepting run's true record need this bridge at all. -/
def DeployedAlgebraicDecode.reRound {G : Type*} [AddCommGroup G] [Module Fp G]
    [Inhabited G]
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {ic : Fin shape.numProofs → Nat → G} {ps : ProofString shape Fp G}
    {nu : Fin 11 → Fp} {r₁ : Fin shape.k → Fp}
    {a : Fin (2 ^ urs.k) → Fp} {aU aW : Fp}
    (d : DeployedAlgebraicDecode urs hk vk ic ps (chRecord nu r₁) a aU aW)
    (r₂ : Fin shape.k → Fp) :
    DeployedAlgebraicDecode urs hk vk ic ps (chRecord nu r₂) a aU aW where
  batches := ⟨d.batches.x4, d.batches.x1⟩
  x4Values := d.x4Values
  memberValues := d.memberValues

/-- The one-run wrapped output: the straight-line event's run at `basis` and the oracle table `O`.
It is computed directly; the proof-only dummy recursive tape is not on this data path. -/
abbrev straightLineRunOutput
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :=
  deployedRootRunOutput family.toRootFamily basis O

/-- The exact computed constraint witness retained by a successful straight-line adapter. -/
def straightLineConstraintWitness
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  ((family.straightLineConstraintSuccess? static basis O).get h).witness

/-- The run's own algebraic decode exists whenever the computed constraint adapter succeeds. -/
theorem straightLineConstraintDecoded_nonempty_decode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    Nonempty (DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      (straightLineRunOutput family basis O).1.proof.1
      (wrappedPreIpaRecord (straightLineRunOutput family basis O))
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))) :=
  ⟨(straightLineConstraintWitness family static basis O h).decode⟩

/-- The decode projected from the computed straight-line constraint witness. -/
def straightLineDecode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  (straightLineConstraintWitness family static basis O h).decode

/-- The run's complete challenge record: the squeezed pre-IPA reads and the true IPA rounds.
The root layer's `wrappedPreIpaRecord` zeroes the rounds; acceptance holds at this record. -/
abbrev straightLineRunRecord
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads (straightLineRunOutput family basis O))
    (runRounds family.toFamily basis O)

/-- The run's pre-IPA reads are the oracle's answers at the squeeze prefixes.  This is what lets
a per-challenge event embed into the index-generic squeeze surface. -/
theorem straightLineRunReads_eq
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    wrappedPreIpaReads (straightLineRunOutput family basis O) =
      fun i => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O) i) := by
  simpa [runReads, runProof] using wrappedPreIpaReads_run family.toFamily basis O

/-- A decoding run is an accepting run: the event's own acceptance component, restated at the
run's proof string and complete challenge record. -/
theorem straightLineAccepts_of_decoded
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
  ((family.straightLineConstraintSuccess? static basis O).get h).accepts

end Zcash.Snark
