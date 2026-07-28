import Zcash.Circuits.Action.Bundle
import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Action.IronwoodGardenActionBridge.ActionGarden

/-!
  Concrete correspondence between the axiom-free integer Action model and
  Ironwood's existing field-valued Action statement.

  The standalone model deliberately has no knowledge of `ZMod`, Halo2, Clean,
  or Ironwood.  This file is the only place where canonical integer
  representatives are transported to and from `Fp`, `Fq`, and `Point Fp`.
-/

namespace Zcash.Circuits.Action.Circuit.ActionGardenBridge

open Halo2

namespace ProofCore

open ActionGarden

abbrev Z := ActionGarden.Z
abbrev Point := ActionGarden.Point

structure CoreParameters where
  poseidon : PoseidonParameters
  sinsemillaGenerator : Z → Point
  noteCommitQ : Point
  commitIvkQ : Point
  merkleCrhQ : Point
  spendAuthG : Point
  valueCommitVG : Point
  valueCommitRG : Point
  nullifierKG : Point
  noteCommitRG : Point
  commitIvkRG : Point

def sinsemillaStep (parameters : CoreParameters)
    (accumulator : Point) (chunk : Z) : Point :=
  let generator := parameters.sinsemillaGenerator chunk
  pointAdd (pointAdd accumulator generator) accumulator

def sinsemillaStepDefined (parameters : CoreParameters)
    (accumulator : Point) (chunk : Z) : Prop :=
  let generator := parameters.sinsemillaGenerator chunk
  let firstSum := pointAdd accumulator generator
  pointIsIdentity accumulator = false /\
  pointIsIdentity generator = false /\
  baseEqual accumulator.x generator.x = false /\
  pointIsIdentity firstSum = false /\
  baseEqual firstSum.x accumulator.x = false

def sinsemillaHashToPoint
    (parameters : CoreParameters) (domain : Point) (chunks : List Z) : Point :=
  List.foldl
    (fun accumulator chunk => sinsemillaStep parameters accumulator chunk)
    domain
    chunks

def sinsemillaHashDefinedFrom
    (parameters : CoreParameters) : Point → List Z → Prop
  | _, List.nil => True
  | accumulator, List.cons chunk rest =>
      sinsemillaStepDefined parameters accumulator chunk /\
      sinsemillaHashDefinedFrom parameters
        (sinsemillaStep parameters accumulator chunk) rest

def sinsemillaHashDefined
    (parameters : CoreParameters) (domain : Point) (chunks : List Z) : Prop :=
  sinsemillaHashDefinedFrom parameters domain chunks

/-! ## Protocol message encodings

Messages are first assembled as nonnegative integers, then decomposed
little-endian into fixed counts of 10-bit words.  Point encodings include the
parity bit at bit 255, exactly as required by Orchard NoteCommit. -/

def chunksOf (value count : Z) : List Z :=
  List.map
    (fun index =>
      zMod
        (zDiv value
          (zPowNat zTwo (Nat.mul 10 index)))
        (Int.ofNat 1024))
    (List.range (Int.toNat count))

def pointParity (point : Point) : Z :=
  zMod point.y zTwo

def noteCommitMessage
    (gd pkd : Point) (value rho psi : Z) : Z :=
  zAdd
    (zAdd
      (zAdd
        (zAdd
          (zAdd
            (zAdd
              (baseNormalize gd.x)
              (zMul (zPowNat zTwo 255) (pointParity gd)))
            (zMul (zPowNat zTwo 256) (baseNormalize pkd.x)))
          (zMul (zPowNat zTwo 511) (pointParity pkd)))
        (zMul (zPowNat zTwo 512) value))
      (zMul (zPowNat zTwo 576) rho))
    (zMul (zPowNat zTwo 831) psi)

def noteCommitChunks
    (gd pkd : Point) (value rho psi : Z) : List Z :=
  chunksOf (noteCommitMessage gd pkd value rho psi) (Int.ofNat 109)

def commitIvkMessage (ak nk : Z) : Z :=
  zAdd ak (zMul (zPowNat zTwo 255) nk)

def commitIvkChunks (ak nk : Z) : List Z :=
  chunksOf (commitIvkMessage ak nk) (Int.ofNat 51)

def merkleMessage (layer left right : Z) : Z :=
  zAdd layer
    (zAdd
      (zMul (zPowNat zTwo 10) left)
      (zMul (zPowNat zTwo 265) right))

def merkleChunks (layer left right : Z) : List Z :=
  chunksOf (merkleMessage layer left right) (Int.ofNat 52)

/-! ## Merkle authentication paths

Only sibling and direction are stored.  The layer is derived from list
position, starting at zero, which is the canonical representation used by the
Lean-to-Rocq bridge.  Definedness is tracked at every Sinsemilla fold. -/

structure CorePathElement where
  sibling : Z
  isRight : Bool
deriving DecidableEq, Repr

def merkleChildren (node : Z) (element : CorePathElement) : Z × Z :=
  if element.isRight
  then (element.sibling, node)
  else (node, element.sibling)

def merkleStep (parameters : CoreParameters)
    (layer node : Z) (element : CorePathElement) : Z :=
  let children := merkleChildren node element
  extractX
    (sinsemillaHashToPoint parameters parameters.merkleCrhQ
      (merkleChunks layer children.1 children.2))

def merkleStepDefined (parameters : CoreParameters)
    (layer node : Z) (element : CorePathElement) : Prop :=
  let children := merkleChildren node element
  sinsemillaHashDefined parameters parameters.merkleCrhQ
    (merkleChunks layer children.1 children.2)

def merkleRootFrom
    (parameters : CoreParameters) : Z → Z → List CorePathElement → Z
  | _, node, List.nil => node
  | layer, node, List.cons element rest =>
      merkleRootFrom parameters
        (zAdd layer zOne)
        (merkleStep parameters layer node element)
        rest

def merkleRoot
    (parameters : CoreParameters) (leaf : Z) (path : List CorePathElement) : Z :=
  merkleRootFrom parameters zZero leaf path

def merklePathDefinedFrom
    (parameters : CoreParameters) : Z → Z → List CorePathElement → Prop
  | _, _, List.nil => True
  | layer, node, List.cons element rest =>
      merkleStepDefined parameters layer node element /\
      merklePathDefinedFrom parameters
        (zAdd layer zOne)
        (merkleStep parameters layer node element)
        rest

def merklePathDefined
    (parameters : CoreParameters) (leaf : Z) (path : List CorePathElement) : Prop :=
  merklePathDefinedFrom parameters zZero leaf path

def pathDepth : List CorePathElement → Z
  | List.nil => zZero
  | List.cons _ rest => zAdd zOne (pathDepth rest)

/-! ## Action records and output primitives

`CoreActionInputs` contains every value needed either by validity or by the output
function.  Base-field and scalar-field values still share carrier `Z`; the
validity predicate below states their canonical domains explicitly. -/

structure CoreActionInputs where
  ak : Point
  nk : Z
  rhoOld : Z
  psiOld : Z
  cmOld : Point
  gdOld : Point
  pkdOld : Point
  vOld : Z
  rivk : Z
  alpha : Z
  rcmOld : Z
  anchorPublic : Z
  enableSpend : Z
  enableOutput : Z
  disableCrossAddress : Z
  magnitude : Z
  sign : Z
  leaf : Z
  path : List CorePathElement
  gdNew : Point
  pkdNew : Point
  vNew : Z
  psiNew : Z
  rcmNew : Z
  rcv : Z
deriving DecidableEq, Repr

structure CoreActionOutputs where
  anchor : Z
  cvNet : Point
  nfOld : Z
  rk : Point
  cmx : Z
deriving DecidableEq, Repr

def coreSignedNetValue (magnitude sign : Z) : Z :=
  if baseEqual sign zOne then baseToScalar magnitude
  else scalarNeg (baseToScalar magnitude)

def coreSpendAuthRandomize
    (parameters : CoreParameters) (ak : Point) (alpha : Z) : Point :=
  pointAdd ak (scalarMul alpha parameters.spendAuthG)

def coreValueCommit
    (parameters : CoreParameters) (value randomness : Z) : Point :=
  pointAdd
    (scalarMul value parameters.valueCommitVG)
    (scalarMul randomness parameters.valueCommitRG)

def coreNullifier
    (parameters : CoreParameters) (nk rho psi : Z) (cm : Point) : Z :=
  let hash := poseidonHash2 parameters.poseidon nk rho
  let scalar := baseToScalar (baseAdd hash psi)
  extractX
    (pointAdd
      (scalarMul scalar parameters.nullifierKG)
      cm)

def coreNoteCommit
    (parameters : CoreParameters)
    (gd pkd : Point) (value rho psi randomness : Z) : Point :=
  pointAdd
    (sinsemillaHashToPoint parameters parameters.noteCommitQ
      (noteCommitChunks gd pkd value rho psi))
    (scalarMul randomness parameters.noteCommitRG)

def coreCommitIvk
    (parameters : CoreParameters) (ak nk randomness : Z) : Point :=
  pointAdd
    (sinsemillaHashToPoint parameters parameters.commitIvkQ
      (commitIvkChunks ak nk))
    (scalarMul randomness parameters.commitIvkRG)

/-! ## Input validity

The relation is split into seven named groups so each bridge can prove and
review one protocol obligation at a time.  The final conjunction includes
parameter validity, typed representations, numeric ranges, value/flag
constraints, ownership, Merkle validity, and new-note hash definedness. -/

def coreParametersValid (parameters : CoreParameters) : Prop :=
  pointCanonical parameters.noteCommitQ /\
  pointCanonical parameters.commitIvkQ /\
  pointCanonical parameters.merkleCrhQ /\
  pointCanonical parameters.spendAuthG /\
  pointCanonical parameters.valueCommitVG /\
  pointCanonical parameters.valueCommitRG /\
  pointCanonical parameters.nullifierKG /\
  pointCanonical parameters.noteCommitRG /\
  pointCanonical parameters.commitIvkRG /\
  pointOnCurve parameters.noteCommitQ /\
  pointOnCurve parameters.commitIvkQ /\
  pointOnCurve parameters.merkleCrhQ /\
  pointOnCurve parameters.spendAuthG /\
  pointOnCurve parameters.valueCommitVG /\
  pointOnCurve parameters.valueCommitRG /\
  pointOnCurve parameters.nullifierKG /\
  pointOnCurve parameters.noteCommitRG /\
  pointOnCurve parameters.commitIvkRG /\
  forall chunk : Z,
    inRange chunk (Int.ofNat 1024) ->
    pointCanonical (parameters.sinsemillaGenerator chunk) /\
    pointOnCurve (parameters.sinsemillaGenerator chunk)

def corePointsTyped (input : CoreActionInputs) : Prop :=
  pointCanonical input.ak /\
  pointCanonical input.cmOld /\
  pointCanonical input.gdOld /\
  pointCanonical input.pkdOld /\
  pointCanonical input.gdNew /\
  pointCanonical input.pkdNew /\
  pointOnCurve input.ak /\
  pointValid input.cmOld /\
  pointOnCurve input.gdOld /\
  pointOnCurve input.pkdOld /\
  pointOnCurve input.gdNew /\
  pointOnCurve input.pkdNew

def coreBaseValuesTyped (input : CoreActionInputs) : Prop :=
  baseCanonical input.nk /\
  baseCanonical input.rhoOld /\
  baseCanonical input.psiOld /\
  baseCanonical input.vOld /\
  baseCanonical input.anchorPublic /\
  baseCanonical input.enableSpend /\
  baseCanonical input.enableOutput /\
  baseCanonical input.disableCrossAddress /\
  baseCanonical input.magnitude /\
  baseCanonical input.sign /\
  baseCanonical input.leaf /\
  baseCanonical input.vNew /\
  baseCanonical input.psiNew

def coreScalarValuesTyped (input : CoreActionInputs) : Prop :=
  scalarCanonical input.rivk /\
  scalarCanonical input.alpha /\
  scalarCanonical input.rcmOld /\
  scalarCanonical input.rcmNew /\
  scalarCanonical input.rcv

def coreInputsTyped (input : CoreActionInputs) : Prop :=
  corePointsTyped input /\
  coreBaseValuesTyped input /\
  coreScalarValuesTyped input

def coreRangesValid (input : CoreActionInputs) : Prop :=
  let twoTo64 := zPowNat zTwo 64
  let twoTo255 := zPowNat zTwo 255
  inRange input.vOld twoTo64 /\
  inRange input.vNew twoTo64 /\
  inRange input.magnitude twoTo64 /\
  (input.sign = zOne \/ input.sign = baseNeg zOne) /\
  inRange input.leaf twoTo255 /\
  forall element : CorePathElement,
    List.Mem element input.path ->
    inRange element.sibling twoTo255

def coreValueConstraints (input : CoreActionInputs) : Prop :=
  baseSub input.vOld input.vNew =
    baseMul input.magnitude input.sign /\
  baseMul input.vOld (baseSub zOne input.enableSpend) = zZero /\
  baseMul input.vNew (baseSub zOne input.enableOutput) = zZero /\
  (Not (input.disableCrossAddress = zZero) ->
    input.gdOld = input.gdNew /\
    input.pkdOld = input.pkdNew)

def coreOwnershipValid
    (parameters : CoreParameters) (input : CoreActionInputs) : Prop :=
  let ivkChunks := commitIvkChunks (extractX input.ak) input.nk
  let oldNoteChunks :=
    noteCommitChunks input.gdOld input.pkdOld
      input.vOld input.rhoOld input.psiOld
  let ivkPoint :=
    coreCommitIvk parameters (extractX input.ak) input.nk input.rivk
  sinsemillaHashDefined parameters parameters.commitIvkQ ivkChunks /\
  input.pkdOld =
    basePointMul (extractX ivkPoint) input.gdOld /\
  sinsemillaHashDefined parameters parameters.noteCommitQ oldNoteChunks /\
  input.cmOld =
    coreNoteCommit parameters input.gdOld input.pkdOld
      input.vOld input.rhoOld input.psiOld input.rcmOld

def coreMerkleValid
    (parameters : CoreParameters) (input : CoreActionInputs) : Prop :=
  pathDepth input.path = Int.ofNat 32 /\
  merklePathDefined parameters input.leaf input.path /\
  input.leaf = extractX input.cmOld /\
  (input.vOld = zZero \/
    input.anchorPublic =
      merkleRoot parameters input.leaf input.path)

def coreNewNoteValid
    (parameters : CoreParameters) (input : CoreActionInputs) : Prop :=
  let nfOld :=
    coreNullifier parameters input.nk input.rhoOld input.psiOld input.cmOld
  sinsemillaHashDefined parameters parameters.noteCommitQ
    (noteCommitChunks input.gdNew input.pkdNew
      input.vNew nfOld input.psiNew)

def coreValidActionInputs
    (parameters : CoreParameters) (input : CoreActionInputs) : Prop :=
  coreParametersValid parameters /\
  coreInputsTyped input /\
  coreRangesValid input /\
  coreValueConstraints input /\
  coreOwnershipValid parameters input /\
  coreMerkleValid parameters input /\
  coreNewNoteValid parameters input

/-! ## Deterministic Action output

This is the high-level input-to-output function.  Validity is intentionally
separate: callers may compute the total function on any record, while the
equivalence theorems use `coreValidActionInputs` to select the protocol-defined
branch. -/

def coreOrchardAction
    (parameters : CoreParameters) (input : CoreActionInputs) : CoreActionOutputs :=
  let nfOld :=
    coreNullifier parameters input.nk input.rhoOld input.psiOld input.cmOld
  let rhoNew := nfOld
  {
    anchor :=
      if baseEqual input.vOld zZero
      then input.anchorPublic
      else merkleRoot parameters input.leaf input.path
    cvNet :=
      coreValueCommit parameters
        (coreSignedNetValue input.magnitude input.sign)
        input.rcv
    nfOld := nfOld
    rk := coreSpendAuthRandomize parameters input.ak input.alpha
    cmx :=
      extractX
        (coreNoteCommit parameters input.gdNew input.pkdNew
          input.vNew rhoNew input.psiNew input.rcmNew)
  }

end ProofCore


def fpToZ (value : Fp) : ActionGarden.Z :=
  Int.ofNat value.val

def fqToZ (value : Fq) : ActionGarden.Z :=
  Int.ofNat value.val

def pointToZ (point : Point Fp) : ActionGarden.Point :=
  { x := fpToZ point.x, y := fpToZ point.y }

def stateToZ
    (state : Poseidon.Permute.State Fp) : ActionGarden.State3 :=
  {
    x0 := fpToZ state.x0
    x1 := fpToZ state.x1
    x2 := fpToZ state.x2
  }

def poseidonParameters : ActionGarden.PoseidonParameters :=
  {
    roundConstant :=
      fun round =>
        stateToZ
          (Poseidon.Permute.P128Pow5T3.roundConstants (Int.toNat round))
    mds := {
      m00 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 0 0)
      m01 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 0 1)
      m02 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 0 2)
      m10 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 1 0)
      m11 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 1 1)
      m12 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 1 2)
      m20 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 2 0)
      m21 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 2 1)
      m22 := fpToZ (Poseidon.Permute.P128Pow5T3.mds 2 2)
    }
  }

def parameters (G : Specs.Sinsemilla.Generators) (B : Bases) :
    ProofCore.CoreParameters :=
  {
    poseidon := poseidonParameters
    sinsemillaGenerator :=
      fun chunk => pointToZ (G.S (Int.toNat chunk))
    noteCommitQ := pointToZ B.noteQ
    commitIvkQ := pointToZ B.ivkQ
    merkleCrhQ := pointToZ B.merkleQ
    spendAuthG := pointToZ B.spendAuthG.point
    valueCommitVG := pointToZ B.valueCommitV.point
    valueCommitRG := pointToZ B.valueCommitR.point
    nullifierKG := pointToZ B.nullifierK.point
    noteCommitRG := pointToZ B.noteCommitR.point
    commitIvkRG := pointToZ B.commitIvkR.point
  }

def pathElementOf (element : Fp × Fp) :
    ProofCore.CorePathElement :=
  {
    sibling := fpToZ element.1
    isRight := decide (element.2 = (1 : Fp))
  }

def pathElement (wit : ActionData) (index : Nat) :
    ProofCore.CorePathElement :=
  pathElementOf (wit.merklePath index)

def pathSegment
    (wit : Nat → Fp × Fp) (count : Nat) :
    List ProofCore.CorePathElement :=
  (List.range count).map (fun index => pathElementOf (wit index))

def path (wit : ActionData) : List ProofCore.CorePathElement :=
  pathSegment wit.merklePath 32

def input (wit : ActionData) : ProofCore.CoreActionInputs :=
  {
    ak := pointToZ wit.akP
    nk := fpToZ wit.nk
    rhoOld := fpToZ wit.rhoOld
    psiOld := fpToZ wit.psiOld
    cmOld := pointToZ wit.cmOld
    gdOld := pointToZ wit.gdOld
    pkdOld := pointToZ wit.pkdOld
    vOld := fpToZ wit.vOld
    rivk := fqToZ wit.rivk.2
    alpha := fqToZ wit.alpha.2
    rcmOld := fqToZ wit.rcmOld.2
    anchorPublic := fpToZ wit.anchor
    enableSpend := fpToZ wit.enableSpend
    enableOutput := fpToZ wit.enableOutput
    disableCrossAddress := fpToZ wit.disableCrossAddress
    magnitude := fpToZ wit.magnitude
    sign := fpToZ wit.sign
    leaf := fpToZ wit.cmOld.x
    path := path wit
    gdNew := pointToZ wit.gdNew
    pkdNew := pointToZ wit.pkdNew
    vNew := fpToZ wit.vNew
    psiNew := fpToZ wit.psiNew
    rcmNew := fqToZ wit.rcmNew.2
    rcv := fqToZ wit.rcv.2
  }

def output (wit : ActionData) : ProofCore.CoreActionOutputs :=
  {
    anchor := fpToZ wit.anchor
    cvNet := pointToZ { x := wit.cvX, y := wit.cvY }
    nfOld := fpToZ wit.nfOld
    rk := pointToZ { x := wit.rkX, y := wit.rkY }
    cmx := fpToZ wit.cmx
  }

/-! ## Garden-shaped deployed adapters

The public standalone record mirrors Garden rather than the circuit witness.
In particular, every Merkle element stores its layer, while the four values
used only by validity live in `FullActionInputs` instead of the protocol input
record consumed by `orchardAction`. -/

def gardenPathFrom
    (layer : Nat) :
    List ProofCore.CorePathElement →
      List (ActionGarden.Z × ActionGarden.Z × Bool)
  | List.nil => List.nil
  | List.cons element rest =>
      List.cons
        (Int.ofNat layer, element.sibling, element.isRight)
        (gardenPathFrom (Nat.succ layer) rest)

def gardenPath (wit : ActionData) :
    List (ActionGarden.Z × ActionGarden.Z × Bool) :=
  gardenPathFrom 0 (path wit)

def gardenInput (wit : ActionData) : ActionGarden.ActionInputs :=
  {
    inAk := pointToZ wit.akP
    inNk := fpToZ wit.nk
    inRhoOld := fpToZ wit.rhoOld
    inPsiOld := fpToZ wit.psiOld
    inCmOld := pointToZ wit.cmOld
    inGdOld := pointToZ wit.gdOld
    inPkdOld := pointToZ wit.pkdOld
    inVOld := fpToZ wit.vOld
    inRivk := fqToZ wit.rivk.2
    inAlpha := fqToZ wit.alpha.2
    inAnchorPublic := fpToZ wit.anchor
    inRcv := fqToZ wit.rcv.2
    inMagnitude := fpToZ wit.magnitude
    inSign := fpToZ wit.sign
    inLeaf := fpToZ wit.cmOld.x
    inPath := gardenPath wit
    inGdNew := pointToZ wit.gdNew
    inPkdNew := pointToZ wit.pkdNew
    inVNew := fpToZ wit.vNew
    inPsiNew := fpToZ wit.psiNew
    inRcmNew := fqToZ wit.rcmNew.2
  }

def fullInput (wit : ActionData) : ActionGarden.FullActionInputs :=
  {
    action := gardenInput wit
    rcmOld := fqToZ wit.rcmOld.2
    enableSpend := fpToZ wit.enableSpend
    enableOutput := fpToZ wit.enableOutput
    disableCrossAddress := fpToZ wit.disableCrossAddress
  }

def gardenOutput (wit : ActionData) : ActionGarden.ActionOutputs :=
  {
    outAnchor := fpToZ wit.anchor
    outCvNet := pointToZ { x := wit.cvX, y := wit.cvY }
    outNfOld := fpToZ wit.nfOld
    outRk := pointToZ { x := wit.rkX, y := wit.rkY }
    outCmx := fpToZ wit.cmx
  }

def gardenOutputOfCore
    (core : ProofCore.CoreActionOutputs) : ActionGarden.ActionOutputs :=
  {
    outAnchor := core.anchor
    outCvNet := core.cvNet
    outNfOld := core.nfOld
    outRk := core.rk
    outCmx := core.cmx
  }

def dropGardenPath
    (path : List (ActionGarden.Z × ActionGarden.Z × Bool)) :
    List ProofCore.CorePathElement :=
  path.map
    (fun element =>
      { sibling := element.2.1, isRight := element.2.2 })

def coreInputOfFull
    (input : ActionGarden.FullActionInputs) :
    ProofCore.CoreActionInputs :=
  let core := input.action
  {
    ak := core.inAk
    nk := core.inNk
    rhoOld := core.inRhoOld
    psiOld := core.inPsiOld
    cmOld := core.inCmOld
    gdOld := core.inGdOld
    pkdOld := core.inPkdOld
    vOld := core.inVOld
    rivk := core.inRivk
    alpha := core.inAlpha
    rcmOld := input.rcmOld
    anchorPublic := core.inAnchorPublic
    enableSpend := input.enableSpend
    enableOutput := input.enableOutput
    disableCrossAddress := input.disableCrossAddress
    magnitude := core.inMagnitude
    sign := core.inSign
    leaf := core.inLeaf
    path := dropGardenPath core.inPath
    gdNew := core.inGdNew
    pkdNew := core.inPkdNew
    vNew := core.inVNew
    psiNew := core.inPsiNew
    rcmNew := core.inRcmNew
    rcv := core.inRcv
  }

theorem dropGardenPath_gardenPathFrom
    (layer : Nat) (path : List ProofCore.CorePathElement) :
    dropGardenPath (gardenPathFrom layer path) = path := by
  induction path generalizing layer with
  | nil =>
      rfl
  | cons element rest inductionHypothesis =>
      simp only [gardenPathFrom, dropGardenPath, List.map_cons]
      change
        { sibling := element.sibling, isRight := element.isRight } ::
            dropGardenPath (gardenPathFrom (Nat.succ layer) rest) =
          element :: rest
      rw [inductionHypothesis]

theorem coreInputOfFull_fullInput (wit : ActionData) :
    coreInputOfFull (fullInput wit) = input wit := by
  simp only [coreInputOfFull, fullInput, gardenInput, gardenPath, input,
    dropGardenPath_gardenPathFrom]

/-! ## Deployed constant audit

The standalone file spells every deployed constant as an integer literal.
The definitions and certificates below compare those literals with the
proof-carrying constants imported by Ironwood.  The two whole-table theorems
are stronger review artifacts than scattered pointwise checks; the finite
accessor theorems are the form consumed by indexed protocol operations. -/

def ironwoodPoseidonRoundConstants : List ActionGarden.State3 :=
  (List.range 64).map
    (fun round =>
      stateToZ
        (Poseidon.Permute.P128Pow5T3.roundConstants round))

def ironwoodSinsemillaGenerators : List ActionGarden.Point :=
  (List.range 1024).map
    (fun word =>
      pointToZ
        (Specs.Sinsemilla.orchardGenerators.S word))

set_option maxRecDepth 100000 in
theorem orchardPoseidonRoundConstants_deployed :
    ActionGarden.orchardPoseidonRoundConstants =
      ironwoodPoseidonRoundConstants := by
  native_decide

set_option maxRecDepth 100000 in
theorem orchardSinsemillaGenerators_deployed :
    ActionGarden.orchardSinsemillaGenerators =
      ironwoodSinsemillaGenerators := by
  native_decide

set_option maxRecDepth 100000 in
theorem orchardPoseidonRoundConstant_deployed :
    ∀ round : Fin 64,
      ActionGarden.orchardPoseidonRoundConstant (Int.ofNat round.val) =
        stateToZ
          (Poseidon.Permute.P128Pow5T3.roundConstants round.val) := by
  native_decide

set_option maxRecDepth 100000 in
theorem orchardSinsemillaGenerator_deployed :
    ∀ word : Fin 1024,
      ActionGarden.orchardSinsemillaGenerator (Int.ofNat word.val) =
        pointToZ (Specs.Sinsemilla.orchardGenerators.S word.val) := by
  native_decide

theorem orchardNoteCommitQ_deployed :
    ActionGarden.orchardNoteCommitQ =
      pointToZ Zcash.Circuits.Action.noteQ := by
  native_decide

theorem orchardCommitIvkQ_deployed :
    ActionGarden.orchardCommitIvkQ =
      pointToZ Zcash.Circuits.Action.ivkQ := by
  native_decide

theorem orchardMerkleCrhQ_deployed :
    ActionGarden.orchardMerkleCrhQ =
      pointToZ Zcash.Circuits.Action.merkleQ := by
  native_decide

theorem orchardSpendAuthG_deployed :
    ActionGarden.orchardSpendAuthG =
      pointToZ Zcash.Circuits.Action.orchardBases.spendAuthG.point := by
  native_decide

theorem orchardValueCommitVG_deployed :
    ActionGarden.orchardValueCommitVG =
      pointToZ Zcash.Circuits.Action.orchardBases.valueCommitV.point := by
  native_decide

theorem orchardValueCommitRG_deployed :
    ActionGarden.orchardValueCommitRG =
      pointToZ Zcash.Circuits.Action.orchardBases.valueCommitR.point := by
  native_decide

theorem orchardNullifierKG_deployed :
    ActionGarden.orchardNullifierKG =
      pointToZ Zcash.Circuits.Action.orchardBases.nullifierK.point := by
  native_decide

theorem orchardNoteCommitRG_deployed :
    ActionGarden.orchardNoteCommitRG =
      pointToZ Zcash.Circuits.Action.orchardBases.noteCommitR.point := by
  native_decide

theorem orchardCommitIvkRG_deployed :
    ActionGarden.orchardCommitIvkRG =
      pointToZ Zcash.Circuits.Action.orchardBases.commitIvkR.point := by
  native_decide

def zToFp (value : ActionGarden.Z) : Fp :=
  Int.cast value

def zToFq (value : ActionGarden.Z) : Fq :=
  Int.cast value

theorem pallasBaseModulus_eq :
    ActionGarden.pallasBaseModulus =
      Int.ofNat CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
  native_decide

theorem pallasScalarModulus_eq :
    ActionGarden.pallasScalarModulus =
      Int.ofNat CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  native_decide

theorem fpToZ_zToFp (value : ActionGarden.Z) :
    fpToZ (zToFp value) = ActionGarden.baseNormalize value := by
  unfold fpToZ zToFp ActionGarden.baseNormalize ActionGarden.normalize ActionGarden.zMod
  rw [pallasBaseModulus_eq]
  change
    ((ZMod.val (Int.cast value : Fp) : Int) =
      Int.emod value
        (Int.ofNat CompElliptic.Fields.Pasta.PALLAS_BASE_CARD))
  exact ZMod.val_intCast value

theorem fqToZ_zToFq (value : ActionGarden.Z) :
    fqToZ (zToFq value) = ActionGarden.scalarNormalize value := by
  unfold fqToZ zToFq ActionGarden.scalarNormalize ActionGarden.normalize ActionGarden.zMod
  rw [pallasScalarModulus_eq]
  change
    ((ZMod.val (Int.cast value : Fq) : Int) =
      Int.emod value
        (Int.ofNat CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD))
  exact ZMod.val_intCast value

theorem zToFp_fpToZ (value : Fp) :
    zToFp (fpToZ value) = value := by
  unfold zToFp fpToZ
  change ((value.val : Nat) : Fp) = value
  exact ZMod.natCast_zmod_val value

theorem zToFq_fqToZ (value : Fq) :
    zToFq (fqToZ value) = value := by
  unfold zToFq fqToZ
  change ((value.val : Nat) : Fq) = value
  exact ZMod.natCast_zmod_val value

theorem fpToZ_add (left right : Fp) :
    fpToZ (left + right) =
      ActionGarden.baseAdd (fpToZ left) (fpToZ right) := by
  unfold ActionGarden.baseAdd ActionGarden.addModulo
  change fpToZ (left + right) =
    ActionGarden.baseNormalize (ActionGarden.zAdd (fpToZ left) (fpToZ right))
  rw [← fpToZ_zToFp (ActionGarden.zAdd (fpToZ left) (fpToZ right))]
  apply congrArg fpToZ
  unfold zToFp ActionGarden.zAdd
  rw [show (Int.cast (Int.add (fpToZ left) (fpToZ right)) : Fp) =
    Int.cast (fpToZ left) + Int.cast (fpToZ right) from
      Int.cast_add (fpToZ left) (fpToZ right)]
  rw [show (Int.cast (fpToZ left) : Fp) = left from zToFp_fpToZ left,
    show (Int.cast (fpToZ right) : Fp) = right from zToFp_fpToZ right]

theorem fpToZ_sub (left right : Fp) :
    fpToZ (left - right) =
      ActionGarden.baseSub (fpToZ left) (fpToZ right) := by
  unfold ActionGarden.baseSub ActionGarden.subModulo
  change fpToZ (left - right) =
    ActionGarden.baseNormalize (ActionGarden.zSub (fpToZ left) (fpToZ right))
  rw [← fpToZ_zToFp (ActionGarden.zSub (fpToZ left) (fpToZ right))]
  apply congrArg fpToZ
  unfold zToFp ActionGarden.zSub
  rw [show (Int.cast (Int.sub (fpToZ left) (fpToZ right)) : Fp) =
    Int.cast (fpToZ left) - Int.cast (fpToZ right) from
      Int.cast_sub (fpToZ left) (fpToZ right)]
  rw [show (Int.cast (fpToZ left) : Fp) = left from zToFp_fpToZ left,
    show (Int.cast (fpToZ right) : Fp) = right from zToFp_fpToZ right]

theorem fpToZ_mul (left right : Fp) :
    fpToZ (left * right) =
      ActionGarden.baseMul (fpToZ left) (fpToZ right) := by
  unfold ActionGarden.baseMul ActionGarden.mulModulo
  change fpToZ (left * right) =
    ActionGarden.baseNormalize (ActionGarden.zMul (fpToZ left) (fpToZ right))
  rw [← fpToZ_zToFp (ActionGarden.zMul (fpToZ left) (fpToZ right))]
  apply congrArg fpToZ
  unfold zToFp ActionGarden.zMul
  rw [show (Int.cast (Int.mul (fpToZ left) (fpToZ right)) : Fp) =
    Int.cast (fpToZ left) * Int.cast (fpToZ right) from
      Int.cast_mul (fpToZ left) (fpToZ right)]
  rw [show (Int.cast (fpToZ left) : Fp) = left from zToFp_fpToZ left,
    show (Int.cast (fpToZ right) : Fp) = right from zToFp_fpToZ right]

theorem fpToZ_neg (value : Fp) :
    fpToZ (-value) = ActionGarden.baseNeg (fpToZ value) := by
  unfold ActionGarden.baseNeg ActionGarden.negModulo
  change fpToZ (-value) =
    ActionGarden.baseNormalize (ActionGarden.zNeg (fpToZ value))
  rw [← fpToZ_zToFp (ActionGarden.zNeg (fpToZ value))]
  apply congrArg fpToZ
  unfold zToFp ActionGarden.zNeg
  rw [show (Int.cast (Int.neg (fpToZ value)) : Fp) =
    -Int.cast (fpToZ value) from Int.cast_neg (fpToZ value)]
  rw [show (Int.cast (fpToZ value) : Fp) = value from zToFp_fpToZ value]

theorem fqToZ_add (left right : Fq) :
    fqToZ (left + right) =
      ActionGarden.scalarAdd (fqToZ left) (fqToZ right) := by
  unfold ActionGarden.scalarAdd ActionGarden.addModulo
  change fqToZ (left + right) =
    ActionGarden.scalarNormalize (ActionGarden.zAdd (fqToZ left) (fqToZ right))
  rw [← fqToZ_zToFq (ActionGarden.zAdd (fqToZ left) (fqToZ right))]
  apply congrArg fqToZ
  unfold zToFq ActionGarden.zAdd
  rw [show (Int.cast (Int.add (fqToZ left) (fqToZ right)) : Fq) =
    Int.cast (fqToZ left) + Int.cast (fqToZ right) from
      Int.cast_add (fqToZ left) (fqToZ right)]
  rw [show (Int.cast (fqToZ left) : Fq) = left from zToFq_fqToZ left,
    show (Int.cast (fqToZ right) : Fq) = right from zToFq_fqToZ right]

theorem fqToZ_neg (value : Fq) :
    fqToZ (-value) = ActionGarden.scalarNeg (fqToZ value) := by
  unfold ActionGarden.scalarNeg ActionGarden.negModulo
  change fqToZ (-value) =
    ActionGarden.scalarNormalize (ActionGarden.zNeg (fqToZ value))
  rw [← fqToZ_zToFq (ActionGarden.zNeg (fqToZ value))]
  apply congrArg fqToZ
  unfold zToFq ActionGarden.zNeg
  rw [show (Int.cast (Int.neg (fqToZ value)) : Fq) =
    -Int.cast (fqToZ value) from Int.cast_neg (fqToZ value)]
  rw [show (Int.cast (fqToZ value) : Fq) = value from zToFq_fqToZ value]

theorem baseNormalize_fpToZ (value : Fp) :
    ActionGarden.baseNormalize (fpToZ value) = fpToZ value := by
  symm
  rw [← fpToZ_zToFp]
  rw [zToFp_fpToZ]

theorem scalarNormalize_fqToZ (value : Fq) :
    ActionGarden.scalarNormalize (fqToZ value) = fqToZ value := by
  symm
  rw [← fqToZ_zToFq]
  rw [zToFq_fqToZ]

theorem fpToZ_ne_zero {value : Fp} (nonzero : value ≠ 0) :
    fpToZ value ≠ ActionGarden.zZero := by
  intro representativeZero
  apply nonzero
  have castEquality := congrArg zToFp representativeZero
  simpa [ActionGarden.zZero, zToFp_fpToZ] using castEquality

theorem baseInverseExponent_eq :
    Int.toNat
      (ActionGarden.zSub ActionGarden.pallasBaseModulus ActionGarden.zTwo) =
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2 := by
  native_decide

theorem fp_pow_card_sub_two_eq_inv {value : Fp} (nonzero : value ≠ 0) :
    value ^ (CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2) = value⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have exponentEquality :
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2 + 1 =
        CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 1 := by native_decide
  rw [exponentEquality]
  exact ZMod.pow_card_sub_one_eq_one nonzero

theorem fpToZ_inv (value : Fp) :
    fpToZ value⁻¹ = ActionGarden.baseInverse (fpToZ value) := by
  by_cases nonzero : value = 0
  · subst value
    native_decide
  · have representativeNonzero := fpToZ_ne_zero nonzero
    unfold ActionGarden.baseInverse ActionGarden.modInverse
    change fpToZ value⁻¹ =
      if ActionGarden.zEq (ActionGarden.baseNormalize (fpToZ value))
          ActionGarden.zZero
      then ActionGarden.zZero
      else
        ActionGarden.baseNormalize
          (ActionGarden.zPowNat
            (ActionGarden.baseNormalize (fpToZ value))
            (Int.toNat
              (ActionGarden.zSub ActionGarden.pallasBaseModulus ActionGarden.zTwo)))
    rw [baseNormalize_fpToZ]
    simp only [ActionGarden.zEq, decide_eq_false_iff_not, representativeNonzero,
      ↓reduceIte]
    change fpToZ value⁻¹ =
      ActionGarden.baseNormalize
        (ActionGarden.zPowNat (fpToZ value)
          (Int.toNat
            (ActionGarden.zSub ActionGarden.pallasBaseModulus ActionGarden.zTwo)))
    rw [baseInverseExponent_eq]
    rw [← fpToZ_zToFp]
    apply congrArg fpToZ
    unfold zToFp ActionGarden.zPowNat
    rw [show
      (Int.cast
          (Int.pow (fpToZ value)
            (CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2)) : Fp) =
        (Int.cast (fpToZ value) : Fp) ^
          (CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2) from
      Int.cast_pow (fpToZ value)
        (CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 2)]
    rw [show (Int.cast (fpToZ value) : Fp) = value from zToFp_fpToZ value]
    exact (fp_pow_card_sub_two_eq_inv nonzero).symm

theorem fpToZ_div (numerator denominator : Fp) :
    fpToZ (numerator * denominator⁻¹) =
      ActionGarden.baseDiv (fpToZ numerator) (fpToZ denominator) := by
  unfold ActionGarden.baseDiv
  rw [← fpToZ_inv, ← fpToZ_mul]

theorem fpToZ_injective : Function.Injective fpToZ := by
  intro left right representativesEqual
  have castEquality := congrArg zToFp representativesEqual
  simpa [zToFp_fpToZ] using castEquality

theorem fqToZ_injective : Function.Injective fqToZ := by
  intro left right representativesEqual
  have castEquality := congrArg zToFq representativesEqual
  simpa [zToFq_fqToZ] using castEquality

theorem baseEqual_fpToZ (left right : Fp) :
    ActionGarden.baseEqual (fpToZ left) (fpToZ right) =
      decide (left = right) := by
  unfold ActionGarden.baseEqual
  rw [baseNormalize_fpToZ, baseNormalize_fpToZ]
  unfold ActionGarden.zEq
  by_cases equal : left = right
  · subst right
    simp
  · have representativesNotEqual : fpToZ left ≠ fpToZ right :=
      fun equality => equal (fpToZ_injective equality)
    simp [equal, representativesNotEqual]

theorem pointNormalize_pointToZ (point : Point Fp) :
    ActionGarden.pointNormalize (pointToZ point) = pointToZ point := by
  cases point with
  | mk x y =>
      simp only [ActionGarden.pointNormalize, pointToZ]
      rw [baseNormalize_fpToZ, baseNormalize_fpToZ]

theorem pointToZ_injective : Function.Injective pointToZ := by
  intro left right equality
  cases left with
  | mk leftX leftY =>
      cases right with
      | mk rightX rightY =>
          simp only [pointToZ, ActionGarden.Point.mk.injEq] at equality
          apply Point.ext_coords
          simp only [Point.coords]
          exact Prod.ext
            (fpToZ_injective equality.1)
            (fpToZ_injective equality.2)

theorem pointToZ_zero :
    pointToZ (0 : Point Fp) = ActionGarden.pointIdentity := by
  native_decide

theorem fpToZ_zero : fpToZ (0 : Fp) = ActionGarden.zZero := by
  native_decide

theorem fpToZ_one : fpToZ (1 : Fp) = ActionGarden.zOne := by
  native_decide

theorem fpToZ_two : fpToZ (2 : Fp) = ActionGarden.zTwo := by
  native_decide

theorem fpToZ_three : fpToZ (3 : Fp) = Int.ofNat 3 := by
  native_decide

theorem fpToZ_nat_zero : fpToZ (0 : Fp) = Int.ofNat 0 := by
  native_decide

theorem fpToZ_nat_two : fpToZ (2 : Fp) = Int.ofNat 2 := by
  native_decide

theorem baseEqual_add_zero (left right : Fp) :
    ActionGarden.baseEqual
        (ActionGarden.baseAdd (fpToZ left) (fpToZ right))
        ActionGarden.zZero =
      decide (left + right = 0) := by
  rw [← fpToZ_add, ← fpToZ_zero, baseEqual_fpToZ]

theorem pointIsIdentity_pointToZ (point : Point Fp) :
    ActionGarden.pointIsIdentity (pointToZ point) =
      decide (point = (0 : Point Fp)) := by
  cases point with
  | mk x y =>
      unfold ActionGarden.pointIsIdentity
      simp only [pointToZ, Point.zero_def, ActionGarden.pointIdentity]
      rw [← fpToZ_zero]
      rw [baseEqual_fpToZ, baseEqual_fpToZ]
      simp only [Point.mk.injEq]
      change
        (decide (x = 0) && decide (y = 0)) =
          decide (x = 0 ∧ y = 0)
      by_cases xZero : x = 0 <;> by_cases yZero : y = 0 <;>
        simp [xZero, yZero]

theorem extractX_pointToZ (point : Point Fp) :
    ActionGarden.extractX (pointToZ point) = fpToZ point.x := by
  unfold ActionGarden.extractX
  rw [pointIsIdentity_pointToZ]
  by_cases identity : point = 0
  · subst point
    native_decide
  · simp only [identity, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact baseNormalize_fpToZ point.x

theorem pointToZ_add (left right : Point Fp) :
    pointToZ (left + right) =
      ActionGarden.pointAdd (pointToZ left) (pointToZ right) := by
  rw [Point.add_def]
  by_cases leftIdentity : left = 0
  · subst left
    simp only [Point.zero_def, Point.coords]
    rw [CompElliptic.CurveForms.ShortWeierstrass.zero_add]
    unfold ActionGarden.pointAdd
    rw [pointIsIdentity_pointToZ]
    simp only [decide_true, ↓reduceIte]
    exact (pointNormalize_pointToZ right).symm
  ·
    by_cases rightIdentity : right = 0
    · subst right
      simp only [Point.zero_def, Point.coords]
      rw [CompElliptic.CurveForms.ShortWeierstrass.add_zero]
      unfold ActionGarden.pointAdd
      rw [pointIsIdentity_pointToZ]
      simp only [leftIdentity, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [pointIsIdentity_pointToZ]
      exact (pointNormalize_pointToZ left).symm
    ·
      have leftCoordsNonzero : left.coords ≠ (0, 0) := by
        intro coordinatesZero
        apply leftIdentity
        apply Point.ext_coords
        simpa [Point.zero_def] using coordinatesZero
      have rightCoordsNonzero : right.coords ≠ (0, 0) := by
        intro coordinatesZero
        apply rightIdentity
        apply Point.ext_coords
        simpa [Point.zero_def] using coordinatesZero
      unfold CompElliptic.CurveForms.ShortWeierstrass.add
      simp only [Point.coords]
      simp only [Point.coords] at leftCoordsNonzero rightCoordsNonzero
      rw [if_neg leftCoordsNonzero, if_neg rightCoordsNonzero]
      unfold ActionGarden.pointAdd
      rw [pointIsIdentity_pointToZ, pointIsIdentity_pointToZ]
      simp only [leftIdentity, rightIdentity, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      simp only [pointToZ]
      rw [baseEqual_fpToZ]
      by_cases xEqual : left.x = right.x
      · simp only [xEqual, decide_true, ↓reduceIte]
        rw [baseEqual_add_zero]
        by_cases inverse : left.y + right.y = 0
        · simp only [inverse, decide_true, ↓reduceIte]
          simp only [Point.ofCoords]
          exact pointToZ_zero
        · simp only [inverse, decide_false, Bool.false_eq_true, ↓reduceIte]
          simp only [Point.ofCoords, pallasA, add_zero, pow_two]
          simp only [ActionGarden.zZero, ActionGarden.zTwo]
          rw [← fpToZ_nat_zero, ← fpToZ_nat_two, ← fpToZ_three]
          simp only [← fpToZ_add, ← fpToZ_sub, ← fpToZ_mul,
            ← fpToZ_div]
          simp only [div_eq_mul_inv, add_zero]
      · simp only [xEqual, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp only [Point.ofCoords, pow_two]
        simp only [← fpToZ_sub, ← fpToZ_mul, ← fpToZ_div]
        rfl

theorem zEq_fpToZ (left right : Fp) :
    ActionGarden.zEq (fpToZ left) (fpToZ right) =
      decide (left = right) := by
  unfold ActionGarden.zEq
  by_cases equal : left = right
  · subst right
    simp
  · have representativesNotEqual : fpToZ left ≠ fpToZ right :=
      fun equality => equal (fpToZ_injective equality)
    simp [equal, representativesNotEqual]

theorem zEq_fpToZ_zero (value : Fp) :
    ActionGarden.zEq (fpToZ value) ActionGarden.zZero =
      decide (value = 0) := by
  rw [← fpToZ_zero, zEq_fpToZ]

theorem point_eq_zero_of_valid_of_x_eq_zero
    {point : Point Fp}
    (valid : point.Valid) (xZero : point.x = 0) :
    point = 0 := by
  apply Point.ext_coords
  simp only [Point.coords, Point.zero_def]
  exact Prod.ext xZero
    (Point.y_eq_zero_of_valid_of_x_eq_zero valid xZero)

theorem point_x_eq_zero_iff_of_valid
    {point : Point Fp} (valid : point.Valid) :
    point.x = 0 ↔ point = 0 := by
  constructor
  · exact point_eq_zero_of_valid_of_x_eq_zero valid
  · intro identity
    subst point
    rfl

/-- Garden's x-sentinel total addition computes Ironwood group addition on
valid Pallas points.  The validity hypotheses are exactly what identifies an
x-coordinate of zero with the `(0, 0)` identity representation. -/
theorem pointToZ_addGarden
    (left right : Point Fp)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    pointToZ (left + right) =
      ActionGarden.pointAddGarden (pointToZ left) (pointToZ right) := by
  rw [Point.add_def]
  by_cases leftXZero : left.x = 0
  · have leftIdentity :=
      point_eq_zero_of_valid_of_x_eq_zero leftValid leftXZero
    subst left
    simp only [Point.zero_def, Point.coords]
    rw [CompElliptic.CurveForms.ShortWeierstrass.zero_add]
    unfold ActionGarden.pointAddGarden
    simp only [pointToZ]
    rw [zEq_fpToZ_zero]
    simp
  ·
    by_cases rightXZero : right.x = 0
    · have rightIdentity :=
        point_eq_zero_of_valid_of_x_eq_zero rightValid rightXZero
      subst right
      simp only [Point.zero_def, Point.coords]
      rw [CompElliptic.CurveForms.ShortWeierstrass.add_zero]
      unfold ActionGarden.pointAddGarden
      simp only [pointToZ]
      rw [zEq_fpToZ_zero]
      simp only [leftXZero, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [zEq_fpToZ_zero]
      simp
    ·
      have leftIdentity : left ≠ 0 := by
        intro identity
        subst left
        exact leftXZero rfl
      have rightIdentity : right ≠ 0 := by
        intro identity
        subst right
        exact rightXZero rfl
      have leftCoordsNonzero : left.coords ≠ (0, 0) := by
        intro coordinatesZero
        apply leftIdentity
        apply Point.ext_coords
        simpa [Point.zero_def] using coordinatesZero
      have rightCoordsNonzero : right.coords ≠ (0, 0) := by
        intro coordinatesZero
        apply rightIdentity
        apply Point.ext_coords
        simpa [Point.zero_def] using coordinatesZero
      unfold CompElliptic.CurveForms.ShortWeierstrass.add
      simp only [Point.coords]
      simp only [Point.coords] at leftCoordsNonzero rightCoordsNonzero
      rw [if_neg leftCoordsNonzero, if_neg rightCoordsNonzero]
      unfold ActionGarden.pointAddGarden
      simp only [pointToZ]
      rw [zEq_fpToZ_zero, zEq_fpToZ_zero]
      simp only [leftXZero, rightXZero, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [zEq_fpToZ]
      by_cases xEqual : left.x = right.x
      · simp only [xEqual, decide_true, ↓reduceIte]
        rw [← fpToZ_add, zEq_fpToZ_zero]
        by_cases inverse : left.y + right.y = 0
        · simp only [inverse, decide_true, ↓reduceIte]
          simp only [Point.ofCoords]
          exact pointToZ_zero
        · simp only [inverse, decide_false, Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          simp only [Point.ofCoords, pallasA, add_zero, pow_two]
          simp only [ActionGarden.zTwo]
          rw [← fpToZ_nat_two, ← fpToZ_three]
          simp only [← fpToZ_add, ← fpToZ_sub, ← fpToZ_mul,
            ← fpToZ_div]
          simp only [div_eq_mul_inv, add_zero]
      · simp only [xEqual, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp only [Point.ofCoords, pow_two]
        simp only [← fpToZ_sub, ← fpToZ_mul, ← fpToZ_div]
        rfl

theorem pointToZ_nsmul (scalar : Nat) (point : Point Fp) :
    pointToZ (scalar • point) =
      ActionGarden.pointNatMul scalar (pointToZ point) := by
  induction scalar with
  | zero =>
      simp only [Point.nsmul_def,
        CompElliptic.CurveForms.ShortWeierstrass.smul,
        Point.ofCoords, pointToZ, ActionGarden.pointNatMul,
        ActionGarden.pointIdentity]
      rw [fpToZ_zero]
  | succ scalar inductionHypothesis =>
      rw [Point.nsmul_def]
      change
        pointToZ ((scalar • point) + point) =
          ActionGarden.pointAdd
            (ActionGarden.pointNatMul scalar (pointToZ point))
            (pointToZ point)
      rw [pointToZ_add]
      rw [inductionHypothesis]

theorem scalarNat_fqToZ (scalar : Fq) :
    Int.toNat (ActionGarden.scalarNormalize (fqToZ scalar)) = scalar.val := by
  rw [scalarNormalize_fqToZ]
  rfl

theorem pointToZ_fullScalarMul
    (base : Ecc.MulFixed.FixedBase) (scalar : Fq) :
    pointToZ (scalar • base) =
      ActionGarden.scalarMul (fqToZ scalar) (pointToZ base.point) := by
  change
    pointToZ (Ecc.MulFixed.FixedBase.scalarMul base scalar) =
      ActionGarden.scalarMul (fqToZ scalar) (pointToZ base.point)
  unfold Ecc.MulFixed.FixedBase.scalarMul ActionGarden.scalarMul
  rw [scalarNat_fqToZ]
  change pointToZ (scalar.val • base.point) =
    ActionGarden.pointNatMul scalar.val (pointToZ base.point)
  exact pointToZ_nsmul scalar.val base.point

theorem pointToZ_shortScalarMul
    (base : Ecc.MulFixed.Short.FixedBase) (scalar : Fq) :
    pointToZ (scalar • base) =
      ActionGarden.scalarMul (fqToZ scalar) (pointToZ base.point) := by
  change
    pointToZ (Ecc.MulFixed.Short.FixedBase.scalarMul base scalar) =
      ActionGarden.scalarMul (fqToZ scalar) (pointToZ base.point)
  unfold Ecc.MulFixed.Short.FixedBase.scalarMul ActionGarden.scalarMul
  rw [scalarNat_fqToZ]
  change pointToZ (scalar.val • base.point) =
    ActionGarden.pointNatMul scalar.val (pointToZ base.point)
  exact pointToZ_nsmul scalar.val base.point

def fieldPoseidonFullRound
    (round : Nat) (state : Poseidon.Permute.State Fp) :
    Poseidon.Permute.State Fp :=
  Poseidon.FullRound.value
    (Poseidon.FullRound.params
      Poseidon.Permute.P128Pow5T3.roundConstants
      Poseidon.Permute.P128Pow5T3.mds
      round)
    state

def fieldPoseidonPartialPair
    (round : Nat) (state : Poseidon.Permute.State Fp) :
    Poseidon.Permute.State Fp :=
  Poseidon.PartialRounds.value
    (Poseidon.PartialRounds.paramsP128
      Poseidon.Permute.P128Pow5T3.roundConstants round)
    state

theorem fpToZ_pow5 (value : Fp) :
    fpToZ (Poseidon.pow5 value) =
      ActionGarden.basePow5 (fpToZ value) := by
  change
    fpToZ ((value * value) * (value * value) * value) =
      ActionGarden.baseMul
        (ActionGarden.baseMul
          (ActionGarden.baseMul (fpToZ value) (fpToZ value))
          (ActionGarden.baseMul (fpToZ value) (fpToZ value)))
        (fpToZ value)
  simp only [fpToZ_mul]

theorem intToNat_ofNat (value : Nat) :
    Int.toNat (Int.ofNat value) = value := by
  rfl

theorem intToNat_roundSuccessor (value : Nat) :
    Int.toNat (Int.add (Int.ofNat value) (Int.ofNat 1)) =
      Nat.add value 1 := by
  rfl

theorem stateToZ_fullRound
    (round : Nat) (state : Poseidon.Permute.State Fp) :
    stateToZ (fieldPoseidonFullRound round state) =
      ActionGarden.poseidonFullRound poseidonParameters
        (Int.ofNat round) (stateToZ state) := by
  cases state with
  | mk x0 x1 x2 =>
      simp only [fieldPoseidonFullRound, Poseidon.FullRound.value,
        Poseidon.FullRound.params, Poseidon.FullRound.Gate.Params.mk,
        Poseidon.Permute.State.mk.injEq, stateToZ,
        ActionGarden.poseidonFullRound, poseidonParameters,
        ActionGarden.PoseidonParameters.roundConstant,
        ActionGarden.PoseidonParameters.mds,
        intToNat_ofNat, ActionGarden.matrixApply]
      simp only [← fpToZ_add, ← fpToZ_mul, ← fpToZ_pow5]

theorem stateToZ_partialPair
    (round : Nat) (state : Poseidon.Permute.State Fp) :
    stateToZ (fieldPoseidonPartialPair round state) =
      ActionGarden.poseidonPartialPair poseidonParameters
        (Int.ofNat round) (stateToZ state) := by
  cases state with
  | mk x0 x1 x2 =>
      simp only [fieldPoseidonPartialPair, Poseidon.PartialRounds.value,
        Poseidon.PartialRounds.paramsP128, Poseidon.PartialRounds.params,
        Poseidon.PartialRounds.Gate.Params.mk,
        Poseidon.PartialRounds.mid0SboxValue,
        Poseidon.Permute.State.mk.injEq, stateToZ,
        ActionGarden.poseidonPartialPair, poseidonParameters,
        ActionGarden.PoseidonParameters.roundConstant,
        ActionGarden.PoseidonParameters.mds,
        ActionGarden.zAdd, ActionGarden.zOne, intToNat_ofNat,
        intToNat_roundSuccessor,
        ActionGarden.matrixApply]
      simp only [← fpToZ_add, ← fpToZ_mul, ← fpToZ_pow5]

theorem stateToZ_foldl
    (count offset : Nat)
    (fieldStep : Nat → Poseidon.Permute.State Fp →
      Poseidon.Permute.State Fp)
    (integerStep : Nat → ActionGarden.State3 → ActionGarden.State3)
    (stepCorrespondence :
      ∀ index state,
        stateToZ (fieldStep index state) =
          integerStep index (stateToZ state))
    (initial : Poseidon.Permute.State Fp) :
    stateToZ
        (Fin.foldl count
          (fun state index => fieldStep (Nat.add index.val offset) state)
          initial) =
      ActionGarden.iterateIndexedFrom count offset
        integerStep (stateToZ initial) := by
  induction count generalizing offset initial with
  | zero =>
      simp only [Fin.foldl_zero, ActionGarden.iterateIndexedFrom]
  | succ count inductionHypothesis =>
      rw [Fin.foldl_succ]
      simp only [Fin.val_zero, Nat.zero_add]
      have shiftedStep :
          (fun (state : Poseidon.Permute.State Fp) (index : Fin count) =>
              fieldStep (Nat.add index.succ.val offset) state) =
            (fun state index =>
              fieldStep (Nat.add index.val (Nat.succ offset)) state) := by
        funext state index
        apply congrArg (fun nextIndex => fieldStep nextIndex state)
        change
          Nat.add (Nat.succ index.val) offset =
            Nat.add index.val (Nat.succ offset)
        exact
          (Nat.succ_add index.val offset).trans
            (Nat.add_succ index.val offset).symm
      rw [shiftedStep]
      rw [show Nat.add 0 offset = offset from Nat.zero_add offset]
      rw [inductionHypothesis (Nat.succ offset)
        (fieldStep offset initial)]
      rw [ActionGarden.iterateIndexedFrom]
      rw [stepCorrespondence]

set_option maxRecDepth 100000 in
theorem stateToZ_poseidonPermute
    (state : Poseidon.Permute.State Fp) :
    stateToZ
        (Poseidon.Permute.value
          Poseidon.Permute.P128Pow5T3.roundConstants state) =
      ActionGarden.poseidonPermute poseidonParameters (stateToZ state) := by
  have firstCorrespondence :
      stateToZ
          (Fin.foldl 4
            (fun value index => fieldPoseidonFullRound index.val value)
            state) =
        ActionGarden.iterateIndexedFrom 4 0
          (fun index value =>
            ActionGarden.poseidonFullRound poseidonParameters
              (Int.ofNat index) value)
          (stateToZ state) := by
    exact
      stateToZ_foldl 4 0
        fieldPoseidonFullRound
        (fun index value =>
          ActionGarden.poseidonFullRound poseidonParameters
            (Int.ofNat index) value)
        stateToZ_fullRound state
  have partialCorrespondence :
      stateToZ
          (Fin.foldl 28
            (fun value index =>
              fieldPoseidonPartialPair
                (Nat.add 4 (Nat.mul 2 index.val)) value)
            (Fin.foldl 4
              (fun value index => fieldPoseidonFullRound index.val value)
              state)) =
        ActionGarden.iterateIndexedFrom 28 0
          (fun index value =>
            ActionGarden.poseidonPartialPair poseidonParameters
              (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
          (ActionGarden.iterateIndexedFrom 4 0
            (fun index value =>
              ActionGarden.poseidonFullRound poseidonParameters
                (Int.ofNat index) value)
            (stateToZ state)) := by
    have mapped := stateToZ_foldl 28 0
      (fun index =>
        fieldPoseidonPartialPair (Nat.add 4 (Nat.mul 2 index)))
      (fun index value =>
        ActionGarden.poseidonPartialPair poseidonParameters
          (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
      (fun index value =>
        stateToZ_partialPair (Nat.add 4 (Nat.mul 2 index)) value)
      (Fin.foldl 4
        (fun value index => fieldPoseidonFullRound index.val value)
        state)
    rw [firstCorrespondence] at mapped
    exact mapped
  have finalCorrespondence :
      stateToZ
          (Fin.foldl 4
            (fun value index =>
              fieldPoseidonFullRound (Nat.add 60 index.val) value)
            (Fin.foldl 28
              (fun value index =>
                fieldPoseidonPartialPair
                  (Nat.add 4 (Nat.mul 2 index.val)) value)
              (Fin.foldl 4
                (fun value index => fieldPoseidonFullRound index.val value)
                state))) =
        ActionGarden.iterateIndexedFrom 4 0
          (fun index value =>
            ActionGarden.poseidonFullRound poseidonParameters
              (Int.ofNat (Nat.add 60 index)) value)
          (ActionGarden.iterateIndexedFrom 28 0
            (fun index value =>
              ActionGarden.poseidonPartialPair poseidonParameters
                (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
            (ActionGarden.iterateIndexedFrom 4 0
              (fun index value =>
                ActionGarden.poseidonFullRound poseidonParameters
                  (Int.ofNat index) value)
              (stateToZ state))) := by
    have mapped := stateToZ_foldl 4 0
      (fun index => fieldPoseidonFullRound (Nat.add 60 index))
      (fun index value =>
        ActionGarden.poseidonFullRound poseidonParameters
          (Int.ofNat (Nat.add 60 index)) value)
      (fun index value =>
        stateToZ_fullRound (Nat.add 60 index) value)
      (Fin.foldl 28
        (fun value index =>
          fieldPoseidonPartialPair
            (Nat.add 4 (Nat.mul 2 index.val)) value)
        (Fin.foldl 4
          (fun value index => fieldPoseidonFullRound index.val value)
          state))
    rw [partialCorrespondence] at mapped
    exact mapped
  change
    stateToZ
        (Fin.foldl 4
          (fun value index =>
            fieldPoseidonFullRound (Nat.add 60 index.val) value)
          (Fin.foldl 28
            (fun value index =>
              fieldPoseidonPartialPair
                (Nat.add 4 (Nat.mul 2 index.val)) value)
            (Fin.foldl 4
              (fun value index => fieldPoseidonFullRound index.val value)
              state))) =
      ActionGarden.iterateIndexedFrom 4 0
        (fun index value =>
          ActionGarden.poseidonFullRound poseidonParameters
            (Int.ofNat (Nat.add 60 index)) value)
        (ActionGarden.iterateIndexedFrom 28 0
          (fun index value =>
            ActionGarden.poseidonPartialPair poseidonParameters
              (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
          (ActionGarden.iterateIndexedFrom 4 0
            (fun index value =>
              ActionGarden.poseidonFullRound poseidonParameters
                (Int.ofNat index) value)
            (stateToZ state)))
  exact finalCorrespondence

theorem fieldPoseidonHash2_unfold (left right : Fp) :
    Poseidon.Hash.ConstantLength.value #v[left, right] =
      (Poseidon.Permute.value
        Poseidon.Permute.P128Pow5T3.roundConstants
        {
          x0 := left
          x1 := right
          x2 := ((2 * 2 ^ 64 : Nat) : Fp)
        }).x0 := by
  simp [Poseidon.Hash.ConstantLength.value,
    Poseidon.Hash.ConstantLength.blockCount,
    Poseidon.Hash.ConstantLength.stepValueAt,
    Poseidon.Hash.ConstantLength.absorbPermuteValue,
    Poseidon.Hash.ConstantLength.blockValue,
    Poseidon.Hash.ConstantLength.paddedWord,
    Poseidon.Hash.ConstantLength.capacity,
    Poseidon.Permute.concreteValue,
    Poseidon.Sponge.AddInput.value,
    Poseidon.Sponge.GetOutput.value,
    Fin.foldl_succ, Fin.foldl_zero]

theorem fpToZ_poseidonCapacity :
    fpToZ (((2 * 2 ^ 64 : Nat) : Fp)) =
      ActionGarden.baseNormalize
        (ActionGarden.zMul (Int.ofNat 2)
          (ActionGarden.zPowNat (Int.ofNat 2) 64)) := by
  native_decide

theorem fpToZ_poseidonHash2 (left right : Fp) :
    fpToZ (Poseidon.Hash.ConstantLength.value #v[left, right]) =
      ActionGarden.poseidonHash2 poseidonParameters
        (fpToZ left) (fpToZ right) := by
  rw [fieldPoseidonHash2_unfold]
  have permutationCorrespondence :=
    stateToZ_poseidonPermute
      ({
        x0 := left
        x1 := right
        x2 := ((2 * 2 ^ 64 : Nat) : Fp)
      } : Poseidon.Permute.State Fp)
  have xCorrespondence :=
    congrArg ActionGarden.State3.x0 permutationCorrespondence
  unfold ActionGarden.poseidonHash2
  simp only [stateToZ] at xCorrespondence
  change
    fpToZ
        (Poseidon.Permute.value
          Poseidon.Permute.P128Pow5T3.roundConstants
          {
            x0 := left
            x1 := right
            x2 := ((2 * 2 ^ 64 : Nat) : Fp)
          }).x0 =
      (ActionGarden.poseidonPermute poseidonParameters
        {
          x0 := fpToZ left
          x1 := fpToZ right
          x2 :=
            ActionGarden.baseNormalize
              (ActionGarden.zMul (Int.ofNat 2)
                (ActionGarden.zPowNat (Int.ofNat 2) 64))
        }).x0
  rw [← fpToZ_poseidonCapacity]
  exact xCorrespondence

theorem orchardPoseidonMds_deployed :
    ActionGarden.orchardPoseidonMds =
      poseidonParameters.mds := by
  native_decide

theorem orchardPoseidonRoundConstant_deployed_nat
    (round : Nat) (roundInRange : round < 64) :
    ActionGarden.orchardPoseidonRoundConstant (Int.ofNat round) =
      poseidonParameters.roundConstant (Int.ofNat round) := by
  rw [orchardPoseidonRoundConstant_deployed
    ⟨round, roundInRange⟩]
  rfl

theorem poseidonFullRound_deployed
    (round : Nat) (roundInRange : round < 64)
    (state : ActionGarden.State3) :
    ActionGarden.poseidonFullRound
        ActionGarden.orchardPoseidonParameters
        (Int.ofNat round) state =
      ActionGarden.poseidonFullRound poseidonParameters
        (Int.ofNat round) state := by
  unfold ActionGarden.poseidonFullRound
  simp only [ActionGarden.orchardPoseidonParameters]
  rw [orchardPoseidonRoundConstant_deployed_nat round roundInRange]
  rw [orchardPoseidonMds_deployed]

theorem poseidonPartialPair_deployed
    (round : Nat) (roundInRange : round + 1 < 64)
    (state : ActionGarden.State3) :
    ActionGarden.poseidonPartialPair
        ActionGarden.orchardPoseidonParameters
        (Int.ofNat round) state =
      ActionGarden.poseidonPartialPair poseidonParameters
        (Int.ofNat round) state := by
  unfold ActionGarden.poseidonPartialPair
  simp only [ActionGarden.orchardPoseidonParameters]
  rw [orchardPoseidonRoundConstant_deployed_nat round (by omega)]
  have successor :
      ActionGarden.zAdd (Int.ofNat round) ActionGarden.zOne =
        Int.ofNat (round + 1) := by
    rfl
  rw [successor]
  rw [orchardPoseidonRoundConstant_deployed_nat
    (round + 1) roundInRange]
  rw [orchardPoseidonMds_deployed]

theorem iterateIndexedFrom_congr
    {A : Type} (count index : Nat)
    (left right : Nat → A → A) (initial : A)
    (stepsEqual :
      ∀ current,
        index ≤ current →
        current < index + count →
        ∀ state, left current state = right current state) :
    ActionGarden.iterateIndexedFrom count index left initial =
      ActionGarden.iterateIndexedFrom count index right initial := by
  induction count generalizing index initial with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      rw [ActionGarden.iterateIndexedFrom,
        ActionGarden.iterateIndexedFrom]
      rw [stepsEqual index (by omega) (by omega)]
      apply inductionHypothesis
      intro current lower upper state
      apply stepsEqual current
      · omega
      · omega

/-- The public literal Poseidon table computes the same permutation as the
Ironwood constants on all 64 protocol rounds. -/
theorem poseidonPermute_deployed
    (state : ActionGarden.State3) :
    ActionGarden.poseidonPermute
        ActionGarden.orchardPoseidonParameters state =
      ActionGarden.poseidonPermute poseidonParameters state := by
  unfold ActionGarden.poseidonPermute
  simp only [ActionGarden.iterateIndexed]
  have firstRounds :
      ActionGarden.iterateIndexedFrom 4 0
          (fun index value =>
            ActionGarden.poseidonFullRound
              ActionGarden.orchardPoseidonParameters
              (Int.ofNat index) value)
          state =
        ActionGarden.iterateIndexedFrom 4 0
          (fun index value =>
            ActionGarden.poseidonFullRound poseidonParameters
              (Int.ofNat index) value)
          state := by
    apply iterateIndexedFrom_congr
    intro current lower upper value
    apply poseidonFullRound_deployed
    omega
  rw [firstRounds]
  have partialRounds :
      ActionGarden.iterateIndexedFrom 28 0
          (fun index value =>
            ActionGarden.poseidonPartialPair
              ActionGarden.orchardPoseidonParameters
              (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
          (ActionGarden.iterateIndexedFrom 4 0
            (fun index value =>
              ActionGarden.poseidonFullRound poseidonParameters
                (Int.ofNat index) value)
            state) =
        ActionGarden.iterateIndexedFrom 28 0
          (fun index value =>
            ActionGarden.poseidonPartialPair poseidonParameters
              (Int.ofNat (Nat.add 4 (Nat.mul 2 index))) value)
          (ActionGarden.iterateIndexedFrom 4 0
            (fun index value =>
              ActionGarden.poseidonFullRound poseidonParameters
                (Int.ofNat index) value)
            state) := by
    apply iterateIndexedFrom_congr
    intro current lower upper value
    exact poseidonPartialPair_deployed
      (Nat.add 4 (Nat.mul 2 current))
      (by interval_cases current <;> norm_num) value
  rw [partialRounds]
  apply iterateIndexedFrom_congr
  intro current lower upper value
  exact poseidonFullRound_deployed
    (Nat.add 60 current)
    (by interval_cases current <;> norm_num) value

theorem poseidonHash2_deployed (left right : ActionGarden.Z) :
    ActionGarden.poseidonHash2
        ActionGarden.orchardPoseidonParameters left right =
      ActionGarden.poseidonHash2 poseidonParameters left right := by
  unfold ActionGarden.poseidonHash2
  simp only
  rw [poseidonPermute_deployed]

theorem pointXBaseEqual_pointToZ (left right : Point Fp) :
    ActionGarden.baseEqual (pointToZ left).x (pointToZ right).x =
      decide (left.x = right.x) := by
  exact baseEqual_fpToZ left.x right.x

theorem incompleteAdd_some_components
    {left right result : Point Fp}
    (defined : left ⸭ right = some result) :
    left ≠ 0 ∧
      right ≠ 0 ∧
      left.x ≠ right.x ∧
      result = left + right := by
  rw [Point.incompleteAdd_def] at defined
  by_cases invalid :
      left = 0 ∨ right = 0 ∨ left.x = right.x
  · simp only [invalid, ↓reduceIte, reduceCtorEq] at defined
  · simp only [invalid, ↓reduceIte, Option.some.injEq] at defined
    push_neg at invalid
    exact ⟨invalid.1, invalid.2.1, invalid.2.2, defined.symm⟩

/-- The standalone incomplete chord formula agrees with Ironwood whenever
Ironwood's partial operation returns a point. -/
theorem pointToZ_incompleteAdd_of_some
    {left right result : Point Fp}
    (defined : left ⸭ right = some result) :
    pointToZ result =
      ActionGarden.pointAddIncomplete (pointToZ left) (pointToZ right) := by
  rcases incompleteAdd_some_components defined with
    ⟨leftNonzero, rightNonzero, xDistinct, resultEquality⟩
  subst result
  rw [← Point.nondegenerateAdd_eq_add leftNonzero rightNonzero xDistinct]
  have slopeEquality :
      (right.y - left.y) * (right.x - left.x)⁻¹ =
        (left.y - right.y) * (left.x - right.x)⁻¹ := by
    rw [show left.y - right.y = -(right.y - left.y) by ring]
    rw [show left.x - right.x = -(right.x - left.x) by ring]
    rw [inv_neg]
    ring
  unfold Point.nondegenerateAdd ActionGarden.pointAddIncomplete
  simp only [pointToZ, div_eq_mul_inv]
  simp only [← fpToZ_sub, ← fpToZ_mul, ← fpToZ_div]
  rw [← slopeEquality]

theorem pointIdentityGarden_pointToZ (point : Point Fp) :
    ActionGarden.pointIdentityGarden (pointToZ point) ↔ point = 0 := by
  unfold ActionGarden.pointIdentityGarden
  simp only [pointToZ]
  rw [← fpToZ_zero]
  constructor
  · intro coordinates
    apply Point.ext_coords
    simp only [Point.coords, Point.zero_def]
    exact Prod.ext
      (fpToZ_injective coordinates.1)
      (fpToZ_injective coordinates.2)
  · intro identity
    subst point
    exact ⟨rfl, rfl⟩

theorem sinsemillaStep_of_doubleAndAdd
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (chunk : Nat) (accumulator result : Point Fp)
    (defined :
      Point.doubleAndAdd accumulator (G.S chunk) = some result) :
    ProofCore.sinsemillaStep (parameters G B)
        (pointToZ accumulator) (Int.ofNat chunk) =
      pointToZ result ∧
    ProofCore.sinsemillaStepDefined (parameters G B)
      (pointToZ accumulator) (Int.ofNat chunk) := by
  unfold Point.doubleAndAdd at defined
  cases firstResult :
      accumulator ⸭ G.S chunk with
  | none =>
      simp only [firstResult, Option.bind_none, reduceCtorEq] at defined
      simp at defined
  | some intermediate =>
      simp only [firstResult, Option.bind_some] at defined
      have firstComponents :=
        incompleteAdd_some_components firstResult
      have secondComponents :=
        incompleteAdd_some_components defined
      rcases firstComponents with
        ⟨accumulatorNonzero, generatorNonzero,
          firstXDistinct, intermediateEquality⟩
      rcases secondComponents with
        ⟨intermediateNonzero, accumulatorNonzeroAgain,
          secondXDistinct, resultEquality⟩
      subst intermediate
      subst result
      constructor
      · unfold ProofCore.sinsemillaStep parameters
        simp only [intToNat_ofNat]
        rw [← pointToZ_add, ← pointToZ_add]
      · unfold ProofCore.sinsemillaStepDefined parameters
        simp only [intToNat_ofNat]
        rw [pointIsIdentity_pointToZ, pointIsIdentity_pointToZ]
        rw [pointXBaseEqual_pointToZ]
        rw [show
          ActionGarden.pointAdd
              (pointToZ accumulator) (pointToZ (G.S chunk)) =
            pointToZ (accumulator + G.S chunk) from
          (pointToZ_add accumulator (G.S chunk)).symm]
        rw [pointIsIdentity_pointToZ]
        rw [pointXBaseEqual_pointToZ]
        simp only [accumulatorNonzero, generatorNonzero,
          firstXDistinct, intermediateNonzero, secondXDistinct,
          decide_false, Bool.false_eq_true, not_false_eq_true]
        simp

/-- Standalone step definedness is also sufficient for Ironwood's two
incomplete additions to succeed.  This is the reverse direction of
`sinsemillaStep_of_doubleAndAdd`. -/
theorem doubleAndAdd_of_sinsemillaStepDefined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (chunk : Nat) (accumulator : Point Fp)
    (defined :
      ProofCore.sinsemillaStepDefined (parameters G B)
        (pointToZ accumulator) (Int.ofNat chunk)) :
    Point.doubleAndAdd accumulator (G.S chunk) =
      some (accumulator + G.S chunk + accumulator) := by
  unfold ProofCore.sinsemillaStepDefined at defined
  simp only [parameters, intToNat_ofNat] at defined
  rw [pointIsIdentity_pointToZ, pointIsIdentity_pointToZ] at defined
  rw [pointXBaseEqual_pointToZ] at defined
  rw [show
    ActionGarden.pointAdd
        (pointToZ accumulator) (pointToZ (G.S chunk)) =
      pointToZ (accumulator + G.S chunk) from
    (pointToZ_add accumulator (G.S chunk)).symm] at defined
  rw [pointIsIdentity_pointToZ] at defined
  rw [pointXBaseEqual_pointToZ] at defined
  simp only [decide_eq_false_iff_not] at defined
  rcases defined with
    ⟨accumulatorNonzero, generatorNonzero, firstXDistinct,
     intermediateNonzero, secondXDistinct⟩
  unfold Point.doubleAndAdd
  rw [Point.incompleteAdd_some
    accumulatorNonzero generatorNonzero firstXDistinct]
  exact
    Point.incompleteAdd_some
      intermediateNonzero accumulatorNonzero secondXDistinct

theorem sinsemillaFold_none
    (S : Nat → Point Fp) (chunks : List Nat) :
    List.foldl
        (fun accumulator chunk =>
          Option.bind accumulator (Specs.Sinsemilla.step S chunk))
        none chunks =
      none := by
  induction chunks with
  | nil =>
      rfl
  | cons chunk rest inductionHypothesis =>
      simp only [List.foldl_cons, Option.bind_none]
      exact inductionHypothesis

theorem sinsemillaFold_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (chunks : List Nat) (accumulator result : Point Fp)
    (defined :
      List.foldl
          (fun current chunk =>
            Option.bind current (Specs.Sinsemilla.step G.S chunk))
          (some accumulator) chunks =
        some result) :
    ProofCore.sinsemillaHashToPoint (parameters G B)
        (pointToZ accumulator) (List.map Int.ofNat chunks) =
      pointToZ result ∧
    ProofCore.sinsemillaHashDefinedFrom (parameters G B)
      (pointToZ accumulator) (List.map Int.ofNat chunks) := by
  induction chunks generalizing accumulator with
  | nil =>
      simp only [List.foldl_nil, Option.some.injEq] at defined
      subst result
      exact ⟨rfl, True.intro⟩
  | cons chunk rest inductionHypothesis =>
      simp only [List.foldl_cons, Option.bind_some] at defined
      cases stepResult :
          Specs.Sinsemilla.step G.S chunk accumulator with
      | none =>
          rw [stepResult, sinsemillaFold_none] at defined
          contradiction
      | some nextAccumulator =>
          rw [stepResult] at defined
          have remaining :=
            inductionHypothesis nextAccumulator defined
          have step :=
            sinsemillaStep_of_doubleAndAdd G B chunk accumulator
              nextAccumulator stepResult
          constructor
          · simp only [List.map_cons,
              ProofCore.sinsemillaHashToPoint, List.foldl_cons]
            rw [step.1]
            exact remaining.1
          · simp only [List.map_cons,
              ProofCore.sinsemillaHashDefinedFrom]
            constructor
            · exact step.2
            · rw [step.1]
              exact remaining.2

/-- A structurally defined standalone Sinsemilla fold has a corresponding
successful Ironwood `Option` result. -/
theorem sinsemillaFold_of_defined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (chunks : List Nat) (accumulator : Point Fp)
    (defined :
      ProofCore.sinsemillaHashDefinedFrom (parameters G B)
        (pointToZ accumulator) (List.map Int.ofNat chunks)) :
    ∃ result : Point Fp,
        List.foldl
            (fun current chunk =>
              Option.bind current (Specs.Sinsemilla.step G.S chunk))
            (some accumulator) chunks =
          some result ∧
        ProofCore.sinsemillaHashToPoint (parameters G B)
            (pointToZ accumulator) (List.map Int.ofNat chunks)
          = pointToZ result := by
  induction chunks generalizing accumulator with
  | nil =>
      exact ⟨accumulator, rfl, rfl⟩
  | cons chunk rest inductionHypothesis =>
      simp only [List.map_cons,
        ProofCore.sinsemillaHashDefinedFrom] at defined
      let nextAccumulator := accumulator + G.S chunk + accumulator
      have stepDefined :=
        doubleAndAdd_of_sinsemillaStepDefined G B chunk accumulator
          defined.1
      have stepCorrespondence :
          ProofCore.sinsemillaStep (parameters G B)
              (pointToZ accumulator) (Int.ofNat chunk) =
            pointToZ nextAccumulator := by
        unfold nextAccumulator ProofCore.sinsemillaStep
        simp only [parameters, intToNat_ofNat]
        rw [← pointToZ_add, ← pointToZ_add]
      have restDefined :
          ProofCore.sinsemillaHashDefinedFrom (parameters G B)
            (pointToZ nextAccumulator) (List.map Int.ofNat rest) := by
        rw [← stepCorrespondence]
        exact defined.2
      rcases inductionHypothesis nextAccumulator restDefined with
        ⟨result, foldSucceeds, foldCorrespondence⟩
      refine ⟨result, ?_, ?_⟩
      · simp only [List.foldl_cons, Option.bind_some]
        rw [show
          Specs.Sinsemilla.step G.S chunk accumulator =
            some nextAccumulator from stepDefined]
        exact foldSucceeds
      · simp only [List.map_cons,
          ProofCore.sinsemillaHashToPoint, List.foldl_cons]
        rw [stepCorrespondence]
        exact foldCorrespondence

/-- Standalone hash definedness is equivalent to existence of a successful
Ironwood hash point; this lemma supplies the reverse/existence direction. -/
theorem sinsemillaHashToPoint_of_defined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (domain : Point Fp) (chunks : List Nat)
    (defined :
      ProofCore.sinsemillaHashDefined (parameters G B)
        (pointToZ domain) (List.map Int.ofNat chunks)) :
    ∃ result : Point Fp,
      Specs.Sinsemilla.hashToPoint G.S domain chunks = some result ∧
        ProofCore.sinsemillaHashToPoint (parameters G B)
            (pointToZ domain) (List.map Int.ofNat chunks)
          = pointToZ result := by
  exact sinsemillaFold_of_defined G B chunks domain defined

theorem sinsemillaHashToPoint_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (domain result : Point Fp) (chunks : List Nat)
    (defined :
      Specs.Sinsemilla.hashToPoint G.S domain chunks = some result) :
    ProofCore.sinsemillaHashToPoint (parameters G B)
        (pointToZ domain) (List.map Int.ofNat chunks) =
      pointToZ result ∧
    ProofCore.sinsemillaHashDefined (parameters G B)
      (pointToZ domain) (List.map Int.ofNat chunks) := by
  exact sinsemillaFold_of_some G B chunks domain result defined

/-- A defined deployed Sinsemilla round has the same result in the public
Garden-shaped formula and the proof-only complete-addition model. -/
theorem sinsemillaRound_of_coreDefined
    (chunk : Nat) (chunkInRange : chunk < 1024)
    (accumulator : Point Fp)
    (defined :
      ProofCore.sinsemillaStepDefined
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (Int.ofNat chunk)) :
    ActionGarden.sinsemillaRound
        (pointToZ accumulator) (Int.ofNat chunk) =
      ProofCore.sinsemillaStep
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (Int.ofNat chunk) ∧
    ActionGarden.sinsemillaRoundDefined
      (pointToZ accumulator) (Int.ofNat chunk) := by
  have succeeds :
      Point.doubleAndAdd accumulator
          (Specs.Sinsemilla.orchardGenerators.S chunk) =
        some
          (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
            accumulator) := by
    exact doubleAndAdd_of_sinsemillaStepDefined
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases chunk accumulator defined
  unfold Point.doubleAndAdd at succeeds
  cases firstResult :
      accumulator ⸭ Specs.Sinsemilla.orchardGenerators.S chunk with
  | none =>
      simp [firstResult] at succeeds
  | some intermediate =>
      simp [firstResult] at succeeds
      have generatorEquality :=
        orchardSinsemillaGenerator_deployed
          ⟨chunk, chunkInRange⟩
      have firstCorrespondence :=
        pointToZ_incompleteAdd_of_some firstResult
      have secondCorrespondence :=
        pointToZ_incompleteAdd_of_some succeeds
      have firstComponents :=
        incompleteAdd_some_components firstResult
      have secondComponents :=
        incompleteAdd_some_components succeeds
      rcases firstComponents with
        ⟨accumulatorNonzero, generatorNonzero,
          firstXDistinct, intermediateEquality⟩
      rcases secondComponents with
        ⟨intermediateNonzero, accumulatorNonzeroAgain,
          secondXDistinct, resultEquality⟩
      constructor
      · unfold ActionGarden.sinsemillaRound
        rw [generatorEquality]
        rw [← firstCorrespondence, ← secondCorrespondence]
        have coreCorrespondence :=
          (sinsemillaStep_of_doubleAndAdd
            Specs.Sinsemilla.orchardGenerators
            Zcash.Circuits.Action.orchardBases
            chunk accumulator
              (accumulator +
                Specs.Sinsemilla.orchardGenerators.S chunk +
                accumulator))
            (by
              unfold Point.doubleAndAdd
              rw [firstResult]
              exact succeeds)
        exact coreCorrespondence.1.symm
      · unfold ActionGarden.sinsemillaRoundDefined
        simp only [generatorEquality]
        rw [← firstCorrespondence]
        constructor
        · exact (pointIdentityGarden_pointToZ accumulator).not.mpr
            accumulatorNonzero
        constructor
        · exact
            (pointIdentityGarden_pointToZ
              (Specs.Sinsemilla.orchardGenerators.S chunk)).not.mpr
            generatorNonzero
        constructor
        · simp only [pointToZ, baseNormalize_fpToZ]
          exact fun equality => firstXDistinct (fpToZ_injective equality)
        constructor
        · exact (pointIdentityGarden_pointToZ intermediate).not.mpr
            intermediateNonzero
        · simp only [pointToZ, baseNormalize_fpToZ]
          exact fun equality => secondXDistinct (fpToZ_injective equality)

/-- Conversely, public Garden round definedness reconstructs both successful
Ironwood incomplete additions and hence the proof-only round condition. -/
theorem coreDefined_of_sinsemillaRoundDefined
    (chunk : Nat) (chunkInRange : chunk < 1024)
    (accumulator : Point Fp)
    (defined :
      ActionGarden.sinsemillaRoundDefined
        (pointToZ accumulator) (Int.ofNat chunk)) :
    ProofCore.sinsemillaStepDefined
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (Int.ofNat chunk) ∧
      ActionGarden.sinsemillaRound
          (pointToZ accumulator) (Int.ofNat chunk) =
        ProofCore.sinsemillaStep
          (parameters Specs.Sinsemilla.orchardGenerators
            Zcash.Circuits.Action.orchardBases)
          (pointToZ accumulator) (Int.ofNat chunk) := by
  have generatorEquality :=
    orchardSinsemillaGenerator_deployed
      ⟨chunk, chunkInRange⟩
  unfold ActionGarden.sinsemillaRoundDefined at defined
  simp only [generatorEquality] at defined
  have accumulatorNonzero :
      accumulator ≠ 0 :=
    (pointIdentityGarden_pointToZ accumulator).not.mp defined.1
  have generatorNonzero :
      Specs.Sinsemilla.orchardGenerators.S chunk ≠ 0 :=
    (pointIdentityGarden_pointToZ
      (Specs.Sinsemilla.orchardGenerators.S chunk)).not.mp
      defined.2.1
  have firstXDistinct :
      accumulator.x ≠
        (Specs.Sinsemilla.orchardGenerators.S chunk).x := by
    intro equality
    apply defined.2.2.1
    simp only [pointToZ, baseNormalize_fpToZ]
    exact congrArg fpToZ equality
  have firstSucceeds :
      accumulator ⸭ Specs.Sinsemilla.orchardGenerators.S chunk =
        some
          (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk) :=
    Point.incompleteAdd_some
      accumulatorNonzero generatorNonzero firstXDistinct
  have firstCorrespondence :=
    pointToZ_incompleteAdd_of_some firstSucceeds
  rw [← firstCorrespondence] at defined
  have intermediateNonzero :
      accumulator + Specs.Sinsemilla.orchardGenerators.S chunk ≠ 0 :=
    (pointIdentityGarden_pointToZ
      (accumulator +
        Specs.Sinsemilla.orchardGenerators.S chunk)).not.mp
      defined.2.2.2.1
  have secondXDistinct :
      (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk).x ≠
        accumulator.x := by
    intro equality
    apply defined.2.2.2.2
    simp only [pointToZ, baseNormalize_fpToZ]
    exact congrArg fpToZ equality
  have secondSucceeds :
      (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk) ⸭
          accumulator =
        some
          (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
            accumulator) :=
    Point.incompleteAdd_some
      intermediateNonzero accumulatorNonzero secondXDistinct
  have doubleAndAddSucceeds :
      Point.doubleAndAdd accumulator
          (Specs.Sinsemilla.orchardGenerators.S chunk) =
        some
          (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
            accumulator) := by
    unfold Point.doubleAndAdd
    rw [firstSucceeds]
    exact secondSucceeds
  have coreCorrespondence :=
    sinsemillaStep_of_doubleAndAdd
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases chunk accumulator
      (accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
        accumulator)
      doubleAndAddSucceeds
  constructor
  · exact coreCorrespondence.2
  · unfold ActionGarden.sinsemillaRound
    rw [generatorEquality]
    rw [← firstCorrespondence]
    rw [← pointToZ_incompleteAdd_of_some secondSucceeds]
    exact coreCorrespondence.1.symm

/-- A proof-only defined fold transports to the public Garden fold. -/
theorem sinsemillaHashGarden_of_coreDefined
    (chunks : List Nat) (accumulator : Point Fp)
    (chunksInRange : ∀ chunk ∈ chunks, chunk < 1024)
    (defined :
      ProofCore.sinsemillaHashDefinedFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (List.map Int.ofNat chunks)) :
    ActionGarden.sinsemillaHashToPointGarden
        (pointToZ accumulator) (List.map Int.ofNat chunks) =
      ProofCore.sinsemillaHashToPoint
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (List.map Int.ofNat chunks) ∧
    ActionGarden.sinsemillaHashDefinedFromGarden
      (pointToZ accumulator) (List.map Int.ofNat chunks) := by
  induction chunks generalizing accumulator with
  | nil =>
      exact ⟨rfl, True.intro⟩
  | cons chunk rest inductionHypothesis =>
      simp only [List.map_cons,
        ProofCore.sinsemillaHashDefinedFrom] at defined
      have chunkInRange := chunksInRange chunk (by simp)
      have step :=
        sinsemillaRound_of_coreDefined
          chunk chunkInRange accumulator defined.1
      let nextAccumulator :=
        accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
          accumulator
      have coreStep :
          ProofCore.sinsemillaStep
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (pointToZ accumulator) (Int.ofNat chunk) =
            pointToZ nextAccumulator := by
        unfold nextAccumulator ProofCore.sinsemillaStep
        simp only [parameters, intToNat_ofNat]
        rw [← pointToZ_add, ← pointToZ_add]
      have remainingDefined :
          ProofCore.sinsemillaHashDefinedFrom
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (pointToZ nextAccumulator)
              (List.map Int.ofNat rest) := by
        rw [← coreStep]
        exact defined.2
      have remaining :=
        inductionHypothesis nextAccumulator
          (fun item itemInRest =>
            chunksInRange item (by simp [itemInRest]))
          remainingDefined
      constructor
      · change
          ActionGarden.sinsemillaHashToPointGarden
              (ActionGarden.sinsemillaRound
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest) =
            ProofCore.sinsemillaHashToPoint
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (ProofCore.sinsemillaStep
                (parameters Specs.Sinsemilla.orchardGenerators
                  Zcash.Circuits.Action.orchardBases)
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest)
        rw [step.1, coreStep, remaining.1]
      · change
          ActionGarden.sinsemillaRoundDefined
              (pointToZ accumulator) (Int.ofNat chunk) ∧
            ActionGarden.sinsemillaHashDefinedFromGarden
              (ActionGarden.sinsemillaRound
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest)
        constructor
        · exact step.2
        · rw [step.1, coreStep]
          exact remaining.2

/-- Public Garden fold definedness transports back to the proof-only fold,
while preserving the total fold result. -/
theorem coreDefined_of_sinsemillaHashGarden
    (chunks : List Nat) (accumulator : Point Fp)
    (chunksInRange : ∀ chunk ∈ chunks, chunk < 1024)
    (defined :
      ActionGarden.sinsemillaHashDefinedFromGarden
        (pointToZ accumulator) (List.map Int.ofNat chunks)) :
    ProofCore.sinsemillaHashDefinedFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (List.map Int.ofNat chunks) ∧
    ActionGarden.sinsemillaHashToPointGarden
        (pointToZ accumulator) (List.map Int.ofNat chunks) =
      ProofCore.sinsemillaHashToPoint
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (pointToZ accumulator) (List.map Int.ofNat chunks) := by
  induction chunks generalizing accumulator with
  | nil =>
      exact ⟨True.intro, rfl⟩
  | cons chunk rest inductionHypothesis =>
      simp only [List.map_cons,
        ActionGarden.sinsemillaHashDefinedFromGarden] at defined
      have chunkInRange := chunksInRange chunk (by simp)
      have step :=
        coreDefined_of_sinsemillaRoundDefined
          chunk chunkInRange accumulator defined.1
      let nextAccumulator :=
        accumulator + Specs.Sinsemilla.orchardGenerators.S chunk +
          accumulator
      have coreStep :
          ProofCore.sinsemillaStep
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (pointToZ accumulator) (Int.ofNat chunk) =
            pointToZ nextAccumulator := by
        unfold nextAccumulator ProofCore.sinsemillaStep
        simp only [parameters, intToNat_ofNat]
        rw [← pointToZ_add, ← pointToZ_add]
      have publicStep :
          ActionGarden.sinsemillaRound
              (pointToZ accumulator) (Int.ofNat chunk) =
            pointToZ nextAccumulator :=
        step.2.trans coreStep
      have remainingDefined :
          ActionGarden.sinsemillaHashDefinedFromGarden
            (pointToZ nextAccumulator) (List.map Int.ofNat rest) := by
        rw [← publicStep]
        exact defined.2
      have remaining :=
        inductionHypothesis nextAccumulator
          (fun item itemInRest =>
            chunksInRange item (by simp [itemInRest]))
          remainingDefined
      constructor
      · change
          ProofCore.sinsemillaStepDefined
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (pointToZ accumulator) (Int.ofNat chunk) ∧
            ProofCore.sinsemillaHashDefinedFrom
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (ProofCore.sinsemillaStep
                (parameters Specs.Sinsemilla.orchardGenerators
                  Zcash.Circuits.Action.orchardBases)
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest)
        exact ⟨step.1, by rw [coreStep]; exact remaining.1⟩
      · change
          ActionGarden.sinsemillaHashToPointGarden
              (ActionGarden.sinsemillaRound
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest) =
            ProofCore.sinsemillaHashToPoint
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (ProofCore.sinsemillaStep
                (parameters Specs.Sinsemilla.orchardGenerators
                  Zcash.Circuits.Action.orchardBases)
                (pointToZ accumulator) (Int.ofNat chunk))
              (List.map Int.ofNat rest)
        rw [publicStep, coreStep, remaining.2]

theorem chunksOf_ofNat (value count : Nat) :
    ProofCore.chunksOf (Int.ofNat value) (Int.ofNat count) =
      List.map Int.ofNat (Specs.Sinsemilla.chunksOf value count) := by
  unfold ProofCore.chunksOf Specs.Sinsemilla.chunksOf
  rw [intToNat_ofNat]
  simp only [List.map_map]
  apply List.map_congr_left
  intro index indexInRange
  unfold Specs.bitrange Specs.K
  unfold ActionGarden.zMod ActionGarden.zDiv ActionGarden.zPowNat ActionGarden.zTwo
  rfl

theorem chunksOf_mem_lt_1024
    {value count chunk : Nat}
    (membership : chunk ∈ Specs.Sinsemilla.chunksOf value count) :
    chunk < 1024 := by
  simpa [Specs.K] using
    (Specs.Sinsemilla.chunksOf_mem_lt membership)

/-- A successful deployed Ironwood hash gives the public Garden hash result
and public round-definedness, provided its words index the 1,024-row table. -/
theorem sinsemillaHashGarden_of_some
    (domain result : Point Fp) (chunks : List Nat)
    (chunksInRange : ∀ chunk ∈ chunks, chunk < 1024)
    (defined :
      Specs.Sinsemilla.hashToPoint
          Specs.Sinsemilla.orchardGenerators.S domain chunks =
        some result) :
    ActionGarden.sinsemillaHashToPointGarden
        (pointToZ domain) (List.map Int.ofNat chunks) =
      pointToZ result ∧
    ActionGarden.sinsemillaHashDefinedGarden
      (pointToZ domain) (List.map Int.ofNat chunks) := by
  have core :=
    sinsemillaHashToPoint_of_some
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases
      domain result chunks defined
  have garden :=
    sinsemillaHashGarden_of_coreDefined chunks domain
      chunksInRange core.2
  exact ⟨garden.1.trans core.1, garden.2⟩

/-- Public deployed hash definedness reconstructs a successful Ironwood hash
and proves that both total folds return the same represented point. -/
theorem sinsemillaHashSome_of_gardenDefined
    (domain : Point Fp) (chunks : List Nat)
    (chunksInRange : ∀ chunk ∈ chunks, chunk < 1024)
    (defined :
      ActionGarden.sinsemillaHashDefinedGarden
        (pointToZ domain) (List.map Int.ofNat chunks)) :
    ∃ result : Point Fp,
      Specs.Sinsemilla.hashToPoint
          Specs.Sinsemilla.orchardGenerators.S domain chunks =
        some result ∧
      ActionGarden.sinsemillaHashToPointGarden
          (pointToZ domain) (List.map Int.ofNat chunks) =
        pointToZ result := by
  have garden :=
    coreDefined_of_sinsemillaHashGarden chunks domain
      chunksInRange defined
  rcases
      sinsemillaHashToPoint_of_defined
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        domain chunks garden.1 with
    ⟨result, succeeds, coreResult⟩
  exact ⟨result, succeeds, garden.2.trans coreResult⟩

/-- The recursive Garden-style encoder and Ironwood's indexed chunk encoder
produce the same ten-bit words on nonnegative protocol messages. -/
theorem wordsLe_ofNat (count value : Nat) :
    ActionGarden.wordsLe count (Int.ofNat value) =
      List.map Int.ofNat (Specs.Sinsemilla.chunksOf value count) := by
  induction count generalizing value with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have chunksSucc :
          Specs.Sinsemilla.chunksOf value (Nat.succ count) =
            value % 1024 ::
              Specs.Sinsemilla.chunksOf (value / 1024) count := by
        rw [show Nat.succ count = 1 + count by omega]
        rw [Specs.Sinsemilla.chunksOf_add]
        simp [Specs.Sinsemilla.chunksOf, Specs.bitrange, Specs.K]
      rw [chunksSucc, List.map_cons]
      simp only [ActionGarden.wordsLe]
      have radix :
          ActionGarden.zPowNat ActionGarden.zTwo 10 =
            Int.ofNat 1024 := by native_decide
      rw [radix]
      unfold ActionGarden.zMod ActionGarden.zDiv
      have modEq :
          (Int.ofNat value).emod (Int.ofNat 1024) =
            Int.ofNat (value % 1024) :=
        (Int.natCast_emod value 1024).symm
      have divEq :
          (Int.ofNat value).ediv (Int.ofNat 1024) =
            Int.ofNat (value / 1024) :=
        (Int.natCast_ediv value 1024).symm
      rw [modEq, divEq]
      exact congrArg (List.cons (Int.ofNat (value % 1024)))
        (inductionHypothesis (value / 1024))

theorem intMulCommExplicit (left right : Int) :
    Int.mul left right = Int.mul right left := by
  exact Int.mul_comm left right

theorem intAddZeroExplicit (value : Int) :
    Int.add value (Int.ofNat 0) = value := by
  exact Int.add_zero value

theorem pointParity_pointToZ (point : Point Fp) :
    ProofCore.pointParity (pointToZ point) =
      Int.ofNat (point.y.val % 2) := by
  unfold ProofCore.pointParity ActionGarden.zMod ActionGarden.zTwo pointToZ fpToZ
  rfl

theorem noteCommitMessage_pointToZ
    (gd pkd : Point Fp) (value rho psi : Fp) :
    ProofCore.noteCommitMessage
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi) =
      Int.ofNat
        (Specs.Sinsemilla.noteCommitMessage
          gd.x.val (gd.y.val % 2)
          pkd.x.val (pkd.y.val % 2)
          value.val rho.val psi.val) := by
  unfold ProofCore.noteCommitMessage
  rw [pointParity_pointToZ, pointParity_pointToZ]
  simp only [pointToZ]
  rw [baseNormalize_fpToZ, baseNormalize_fpToZ]
  unfold Specs.Sinsemilla.noteCommitMessage
  unfold ActionGarden.zAdd ActionGarden.zMul ActionGarden.zPowNat
  unfold fpToZ
  rfl

theorem noteCommitChunks_pointToZ
    (gd pkd : Point Fp) (value rho psi : Fp) :
    ProofCore.noteCommitChunks
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi) =
      List.map Int.ofNat
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars gd pkd value rho psi)) := by
  unfold ProofCore.noteCommitChunks
  rw [noteCommitMessage_pointToZ]
  rw [chunksOf_ofNat]
  rfl

/-- Garden's public recursive NoteCommit message encoder is exactly the
Ironwood encoder after canonical field representatives are inserted.  The
only textual difference is coefficient order in multiplication. -/
theorem noteCommitMessageGarden_pointToZ
    (gd pkd : Point Fp) (value rho psi : Fp) :
    ActionGarden.noteCommitMessageGarden
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi) =
      List.map Int.ofNat
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars gd pkd value rho psi)) := by
  have packedEquality :
      ActionGarden.zAdd
        (ActionGarden.zAdd
          (ActionGarden.zAdd
            (ActionGarden.zAdd
              (ActionGarden.zAdd
                (ActionGarden.zAdd
                  (ActionGarden.zAdd
                    (ActionGarden.zAdd
                      (ActionGarden.extractXGarden (pointToZ gd))
                      (ActionGarden.zMul
                        (ActionGarden.pointParity (pointToZ gd))
                        (ActionGarden.zPowNat ActionGarden.zTwo 255)))
                    (ActionGarden.zMul
                      (ActionGarden.extractXGarden (pointToZ pkd))
                      (ActionGarden.zPowNat ActionGarden.zTwo 256)))
                  (ActionGarden.zMul
                    (ActionGarden.pointParity (pointToZ pkd))
                    (ActionGarden.zPowNat ActionGarden.zTwo 511)))
                (ActionGarden.zMul (fpToZ value)
                  (ActionGarden.zPowNat ActionGarden.zTwo 512)))
              (ActionGarden.zMul (fpToZ rho)
                (ActionGarden.zPowNat ActionGarden.zTwo 576)))
            (ActionGarden.zMul (fpToZ psi)
              (ActionGarden.zPowNat ActionGarden.zTwo 831)))
          ActionGarden.zZero)
        ActionGarden.zZero =
      ProofCore.noteCommitMessage
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi) := by
    unfold ProofCore.noteCommitMessage ActionGarden.extractXGarden
    simp only [pointToZ]
    rw [baseNormalize_fpToZ, baseNormalize_fpToZ]
    unfold ActionGarden.pointParity ProofCore.pointParity
    unfold ActionGarden.zAdd ActionGarden.zMul ActionGarden.zZero
    rw [← intMulCommExplicit
      (ActionGarden.zMod (fpToZ gd.y) ActionGarden.zTwo)
      (ActionGarden.zPowNat ActionGarden.zTwo 255)]
    rw [← intMulCommExplicit (fpToZ pkd.x)
      (ActionGarden.zPowNat ActionGarden.zTwo 256)]
    rw [← intMulCommExplicit
      (ActionGarden.zMod (fpToZ pkd.y) ActionGarden.zTwo)
      (ActionGarden.zPowNat ActionGarden.zTwo 511)]
    rw [← intMulCommExplicit (fpToZ value)
      (ActionGarden.zPowNat ActionGarden.zTwo 512)]
    rw [← intMulCommExplicit (fpToZ rho)
      (ActionGarden.zPowNat ActionGarden.zTwo 576)]
    rw [← intMulCommExplicit (fpToZ psi)
      (ActionGarden.zPowNat ActionGarden.zTwo 831)]
    rw [intAddZeroExplicit, intAddZeroExplicit]
  unfold ActionGarden.noteCommitMessageGarden
  rw [packedEquality, noteCommitMessage_pointToZ, wordsLe_ofNat]
  rfl

theorem commitIvkMessage_fpToZ (ak nk : Fp) :
    ProofCore.commitIvkMessage (fpToZ ak) (fpToZ nk) =
      Int.ofNat (Specs.Sinsemilla.commitIvkMessage ak.val nk.val) := by
  unfold ProofCore.commitIvkMessage Specs.Sinsemilla.commitIvkMessage
  unfold ActionGarden.zAdd ActionGarden.zMul ActionGarden.zPowNat fpToZ
  rfl

theorem commitIvkChunks_fpToZ (ak nk : Fp) :
    ProofCore.commitIvkChunks (fpToZ ak) (fpToZ nk) =
      List.map Int.ofNat
        (Specs.Sinsemilla.commitIvkChunks ak.val nk.val) := by
  unfold ProofCore.commitIvkChunks
  rw [commitIvkMessage_fpToZ]
  rw [chunksOf_ofNat]
  unfold Specs.Sinsemilla.commitIvkChunks
  rfl

/-- Public Garden-shaped IVK words coincide with Ironwood's IVK chunks. -/
theorem commitIvkMessageGarden_fpToZ (ak nk : Fp) :
    ActionGarden.commitIvkMessageGarden (fpToZ ak) (fpToZ nk) =
      List.map Int.ofNat
        (Specs.Sinsemilla.commitIvkChunks ak.val nk.val) := by
  have packedEquality :
      ActionGarden.zAdd (fpToZ ak)
          (ActionGarden.zMul (fpToZ nk)
            (ActionGarden.zPowNat ActionGarden.zTwo 255)) =
        ProofCore.commitIvkMessage (fpToZ ak) (fpToZ nk) := by
    unfold ProofCore.commitIvkMessage
    unfold ActionGarden.zAdd ActionGarden.zMul
    rw [← intMulCommExplicit (fpToZ nk)
      (ActionGarden.zPowNat ActionGarden.zTwo 255)]
  unfold ActionGarden.commitIvkMessageGarden
  rw [packedEquality, commitIvkMessage_fpToZ, wordsLe_ofNat]
  unfold Specs.Sinsemilla.commitIvkChunks
  rfl

theorem merkleChunks_eq_chunksOf (layer left right : Nat) :
    Specs.Sinsemilla.merkleChunks layer left right =
      Specs.Sinsemilla.chunksOf
        (layer + 2 ^ 10 * left + 2 ^ 265 * right) 52 := by
  rfl

theorem merkleMessage_ofNat (layer left right : Nat) :
    ProofCore.merkleMessage
        (Int.ofNat layer) (Int.ofNat left) (Int.ofNat right) =
      Int.ofNat (layer + 2 ^ 10 * left + 2 ^ 265 * right) := by
  unfold ProofCore.merkleMessage ActionGarden.zAdd ActionGarden.zMul
  unfold ActionGarden.zPowNat ActionGarden.zTwo
  norm_num
  rw [Int.add_assoc]

theorem merkleChunks_ofNat (layer left right : Nat) :
    ProofCore.merkleChunks
        (Int.ofNat layer) (Int.ofNat left) (Int.ofNat right) =
      List.map Int.ofNat
        (Specs.Sinsemilla.merkleChunks layer left right) := by
  unfold ProofCore.merkleChunks
  rw [merkleMessage_ofNat]
  rw [chunksOf_ofNat]
  rw [merkleChunks_eq_chunksOf]

/-- Public Garden-shaped Merkle words coincide with Ironwood's Merkle chunks.
The explicit layer stored by Garden is the natural-number layer supplied to
Ironwood's implicit path fold. -/
theorem merkleMessageGarden_ofNat (layer left right : Nat) :
    ActionGarden.merkleMessageGarden
        (Int.ofNat layer) (Int.ofNat left) (Int.ofNat right) =
      List.map Int.ofNat
        (Specs.Sinsemilla.merkleChunks layer left right) := by
  have packedEquality :
      ActionGarden.zAdd (Int.ofNat layer)
          (ActionGarden.zAdd
            (ActionGarden.zMul (Int.ofNat left)
              (ActionGarden.zPowNat ActionGarden.zTwo 10))
            (ActionGarden.zMul (Int.ofNat right)
              (ActionGarden.zPowNat ActionGarden.zTwo 265))) =
        ProofCore.merkleMessage
          (Int.ofNat layer) (Int.ofNat left) (Int.ofNat right) := by
    unfold ProofCore.merkleMessage
    unfold ActionGarden.zAdd ActionGarden.zMul
    rw [← intMulCommExplicit (Int.ofNat left)
      (ActionGarden.zPowNat ActionGarden.zTwo 10)]
    rw [← intMulCommExplicit (Int.ofNat right)
      (ActionGarden.zPowNat ActionGarden.zTwo 265)]
  unfold ActionGarden.merkleMessageGarden
  rw [packedEquality, merkleMessage_ofNat, wordsLe_ofNat]
  rw [merkleChunks_eq_chunksOf]

theorem merkleStep_pointToZ_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (layer : Nat) (node sibling position : Fp)
    (hashPoint : Point Fp)
    (hashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.merkleQ
        (Sinsemilla.Merkle.proverChunks layer node sibling
          (position = (1 : Fp))) =
        some hashPoint) :
    ProofCore.merkleStep (parameters G B)
          (Int.ofNat layer) (fpToZ node)
          (pathElementOf (sibling, position)) =
      fpToZ hashPoint.x ∧
    ProofCore.merkleStepDefined (parameters G B)
      (Int.ofNat layer) (fpToZ node)
      (pathElementOf (sibling, position)) := by
  have correspondence :=
    sinsemillaHashToPoint_of_some G B B.merkleQ hashPoint
      (Sinsemilla.Merkle.proverChunks layer node sibling
        (position = (1 : Fp)))
      hashDefined
  by_cases positionIsRight : position = (1 : Fp)
  · simp only [Sinsemilla.Merkle.proverChunks, positionIsRight,
      decide_true, Bool.true_eq, Bool.true_eq_false, Bool.false_eq_true,
      ↓reduceIte] at correspondence
    rw [← merkleChunks_ofNat] at correspondence
    constructor
    · unfold ProofCore.merkleStep ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_true, ↓reduceIte]
      simp only [parameters]
      simp only [parameters] at correspondence
      simp only [fpToZ] at correspondence ⊢
      rw [correspondence.1]
      simpa only [fpToZ] using extractX_pointToZ hashPoint
    · unfold ProofCore.merkleStepDefined ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_true, ↓reduceIte]
      exact correspondence.2
  · simp only [Sinsemilla.Merkle.proverChunks, positionIsRight,
      decide_false, Bool.false_eq, Bool.true_eq_false, Bool.false_eq_true,
      ↓reduceIte] at correspondence
    rw [← merkleChunks_ofNat] at correspondence
    constructor
    · unfold ProofCore.merkleStep ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_false, ↓reduceIte]
      simp only [parameters]
      simp only [parameters] at correspondence
      simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
        fpToZ] at correspondence ⊢
      rw [correspondence.1]
      simpa only [fpToZ] using extractX_pointToZ hashPoint
    · unfold ProofCore.merkleStepDefined ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_false, ↓reduceIte]
      exact correspondence.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- Reverse one Merkle step from standalone definedness to Ironwood's
successful `hashToPoint` result. -/
theorem merkleStep_pointToZ_of_defined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (layer : Nat) (node sibling position : Fp)
    (defined :
      ProofCore.merkleStepDefined (parameters G B)
        (Int.ofNat layer) (fpToZ node)
        (pathElementOf (sibling, position))) :
    ∃ hashPoint : Point Fp,
        Specs.Sinsemilla.hashToPoint G.S B.merkleQ
            (Sinsemilla.Merkle.proverChunks layer node sibling
              (position = (1 : Fp))) =
          some hashPoint ∧
        ProofCore.merkleStep (parameters G B)
            (Int.ofNat layer) (fpToZ node)
            (pathElementOf (sibling, position)) =
          fpToZ hashPoint.x := by
  by_cases positionIsRight : position = (1 : Fp)
  · unfold ProofCore.merkleStepDefined
      ProofCore.merkleChildren pathElementOf at defined
    simp only [positionIsRight, decide_true, ↓reduceIte] at defined
    simp only [parameters, fpToZ] at defined
    rw [merkleChunks_ofNat] at defined
    rcases
        sinsemillaHashToPoint_of_defined G B B.merkleQ
          (Specs.Sinsemilla.merkleChunks
            layer sibling.val node.val) defined with
      ⟨hashPoint, hashSucceeds, hashCorrespondence⟩
    refine ⟨hashPoint, ?_, ?_⟩
    · simpa only [Sinsemilla.Merkle.proverChunks, positionIsRight,
        Bool.true_eq, ↓reduceIte] using hashSucceeds
    · unfold ProofCore.merkleStep ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_true, ↓reduceIte]
      change
        ActionGarden.extractX
            (ProofCore.sinsemillaHashToPoint (parameters G B)
              (pointToZ B.merkleQ)
              (ProofCore.merkleChunks
                (Int.ofNat layer)
                (Int.ofNat sibling.val)
                (Int.ofNat node.val))) =
          fpToZ hashPoint.x
      rw [merkleChunks_ofNat]
      rw [hashCorrespondence]
      exact extractX_pointToZ hashPoint
  · unfold ProofCore.merkleStepDefined
      ProofCore.merkleChildren pathElementOf at defined
    simp only [positionIsRight, decide_false, Bool.false_eq_true,
      ↓reduceIte] at defined
    simp only [parameters, fpToZ] at defined
    rw [merkleChunks_ofNat] at defined
    rcases
        sinsemillaHashToPoint_of_defined G B B.merkleQ
          (Specs.Sinsemilla.merkleChunks
            layer node.val sibling.val) defined with
      ⟨hashPoint, hashSucceeds, hashCorrespondence⟩
    refine ⟨hashPoint, ?_, ?_⟩
    · simpa only [Sinsemilla.Merkle.proverChunks, positionIsRight,
        Bool.false_eq, ↓reduceIte] using hashSucceeds
    · unfold ProofCore.merkleStep ProofCore.merkleChildren pathElementOf
      simp only [positionIsRight, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      change
        ActionGarden.extractX
            (ProofCore.sinsemillaHashToPoint (parameters G B)
              (pointToZ B.merkleQ)
              (ProofCore.merkleChunks
                (Int.ofNat layer)
                (Int.ofNat node.val)
                (Int.ofNat sibling.val))) =
          fpToZ hashPoint.x
      rw [merkleChunks_ofNat]
      rw [hashCorrespondence]
      exact extractX_pointToZ hashPoint

theorem merkleChunks_mem_lt_1024
    {layer left right chunk : Nat}
    (membership :
      chunk ∈ Specs.Sinsemilla.merkleChunks layer left right) :
    chunk < 1024 := by
  rw [Specs.Sinsemilla.merkleChunks_eq_chunksOf] at membership
  exact chunksOf_mem_lt_1024 membership

/-- One represented Merkle step transports from proof-only definedness to the
public explicit-layer Garden operation. -/
theorem merkleLayerGarden_of_coreDefined
    (layer : Nat) (node sibling position : Fp)
    (defined :
      ProofCore.merkleStepDefined
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (pathElementOf (sibling, position))) :
    ActionGarden.merkleLayer
        ActionGarden.orchardParams.merkleCrhQ
        (Int.ofNat layer) (fpToZ node) (fpToZ sibling)
        (decide (position = (1 : Fp))) =
      ProofCore.merkleStep
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (pathElementOf (sibling, position)) ∧
    ActionGarden.merkleStepDefinedGarden
      ActionGarden.orchardParams.merkleCrhQ
      (fpToZ node) (Int.ofNat layer) (fpToZ sibling)
      (decide (position = (1 : Fp))) := by
  rcases
      merkleStep_pointToZ_of_defined
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        layer node sibling position defined with
    ⟨hashPoint, hashSucceeds, coreResult⟩
  by_cases positionIsRight : position = (1 : Fp)
  · have hashSucceedsRight :
        Specs.Sinsemilla.hashToPoint
            Specs.Sinsemilla.orchardGenerators.S
            Zcash.Circuits.Action.orchardBases.merkleQ
            (Specs.Sinsemilla.merkleChunks
              layer sibling.val node.val) =
          some hashPoint := by
      simpa only [Sinsemilla.Merkle.proverChunks,
        positionIsRight, Bool.true_eq, ↓reduceIte] using hashSucceeds
    have hashCorrespondence :=
      sinsemillaHashGarden_of_some
        Zcash.Circuits.Action.orchardBases.merkleQ hashPoint
        (Specs.Sinsemilla.merkleChunks layer sibling.val node.val)
        (fun chunk membership =>
          merkleChunks_mem_lt_1024 membership)
        hashSucceedsRight
    have hashResult :
        ActionGarden.sinsemillaHashToPointGarden
            (pointToZ Zcash.Circuits.Action.merkleQ)
            (List.map Int.ofNat
              (Specs.Sinsemilla.merkleChunks
                layer sibling.val node.val)) =
          pointToZ hashPoint := by
      simpa using hashCorrespondence.1
    have hashIsDefined :
        ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer sibling.val node.val)) := by
      simpa using hashCorrespondence.2
    constructor
    · unfold ActionGarden.merkleLayer
      simp only [positionIsRight, decide_true, ↓reduceIte,
        ActionGarden.orchardParams, fpToZ]
      rw [orchardMerkleCrhQ_deployed]
      rw [merkleMessageGarden_ofNat]
      rw [hashResult]
      simpa [ActionGarden.extractXGarden, pointToZ, fpToZ,
        positionIsRight] using coreResult.symm
    · unfold ActionGarden.merkleStepDefinedGarden
      simp only [positionIsRight, decide_true, ↓reduceIte,
        ActionGarden.orchardParams, fpToZ]
      rw [orchardMerkleCrhQ_deployed]
      rw [merkleMessageGarden_ofNat]
      exact hashIsDefined
  · have hashSucceedsLeft :
        Specs.Sinsemilla.hashToPoint
            Specs.Sinsemilla.orchardGenerators.S
            Zcash.Circuits.Action.orchardBases.merkleQ
            (Specs.Sinsemilla.merkleChunks
              layer node.val sibling.val) =
          some hashPoint := by
      simpa only [Sinsemilla.Merkle.proverChunks,
        positionIsRight, Bool.false_eq, ↓reduceIte] using hashSucceeds
    have hashCorrespondence :=
      sinsemillaHashGarden_of_some
        Zcash.Circuits.Action.orchardBases.merkleQ hashPoint
        (Specs.Sinsemilla.merkleChunks layer node.val sibling.val)
        (fun chunk membership =>
          merkleChunks_mem_lt_1024 membership)
        hashSucceedsLeft
    have hashResult :
        ActionGarden.sinsemillaHashToPointGarden
            (pointToZ Zcash.Circuits.Action.merkleQ)
            (List.map Int.ofNat
              (Specs.Sinsemilla.merkleChunks
                layer node.val sibling.val)) =
          pointToZ hashPoint := by
      simpa using hashCorrespondence.1
    have hashIsDefined :
        ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer node.val sibling.val)) := by
      simpa using hashCorrespondence.2
    constructor
    · unfold ActionGarden.merkleLayer
      simp only [positionIsRight, decide_false, ↓reduceIte,
        Bool.false_eq_true, ActionGarden.orchardParams, fpToZ]
      rw [orchardMerkleCrhQ_deployed]
      rw [merkleMessageGarden_ofNat]
      rw [hashResult]
      simpa [ActionGarden.extractXGarden, pointToZ, fpToZ,
        positionIsRight] using coreResult.symm
    · unfold ActionGarden.merkleStepDefinedGarden
      simp only [positionIsRight, decide_false, ↓reduceIte,
        Bool.false_eq_true, ActionGarden.orchardParams, fpToZ]
      rw [orchardMerkleCrhQ_deployed]
      rw [merkleMessageGarden_ofNat]
      exact hashIsDefined

/-- The reverse one-step bridge reconstructs the represented next node. -/
theorem coreDefined_of_merkleLayerGarden
    (layer : Nat) (node sibling position : Fp)
    (defined :
      ActionGarden.merkleStepDefinedGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ node) (Int.ofNat layer) (fpToZ sibling)
        (decide (position = (1 : Fp)))) :
    ∃ nextNode : Fp,
      ProofCore.merkleStepDefined
          (parameters Specs.Sinsemilla.orchardGenerators
            Zcash.Circuits.Action.orchardBases)
          (Int.ofNat layer) (fpToZ node)
          (pathElementOf (sibling, position)) ∧
      ProofCore.merkleStep
          (parameters Specs.Sinsemilla.orchardGenerators
            Zcash.Circuits.Action.orchardBases)
          (Int.ofNat layer) (fpToZ node)
          (pathElementOf (sibling, position)) =
        fpToZ nextNode ∧
      ActionGarden.merkleLayer
          ActionGarden.orchardParams.merkleCrhQ
          (Int.ofNat layer) (fpToZ node) (fpToZ sibling)
          (decide (position = (1 : Fp))) =
        fpToZ nextNode := by
  by_cases positionIsRight : position = (1 : Fp)
  · have mappedDefined :
        ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer sibling.val node.val)) := by
      unfold ActionGarden.merkleStepDefinedGarden at defined
      simp only [positionIsRight, decide_true, ↓reduceIte,
        ActionGarden.orchardParams, fpToZ] at defined
      rw [orchardMerkleCrhQ_deployed] at defined
      rw [merkleMessageGarden_ofNat] at defined
      exact defined
    rcases
        sinsemillaHashSome_of_gardenDefined
          Zcash.Circuits.Action.orchardBases.merkleQ
          (Specs.Sinsemilla.merkleChunks
            layer sibling.val node.val)
          (fun chunk membership =>
            merkleChunks_mem_lt_1024 membership)
          (by simpa using mappedDefined) with
      ⟨hashPoint, hashSucceeds, publicResult⟩
    have stepCorrespondence :=
      merkleStep_pointToZ_of_some
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        layer node sibling position hashPoint
        (by
          simpa only [Sinsemilla.Merkle.proverChunks,
            positionIsRight, Bool.true_eq, ↓reduceIte] using
            hashSucceeds)
    refine ⟨hashPoint.x, stepCorrespondence.2,
      stepCorrespondence.1, ?_⟩
    unfold ActionGarden.merkleLayer
    simp only [positionIsRight, decide_true, ↓reduceIte,
      ActionGarden.orchardParams, fpToZ]
    rw [orchardMerkleCrhQ_deployed]
    rw [merkleMessageGarden_ofNat]
    rw [show
      ActionGarden.sinsemillaHashToPointGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer sibling.val node.val)) =
        pointToZ hashPoint by simpa using publicResult]
    rfl
  · have mappedDefined :
        ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer node.val sibling.val)) := by
      unfold ActionGarden.merkleStepDefinedGarden at defined
      simp only [positionIsRight, decide_false, Bool.false_eq_true,
        ↓reduceIte, ActionGarden.orchardParams, fpToZ] at defined
      rw [orchardMerkleCrhQ_deployed] at defined
      rw [merkleMessageGarden_ofNat] at defined
      exact defined
    rcases
        sinsemillaHashSome_of_gardenDefined
          Zcash.Circuits.Action.orchardBases.merkleQ
          (Specs.Sinsemilla.merkleChunks
            layer node.val sibling.val)
          (fun chunk membership =>
            merkleChunks_mem_lt_1024 membership)
          (by simpa using mappedDefined) with
      ⟨hashPoint, hashSucceeds, publicResult⟩
    have stepCorrespondence :=
      merkleStep_pointToZ_of_some
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        layer node sibling position hashPoint
        (by
          simpa only [Sinsemilla.Merkle.proverChunks,
            positionIsRight, Bool.false_eq, ↓reduceIte] using
            hashSucceeds)
    refine ⟨hashPoint.x, stepCorrespondence.2,
      stepCorrespondence.1, ?_⟩
    unfold ActionGarden.merkleLayer
    simp only [positionIsRight, decide_false, Bool.false_eq_true,
      ↓reduceIte, ActionGarden.orchardParams, fpToZ]
    rw [orchardMerkleCrhQ_deployed]
    rw [merkleMessageGarden_ofNat]
    rw [show
      ActionGarden.sinsemillaHashToPointGarden
          (pointToZ Zcash.Circuits.Action.merkleQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.merkleChunks
              layer node.val sibling.val)) =
        pointToZ hashPoint by simpa using publicResult]
    rfl

/-- Field-valued path rows used to make the layer-storage isomorphism
structurally explicit in the proof. -/
def corePathOfPairs (pairs : List (Fp × Fp)) :
    List ProofCore.CorePathElement :=
  pairs.map pathElementOf

def gardenPathOfPairs :
    Nat → List (Fp × Fp) →
      List (ActionGarden.Z × ActionGarden.Z × Bool)
  | _, List.nil => List.nil
  | layer, List.cons pair rest =>
      (Int.ofNat layer, fpToZ pair.1,
        decide (pair.2 = (1 : Fp))) ::
      gardenPathOfPairs (Nat.succ layer) rest

theorem gardenPathOfPairs_eq
    (layer : Nat) (pairs : List (Fp × Fp)) :
    gardenPathOfPairs layer pairs =
      gardenPathFrom layer (corePathOfPairs pairs) := by
  induction pairs generalizing layer with
  | nil =>
      rfl
  | cons pair rest inductionHypothesis =>
      simp only [gardenPathOfPairs, corePathOfPairs,
        List.map_cons, gardenPathFrom, pathElementOf]
      simpa only [corePathOfPairs] using
        congrArg
          (List.cons
            (Int.ofNat layer, fpToZ pair.1,
              decide (pair.2 = (1 : Fp))))
          (inductionHypothesis (Nat.succ layer))

set_option maxRecDepth 100000 in
/-- Forward full-path bridge, including every intermediate root. -/
theorem merklePathGarden_of_coreDefined
    (layer : Nat) (node : Fp) (pairs : List (Fp × Fp))
    (defined :
      ProofCore.merklePathDefinedFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (corePathOfPairs pairs)) :
    ActionGarden.merkleRootGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ node) (gardenPathOfPairs layer pairs) =
      ProofCore.merkleRootFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (corePathOfPairs pairs) ∧
    ActionGarden.merklePathDefinedFromGarden
      ActionGarden.orchardParams.merkleCrhQ
      (fpToZ node) (gardenPathOfPairs layer pairs) := by
  induction pairs generalizing layer node with
  | nil =>
      exact ⟨rfl, ActionGarden.merklePathDefinedFromGarden.nil _⟩
  | cons pair rest inductionHypothesis =>
      change
        ProofCore.merkleStepDefined
            (parameters Specs.Sinsemilla.orchardGenerators
              Zcash.Circuits.Action.orchardBases)
            (Int.ofNat layer) (fpToZ node) (pathElementOf pair) ∧
          ProofCore.merklePathDefinedFrom
            (parameters Specs.Sinsemilla.orchardGenerators
              Zcash.Circuits.Action.orchardBases)
            (ActionGarden.zAdd (Int.ofNat layer) ActionGarden.zOne)
            (ProofCore.merkleStep
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (Int.ofNat layer) (fpToZ node) (pathElementOf pair))
            (corePathOfPairs rest)
        at defined
      have step :=
        merkleLayerGarden_of_coreDefined
          layer node pair.1 pair.2 defined.1
      rcases
          merkleStep_pointToZ_of_defined
            Specs.Sinsemilla.orchardGenerators
            Zcash.Circuits.Action.orchardBases
            layer node pair.1 pair.2 defined.1 with
        ⟨hashPoint, hashSucceeds, coreResult⟩
      have remainingDefined :
          ProofCore.merklePathDefinedFrom
            (parameters Specs.Sinsemilla.orchardGenerators
              Zcash.Circuits.Action.orchardBases)
            (Int.ofNat (Nat.succ layer))
            (fpToZ hashPoint.x)
            (corePathOfPairs rest) := by
        change
          ProofCore.merklePathDefinedFrom
            (parameters Specs.Sinsemilla.orchardGenerators
              Zcash.Circuits.Action.orchardBases)
            (ActionGarden.zAdd (Int.ofNat layer) ActionGarden.zOne)
            (fpToZ hashPoint.x)
            (corePathOfPairs rest)
        rw [← coreResult]
        exact defined.2
      have remaining :=
        inductionHypothesis (Nat.succ layer) hashPoint.x
          remainingDefined
      constructor
      · change
          ActionGarden.merkleRootGarden
              ActionGarden.orchardParams.merkleCrhQ
              (ActionGarden.merkleLayer
                ActionGarden.orchardParams.merkleCrhQ
                (Int.ofNat layer) (fpToZ node) (fpToZ pair.1)
                (decide (pair.2 = (1 : Fp))))
              (gardenPathOfPairs (Nat.succ layer) rest) =
            ProofCore.merkleRootFrom
              (parameters Specs.Sinsemilla.orchardGenerators
                Zcash.Circuits.Action.orchardBases)
              (ActionGarden.zAdd (Int.ofNat layer) ActionGarden.zOne)
              (ProofCore.merkleStep
                (parameters Specs.Sinsemilla.orchardGenerators
                  Zcash.Circuits.Action.orchardBases)
                (Int.ofNat layer) (fpToZ node) (pathElementOf pair))
              (corePathOfPairs rest)
        rw [step.1, coreResult]
        exact remaining.1
      · exact ActionGarden.merklePathDefinedFromGarden.cons
          (node := fpToZ node)
          (nextNode := fpToZ hashPoint.x)
          (layer := Int.ofNat layer)
          (sibling := fpToZ pair.1)
          (isRight := decide (pair.2 = (1 : Fp)))
          (rest := gardenPathOfPairs (Nat.succ layer) rest)
          step.2 (step.1.trans coreResult).symm remaining.2

set_option maxRecDepth 100000 in
/-- Reverse full-path bridge. -/
theorem corePathDefined_of_merklePathGarden
    (layer : Nat) (node : Fp) (pairs : List (Fp × Fp))
    (defined :
      ActionGarden.merklePathDefinedFromGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ node) (gardenPathOfPairs layer pairs)) :
    ProofCore.merklePathDefinedFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (corePathOfPairs pairs) ∧
    ActionGarden.merkleRootGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ node) (gardenPathOfPairs layer pairs) =
      ProofCore.merkleRootFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat layer) (fpToZ node)
        (corePathOfPairs pairs) := by
  induction pairs generalizing layer node with
  | nil =>
      exact ⟨True.intro, rfl⟩
  | cons pair rest inductionHypothesis =>
      cases defined with
      | cons _ nextNode _ _ _ _ stepDefined nextEquality restDefined =>
          rcases
              coreDefined_of_merkleLayerGarden
                layer node pair.1 pair.2 stepDefined with
            ⟨nextPoint, coreStepDefined, coreResult, publicResult⟩
          have nextNodeEquality :
              nextNode = fpToZ nextPoint :=
            nextEquality.trans publicResult
          rw [nextNodeEquality] at restDefined
          have remaining :=
            inductionHypothesis (Nat.succ layer) nextPoint restDefined
          constructor
          · change
              ProofCore.merkleStepDefined
                  (parameters Specs.Sinsemilla.orchardGenerators
                    Zcash.Circuits.Action.orchardBases)
                  (Int.ofNat layer) (fpToZ node)
                  (pathElementOf pair) ∧
                ProofCore.merklePathDefinedFrom
                  (parameters Specs.Sinsemilla.orchardGenerators
                    Zcash.Circuits.Action.orchardBases)
                  (ActionGarden.zAdd
                    (Int.ofNat layer) ActionGarden.zOne)
                  (ProofCore.merkleStep
                    (parameters Specs.Sinsemilla.orchardGenerators
                      Zcash.Circuits.Action.orchardBases)
                    (Int.ofNat layer) (fpToZ node)
                    (pathElementOf pair))
                  (corePathOfPairs rest)
            constructor
            · exact coreStepDefined
            · rw [coreResult]
              exact remaining.1
          · change
              ActionGarden.merkleRootGarden
                  ActionGarden.orchardParams.merkleCrhQ
                  (ActionGarden.merkleLayer
                    ActionGarden.orchardParams.merkleCrhQ
                    (Int.ofNat layer) (fpToZ node)
                    (fpToZ pair.1)
                    (decide (pair.2 = (1 : Fp))))
                  (gardenPathOfPairs (Nat.succ layer) rest) =
                ProofCore.merkleRootFrom
                  (parameters Specs.Sinsemilla.orchardGenerators
                    Zcash.Circuits.Action.orchardBases)
                  (ActionGarden.zAdd
                    (Int.ofNat layer) ActionGarden.zOne)
                  (ProofCore.merkleStep
                    (parameters Specs.Sinsemilla.orchardGenerators
                      Zcash.Circuits.Action.orchardBases)
                    (Int.ofNat layer) (fpToZ node)
                    (pathElementOf pair))
                  (corePathOfPairs rest)
            rw [publicResult, coreResult]
            exact remaining.2

/-- The common list of the 32 field-valued Orchard authentication-path rows. -/
def actionPathPairs (wit : ActionData) : List (Fp × Fp) :=
  (List.range 32).map wit.merklePath

/-- Erasing the explicitly stored Garden layers recovers Ironwood's path. -/
theorem corePathOfPairs_actionPathPairs (wit : ActionData) :
    corePathOfPairs (actionPathPairs wit) = path wit := by
  unfold corePathOfPairs actionPathPairs path pathSegment
  rw [List.map_map]
  rfl

/-- Adding the consecutive layer numbers to Ironwood's path gives Garden's
explicit path representation. -/
theorem gardenPathOfPairs_actionPathPairs (wit : ActionData) :
    gardenPathOfPairs 0 (actionPathPairs wit) = gardenPath wit := by
  rw [gardenPathOfPairs_eq]
  rw [corePathOfPairs_actionPathPairs]
  rfl

/-- A defined Ironwood path is the same computation as the public Garden path,
including its final root and all intermediate definedness obligations. -/
theorem merklePathGarden_of_coreValid
    (wit : ActionData)
    (defined :
      ProofCore.merklePathDefined
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (fpToZ wit.cmOld.x) (path wit)) :
    ActionGarden.merkleRootGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ wit.cmOld.x) (gardenPath wit) =
      ProofCore.merkleRoot
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (fpToZ wit.cmOld.x) (path wit) ∧
    ActionGarden.merklePathDefinedGarden
      ActionGarden.orchardParams.merkleCrhQ
      (fpToZ wit.cmOld.x) (gardenPath wit) := by
  have mappedDefined :
      ProofCore.merklePathDefinedFrom
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (Int.ofNat 0) (fpToZ wit.cmOld.x)
        (corePathOfPairs (actionPathPairs wit)) := by
    unfold ProofCore.merklePathDefined at defined
    rw [corePathOfPairs_actionPathPairs]
    exact defined
  have mapped :=
    merklePathGarden_of_coreDefined
      0 wit.cmOld.x (actionPathPairs wit) mappedDefined
  rw [gardenPathOfPairs_actionPathPairs] at mapped
  unfold ProofCore.merkleRoot
  exact mapped

/-- Conversely, Garden path definedness reconstructs Ironwood path
definedness, with the same final root. -/
theorem coreMerklePath_of_gardenValid
    (wit : ActionData)
    (defined :
      ActionGarden.merklePathDefinedGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ wit.cmOld.x) (gardenPath wit)) :
    ProofCore.merklePathDefined
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (fpToZ wit.cmOld.x) (path wit) ∧
    ActionGarden.merkleRootGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ wit.cmOld.x) (gardenPath wit) =
      ProofCore.merkleRoot
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (fpToZ wit.cmOld.x) (path wit) := by
  have mappedDefined :
      ActionGarden.merklePathDefinedFromGarden
        ActionGarden.orchardParams.merkleCrhQ
        (fpToZ wit.cmOld.x)
        (gardenPathOfPairs 0 (actionPathPairs wit)) := by
    rw [gardenPathOfPairs_actionPathPairs]
    exact defined
  have mapped :=
    corePathDefined_of_merklePathGarden
      0 wit.cmOld.x (actionPathPairs wit) mappedDefined
  rw [corePathOfPairs_actionPathPairs] at mapped
  rw [gardenPathOfPairs_actionPathPairs] at mapped
  unfold ProofCore.merklePathDefined ProofCore.merkleRoot
  exact mapped

/-- Garden's explicit layer field is exactly the list position attached by
`gardenPathFrom`. -/
theorem pathLayersFrom_gardenPathFrom
    (layer : Nat) (path : List ProofCore.CorePathElement) :
    ActionGarden.pathLayersFrom (Int.ofNat layer)
      (gardenPathFrom layer path) := by
  induction path generalizing layer with
  | nil =>
      exact True.intro
  | cons element rest inductionHypothesis =>
      change
        Int.ofNat layer = Int.ofNat layer ∧
          ActionGarden.pathLayersFrom
            (ActionGarden.zAdd (Int.ofNat layer) ActionGarden.zOne)
            (gardenPathFrom (Nat.succ layer) rest)
      constructor
      · rfl
      · change
          ActionGarden.pathLayersFrom (Int.ofNat (Nat.succ layer))
            (gardenPathFrom (Nat.succ layer) rest)
        exact inductionHypothesis (Nat.succ layer)

theorem pathLayersCanonical_gardenPath (wit : ActionData) :
    ActionGarden.pathLayersCanonical (gardenPath wit) := by
  unfold ActionGarden.pathLayersCanonical gardenPath
  exact pathLayersFrom_gardenPathFrom 0 (path wit)

theorem merkleRootFrom_append
    (parameters : ProofCore.CoreParameters)
    (layer node : ActionGarden.Z)
    (front back : List ProofCore.CorePathElement) :
    ProofCore.merkleRootFrom parameters layer node (List.append front back) =
      ProofCore.merkleRootFrom parameters
        (ActionGarden.zAdd layer (Int.ofNat front.length))
        (ProofCore.merkleRootFrom parameters layer node front)
        back := by
  induction front generalizing layer node with
  | nil =>
      simp [ProofCore.merkleRootFrom, ActionGarden.zAdd]
  | cons element rest inductionHypothesis =>
      change
        ProofCore.merkleRootFrom parameters
            (ActionGarden.zAdd layer ActionGarden.zOne)
            (ProofCore.merkleStep parameters layer node element)
            (List.append rest back) =
          ProofCore.merkleRootFrom parameters
            (ActionGarden.zAdd layer (Int.ofNat (rest.length + 1)))
            (ProofCore.merkleRootFrom parameters
              (ActionGarden.zAdd layer ActionGarden.zOne)
              (ProofCore.merkleStep parameters layer node element)
              rest)
            back
      rw [inductionHypothesis]
      apply congrArg₂
        (fun nextLayer nextNode =>
          ProofCore.merkleRootFrom parameters nextLayer nextNode back)
      · unfold ActionGarden.zAdd
        simp only [ActionGarden.zOne]
        simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
        exact
          (Int.add_assoc layer 1 (Int.ofNat rest.length)).trans
            (congrArg (Int.add layer)
              (Int.add_comm 1 (Int.ofNat rest.length)))
      · rfl

theorem merklePathDefinedFrom_append_of
    (parameters : ProofCore.CoreParameters)
    (layer node : ActionGarden.Z)
    (front back : List ProofCore.CorePathElement)
    (frontDefined :
      ProofCore.merklePathDefinedFrom parameters layer node front)
    (backDefined :
      ProofCore.merklePathDefinedFrom parameters
        (ActionGarden.zAdd layer (Int.ofNat front.length))
        (ProofCore.merkleRootFrom parameters layer node front)
        back) :
    ProofCore.merklePathDefinedFrom parameters layer node
      (List.append front back) := by
  induction front generalizing layer node with
  | nil =>
      simpa [ProofCore.merkleRootFrom, ActionGarden.zAdd] using backDefined
  | cons element rest inductionHypothesis =>
      simp only [ProofCore.merklePathDefinedFrom] at frontDefined
      change
        ProofCore.merkleStepDefined parameters layer node element ∧
          ProofCore.merklePathDefinedFrom parameters
            (ActionGarden.zAdd layer ActionGarden.zOne)
            (ProofCore.merkleStep parameters layer node element)
            (List.append rest back)
      constructor
      · exact frontDefined.1
      · apply inductionHypothesis
          (layer := ActionGarden.zAdd layer ActionGarden.zOne)
          (node := ProofCore.merkleStep parameters layer node element)
          frontDefined.2
        change
          ProofCore.merklePathDefinedFrom parameters
            (ActionGarden.zAdd layer (Int.ofNat (rest.length + 1)))
            (ProofCore.merkleRootFrom parameters
              (ActionGarden.zAdd layer ActionGarden.zOne)
              (ProofCore.merkleStep parameters layer node element)
              rest)
            back at backDefined
        have layerEquality :
            ActionGarden.zAdd
                (ActionGarden.zAdd layer ActionGarden.zOne)
                (Int.ofNat rest.length) =
              ActionGarden.zAdd layer (Int.ofNat (rest.length + 1)) := by
          unfold ActionGarden.zAdd
          simp only [ActionGarden.zOne]
          simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
          exact
            (Int.add_assoc layer 1 (Int.ofNat rest.length)).trans
              (congrArg (Int.add layer)
                (Int.add_comm 1 (Int.ofNat rest.length)))
        rw [layerEquality]
        exact backDefined

/-- Split standalone Merkle definedness at a list boundary.  Together with
`merklePathDefinedFrom_append_of`, this exposes the exact two chip segments
used by Ironwood. -/
theorem merklePathDefinedFrom_append_to
    (parameters : ProofCore.CoreParameters)
    (layer node : ActionGarden.Z)
    (front back : List ProofCore.CorePathElement)
    (defined :
      ProofCore.merklePathDefinedFrom parameters layer node
        (List.append front back)) :
    ProofCore.merklePathDefinedFrom parameters layer node front ∧
      ProofCore.merklePathDefinedFrom parameters
        (ActionGarden.zAdd layer (Int.ofNat front.length))
        (ProofCore.merkleRootFrom parameters layer node front)
        back := by
  induction front generalizing layer node with
  | nil =>
      constructor
      · exact True.intro
      · simpa [ProofCore.merkleRootFrom, ActionGarden.zAdd] using defined
  | cons element rest inductionHypothesis =>
      change
        ProofCore.merkleStepDefined parameters layer node element ∧
          ProofCore.merklePathDefinedFrom parameters
            (ActionGarden.zAdd layer ActionGarden.zOne)
            (ProofCore.merkleStep parameters layer node element)
            (List.append rest back)
        at defined
      have remaining :=
        inductionHypothesis
          (layer := ActionGarden.zAdd layer ActionGarden.zOne)
          (node := ProofCore.merkleStep parameters layer node element)
          defined.2
      constructor
      · exact ⟨defined.1, remaining.1⟩
      · change
          ProofCore.merklePathDefinedFrom parameters
            (ActionGarden.zAdd layer (Int.ofNat (rest.length + 1)))
            (ProofCore.merkleRootFrom parameters
              (ActionGarden.zAdd layer ActionGarden.zOne)
              (ProofCore.merkleStep parameters layer node element)
              rest)
            back
        have layerEquality :
            ActionGarden.zAdd
                (ActionGarden.zAdd layer ActionGarden.zOne)
                (Int.ofNat rest.length) =
              ActionGarden.zAdd layer (Int.ofNat (rest.length + 1)) := by
          unfold ActionGarden.zAdd
          simp only [ActionGarden.zOne]
          simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
          exact
            (Int.add_assoc layer 1 (Int.ofNat rest.length)).trans
              (congrArg (Int.add layer)
                (Int.add_comm 1 (Int.ofNat rest.length)))
        rw [← layerEquality]
        exact remaining.2

theorem pathSegment_succ
    (wit : Nat → Fp × Fp) (count : Nat) :
    pathSegment wit (Nat.succ count) =
      List.append (pathSegment wit count)
        [pathElementOf (wit count)] := by
  unfold pathSegment
  rw [List.range_succ, List.map_append]
  rfl

theorem pathSegment_length
    (wit : Nat → Fp × Fp) (count : Nat) :
    (pathSegment wit count).length = count := by
  unfold pathSegment
  rw [List.length_map, List.length_range]

theorem pathSegment_add
    (wit : Nat → Fp × Fp) (leftCount rightCount : Nat) :
    pathSegment wit (Nat.add leftCount rightCount) =
      List.append (pathSegment wit leftCount)
        (pathSegment (fun index => wit (Nat.add leftCount index))
          rightCount) := by
  induction rightCount with
  | zero =>
      change
        pathSegment wit leftCount =
          List.append (pathSegment wit leftCount)
            (pathSegment (fun index => wit (Nat.add leftCount index)) 0)
      simp [pathSegment]
  | succ rightCount inductionHypothesis =>
      change
        pathSegment wit (Nat.succ (Nat.add leftCount rightCount)) =
          List.append (pathSegment wit leftCount)
            (pathSegment (fun index => wit (Nat.add leftCount index))
              (Nat.succ rightCount))
      rw [pathSegment_succ, pathSegment_succ]
      rw [inductionHypothesis]
      exact List.append_assoc
        (pathSegment wit leftCount)
        (pathSegment (fun index => wit (Nat.add leftCount index))
          rightCount)
        [pathElementOf (wit (Nat.add leftCount rightCount))]

theorem zAdd_ofNat (left right : Nat) :
    ActionGarden.zAdd (Int.ofNat left) (Int.ofNat right) =
      Int.ofNat (Nat.add left right) := by
  unfold ActionGarden.zAdd
  exact (Int.natCast_add left right).symm

theorem pathNode_pointToZ_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (firstLayer : Nat) (wit : Nat → Fp × Fp)
    (node root : Fp) (count : Nat)
    (succeeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ firstLayer wit node count =
        some root) :
    ProofCore.merkleRootFrom (parameters G B)
          (Int.ofNat firstLayer) (fpToZ node)
          (pathSegment wit count) =
      fpToZ root ∧
    ProofCore.merklePathDefinedFrom (parameters G B)
      (Int.ofNat firstLayer) (fpToZ node)
      (pathSegment wit count) := by
  induction count generalizing node root with
  | zero =>
      simp only [Sinsemilla.Merkle.CalculateRoot.pathNode,
        Option.some.injEq] at succeeds
      subst root
      exact ⟨rfl, True.intro⟩
  | succ count inductionHypothesis =>
      rw [Sinsemilla.Merkle.CalculateRoot.pathNode] at succeeds
      cases previousResult :
          Sinsemilla.Merkle.CalculateRoot.pathNode
            G B.merkleQ firstLayer wit node count with
      | none =>
          simp only [previousResult, Option.bind_none, reduceCtorEq] at succeeds
      | some previousNode =>
          simp only [previousResult, Option.bind_some] at succeeds
          cases stepResult :
              Specs.Sinsemilla.hashToPoint G.S B.merkleQ
                (Sinsemilla.Merkle.proverChunks
                  (firstLayer + count) previousNode
                  (wit count).1 ((wit count).2 = (1 : Fp))) with
          | none =>
              simp only [stepResult, Option.map_none, reduceCtorEq] at succeeds
          | some hashPoint =>
              simp only [stepResult, Option.map_some,
                Option.some.injEq] at succeeds
              subst root
              have previousCorrespondence :=
                inductionHypothesis
                  (node := node) (root := previousNode) previousResult
              have stepCorrespondence :=
                merkleStep_pointToZ_of_some G B
                  (firstLayer + count) previousNode
                  (wit count).1 (wit count).2 hashPoint stepResult
              constructor
              · rw [pathSegment_succ]
                rw [merkleRootFrom_append]
                rw [pathSegment_length]
                rw [zAdd_ofNat]
                rw [previousCorrespondence.1]
                simp only [ProofCore.merkleRootFrom]
                exact stepCorrespondence.1
              · rw [pathSegment_succ]
                apply merklePathDefinedFrom_append_of
                  (frontDefined := previousCorrespondence.2)
                rw [pathSegment_length]
                rw [zAdd_ofNat]
                rw [previousCorrespondence.1]
                simp only [ProofCore.merklePathDefinedFrom]
                exact ⟨stepCorrespondence.2, True.intro⟩

/-- Reverse a structurally defined standalone Merkle segment into the
successful Ironwood `pathNode` computation for the same segment. -/
theorem pathNode_pointToZ_of_defined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (firstLayer : Nat) (wit : Nat → Fp × Fp)
    (node : Fp) (count : Nat)
    (defined :
      ProofCore.merklePathDefinedFrom (parameters G B)
        (Int.ofNat firstLayer) (fpToZ node)
        (pathSegment wit count)) :
    ∃ root : Fp,
        Sinsemilla.Merkle.CalculateRoot.pathNode
            G B.merkleQ firstLayer wit node count
          = some root ∧
        ProofCore.merkleRootFrom (parameters G B)
            (Int.ofNat firstLayer) (fpToZ node)
            (pathSegment wit count) =
          fpToZ root := by
  induction count generalizing node with
  | zero =>
      exact ⟨node, rfl, rfl⟩
  | succ count inductionHypothesis =>
      rw [pathSegment_succ] at defined
      have splitDefined :=
        merklePathDefinedFrom_append_to
          (parameters G B) (Int.ofNat firstLayer) (fpToZ node)
          (pathSegment wit count) [pathElementOf (wit count)]
          defined
      rcases inductionHypothesis node splitDefined.1 with
        ⟨previousNode, previousSucceeds, previousCorrespondence⟩
      have finalDefined := splitDefined.2
      rw [pathSegment_length, zAdd_ofNat,
        previousCorrespondence] at finalDefined
      simp only [ProofCore.merklePathDefinedFrom] at finalDefined
      rcases
          merkleStep_pointToZ_of_defined G B
            (firstLayer + count) previousNode
            (wit count).1 (wit count).2 finalDefined.1 with
        ⟨hashPoint, hashSucceeds, stepCorrespondence⟩
      refine ⟨hashPoint.x, ?_, ?_⟩
      · rw [Sinsemilla.Merkle.CalculateRoot.pathNode]
        rw [previousSucceeds]
        simp only [Option.bind_some]
        rw [hashSucceeds]
        rfl
      · rw [pathSegment_succ]
        rw [merkleRootFrom_append]
        rw [pathSegment_length]
        rw [zAdd_ofNat]
        rw [previousCorrespondence]
        simp only [ProofCore.merkleRootFrom]
        exact stepCorrespondence

theorem merklePath_pointToZ_of_two_segments
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData) (middle root : Fp)
    (firstSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 0 wit.merklePath wit.cmOld.x 16 =
        some middle)
    (secondSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 16
          (fun index => wit.merklePath (16 + index))
          middle 16 =
        some root) :
    ProofCore.merkleRoot (parameters G B)
        (fpToZ wit.cmOld.x) (path wit) =
      fpToZ root ∧
    ProofCore.merklePathDefined (parameters G B)
      (fpToZ wit.cmOld.x) (path wit) := by
  have firstCorrespondence :=
    pathNode_pointToZ_of_some G B 0 wit.merklePath
      wit.cmOld.x middle 16 firstSucceeds
  have secondCorrespondence :=
    pathNode_pointToZ_of_some G B 16
      (fun index => wit.merklePath (16 + index))
      middle root 16 secondSucceeds
  have pathSplit :
      path wit =
        List.append (pathSegment wit.merklePath 16)
          (pathSegment
            (fun index => wit.merklePath (16 + index)) 16) := by
    unfold path
    rw [show 32 = 16 + 16 by norm_num]
    exact pathSegment_add wit.merklePath 16 16
  constructor
  · unfold ProofCore.merkleRoot
    rw [pathSplit, merkleRootFrom_append]
    rw [pathSegment_length]
    change
      ProofCore.merkleRootFrom (parameters G B) (Int.ofNat 16)
          (ProofCore.merkleRootFrom (parameters G B)
            (Int.ofNat 0) (fpToZ wit.cmOld.x)
            (pathSegment wit.merklePath 16))
          (pathSegment (fun index => wit.merklePath (16 + index)) 16) =
        fpToZ root
    rw [firstCorrespondence.1]
    exact secondCorrespondence.1
  · unfold ProofCore.merklePathDefined
    rw [pathSplit]
    apply merklePathDefinedFrom_append_of
      (frontDefined := firstCorrespondence.2)
    rw [pathSegment_length]
    change
      ProofCore.merklePathDefinedFrom (parameters G B) (Int.ofNat 16)
          (ProofCore.merkleRootFrom (parameters G B)
            (Int.ofNat 0) (fpToZ wit.cmOld.x)
            (pathSegment wit.merklePath 16))
          (pathSegment (fun index => wit.merklePath (16 + index)) 16)
    rw [firstCorrespondence.1]
    exact secondCorrespondence.2

/-- Reverse full standalone path definedness into Ironwood's two successful
16-layer chip computations, retaining the root representative equation. -/
theorem merklePath_two_segments_of_defined
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData)
    (defined :
      ProofCore.merklePathDefined (parameters G B)
        (fpToZ wit.cmOld.x) (path wit)) :
    ∃ middle : Fp,
        Sinsemilla.Merkle.CalculateRoot.pathNode
            G B.merkleQ 0 wit.merklePath wit.cmOld.x 16
          = some middle ∧
        ∃ root : Fp,
            Sinsemilla.Merkle.CalculateRoot.pathNode
                G B.merkleQ 16
                (fun index => wit.merklePath (16 + index))
                middle 16 =
              some root ∧
            ProofCore.merkleRoot (parameters G B)
                (fpToZ wit.cmOld.x) (path wit)
              = fpToZ root := by
  have pathSplit :
      path wit =
        List.append (pathSegment wit.merklePath 16)
          (pathSegment
            (fun index => wit.merklePath (16 + index)) 16) := by
    unfold path
    rw [show 32 = 16 + 16 by norm_num]
    exact pathSegment_add wit.merklePath 16 16
  unfold ProofCore.merklePathDefined at defined
  rw [pathSplit] at defined
  have splitDefined :=
    merklePathDefinedFrom_append_to
      (parameters G B) (Int.ofNat 0) (fpToZ wit.cmOld.x)
      (pathSegment wit.merklePath 16)
      (pathSegment (fun index => wit.merklePath (16 + index)) 16)
      defined
  rcases
      pathNode_pointToZ_of_defined G B 0 wit.merklePath
        wit.cmOld.x 16 splitDefined.1 with
    ⟨middle, firstSucceeds, firstCorrespondence⟩
  have secondDefined := splitDefined.2
  rw [pathSegment_length] at secondDefined
  change
    ProofCore.merklePathDefinedFrom (parameters G B)
      (Int.ofNat 16)
      (ProofCore.merkleRootFrom (parameters G B)
        (Int.ofNat 0) (fpToZ wit.cmOld.x)
        (pathSegment wit.merklePath 16))
      (pathSegment (fun index => wit.merklePath (16 + index)) 16)
    at secondDefined
  rw [firstCorrespondence] at secondDefined
  rcases
      pathNode_pointToZ_of_defined G B 16
        (fun index => wit.merklePath (16 + index))
        middle 16 secondDefined with
    ⟨root, secondSucceeds, secondCorrespondence⟩
  refine ⟨middle, firstSucceeds, root, secondSucceeds, ?_⟩
  unfold ProofCore.merkleRoot
  rw [pathSplit, merkleRootFrom_append, pathSegment_length]
  change
    ProofCore.merkleRootFrom (parameters G B) (Int.ofNat 16)
        (ProofCore.merkleRootFrom (parameters G B)
          (Int.ofNat 0) (fpToZ wit.cmOld.x)
          (pathSegment wit.merklePath 16))
        (pathSegment (fun index => wit.merklePath (16 + index)) 16) =
      fpToZ root
  rw [firstCorrespondence]
  exact secondCorrespondence

theorem baseToScalar_fpToZ (value : Fp) :
    ActionGarden.baseToScalar (fpToZ value) =
      fqToZ ((value.val : Nat) : Fq) := by
  unfold ActionGarden.baseToScalar
  rw [baseNormalize_fpToZ]
  change
    ActionGarden.scalarNormalize (fpToZ value) =
      fqToZ (zToFq (fpToZ value))
  exact (fqToZ_zToFq (fpToZ value)).symm

theorem baseCanonical_fpToZ (value : Fp) :
    ActionGarden.baseCanonical (fpToZ value) := by
  exact baseNormalize_fpToZ value

theorem scalarCanonical_fqToZ (value : Fq) :
    ActionGarden.scalarCanonical (fqToZ value) := by
  exact scalarNormalize_fqToZ value

theorem pointCanonical_pointToZ (point : Point Fp) :
    ActionGarden.pointCanonical (pointToZ point) := by
  exact
    ⟨baseCanonical_fpToZ point.x,
     baseCanonical_fpToZ point.y⟩

theorem fpToZ_five : fpToZ (5 : Fp) = Int.ofNat 5 := by
  native_decide

theorem pointOnCurve_pointToZ
    {point : Point Fp} (onCurve : point.OnCurve) :
    ActionGarden.pointOnCurve (pointToZ point) := by
  unfold ActionGarden.pointOnCurve
  simp only [pointToZ]
  rw [← fpToZ_mul, ← fpToZ_mul, ← fpToZ_mul]
  rw [← fpToZ_five, ← fpToZ_add]
  unfold Point.OnCurve pallasB at onCurve
  simpa only [pow_two, pow_succ, pow_zero, mul_one, one_mul] using
    congrArg fpToZ onCurve

theorem pointValid_pointToZ
    {point : Point Fp} (valid : point.Valid) :
    ActionGarden.pointValid (pointToZ point) := by
  rcases valid with onCurve | identity
  · right
    exact pointOnCurve_pointToZ onCurve
  · subst point
    left
    rw [pointNormalize_pointToZ, pointToZ_zero]

/-- Canonical representatives reflect the curve equation back into `Fp`. -/
theorem pointOnCurve_of_pointToZ
    {point : Point Fp}
    (onCurve : ActionGarden.pointOnCurve (pointToZ point)) :
    point.OnCurve := by
  unfold ActionGarden.pointOnCurve at onCurve
  simp only [pointToZ] at onCurve
  rw [← fpToZ_mul, ← fpToZ_mul, ← fpToZ_mul] at onCurve
  rw [← fpToZ_five, ← fpToZ_add] at onCurve
  apply fpToZ_injective at onCurve
  unfold Point.OnCurve pallasB
  simpa only [pow_two, pow_succ, pow_zero, mul_one, one_mul] using
    onCurve

/-- Standalone point validity reflects to Ironwood validity for values in the
image of `pointToZ`. -/
theorem pointValid_of_pointToZ
    {point : Point Fp}
    (valid : ActionGarden.pointValid (pointToZ point)) :
    point.Valid := by
  rcases valid with identity | onCurve
  · right
    rw [pointNormalize_pointToZ] at identity
    apply pointToZ_injective
    rw [pointToZ_zero]
    exact identity
  · left
    exact pointOnCurve_of_pointToZ onCurve

theorem coreParametersValid
    (G : Specs.Sinsemilla.Generators) (B : Bases) :
    ProofCore.coreParametersValid (parameters G B) := by
  unfold ProofCore.coreParametersValid parameters
  refine ⟨pointCanonical_pointToZ B.noteQ, ?_⟩
  refine ⟨pointCanonical_pointToZ B.ivkQ, ?_⟩
  refine ⟨pointCanonical_pointToZ B.merkleQ, ?_⟩
  refine ⟨pointCanonical_pointToZ B.spendAuthG.point, ?_⟩
  refine ⟨pointCanonical_pointToZ B.valueCommitV.point, ?_⟩
  refine ⟨pointCanonical_pointToZ B.valueCommitR.point, ?_⟩
  refine ⟨pointCanonical_pointToZ B.nullifierK.point, ?_⟩
  refine ⟨pointCanonical_pointToZ B.noteCommitR.point, ?_⟩
  refine ⟨pointCanonical_pointToZ B.commitIvkR.point, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.noteQ_onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.ivkQ_onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.merkleQ_onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.spendAuthG.onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.valueCommitV.onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.valueCommitR.onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.nullifierK.onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.noteCommitR.onCurve, ?_⟩
  refine ⟨pointOnCurve_pointToZ B.commitIvkR.onCurve, ?_⟩
  intro chunk chunkRange
  refine ⟨pointCanonical_pointToZ (G.S chunk.toNat), ?_⟩
  apply pointOnCurve_pointToZ
  apply G.S_onCurve
  change Int.toNat chunk < 1024
  have nonnegative : Int.ofNat 0 ≤ chunk := chunkRange.1
  have upperBound : chunk < Int.ofNat 1024 := chunkRange.2
  apply Int.ofNat_lt.mp
  rw [Int.toNat_of_nonneg nonnegative]
  exact upperBound

theorem pointToZ_scalarNsmul (scalar : Fq) (point : Point Fp) :
    pointToZ (scalar.val • point) =
      ActionGarden.scalarMul (fqToZ scalar) (pointToZ point) := by
  unfold ActionGarden.scalarMul
  rw [scalarNat_fqToZ]
  exact pointToZ_nsmul scalar.val point

/-- Garden's scalar operation on a canonical base-field representative has
the same reduction into `Fq` as Ironwood's short-scalar conversion. -/
theorem pointToZ_baseScalarMul
    (base : Ecc.MulFixed.FixedBase) (value : Fp) :
    ActionGarden.scalarMul (fpToZ value) (pointToZ base.point) =
      pointToZ (((value.val : Nat) : Fq) • base) := by
  rw [pointToZ_fullScalarMul]
  unfold ActionGarden.scalarMul
  rw [scalarNat_fqToZ]
  have normalization := baseToScalar_fpToZ value
  unfold ActionGarden.baseToScalar at normalization
  rw [baseNormalize_fpToZ] at normalization
  rw [normalization]
  rfl

/-- The public Garden-shaped nullifier primitive agrees directly with the
Ironwood field computation at the deployed constants. -/
theorem nullifierGarden_pointToZ
    (nk rho psi : Fp) (cm : Point Fp) (cmValid : cm.Valid) :
    ActionGarden.nullifier
        (fpToZ nk) (fpToZ rho) (fpToZ psi) (pointToZ cm) =
      fpToZ
        (cm +
          ((Poseidon.Hash.ConstantLength.value #v[nk, rho] + psi).val : Fq)
            • Zcash.Circuits.Action.orchardBases.nullifierK).x := by
  let hash := Poseidon.Hash.ConstantLength.value #v[nk, rho]
  let scalar : Fq := ((hash + psi).val : Nat)
  have hashCorrespondence :
      ActionGarden.poseidonHash2
          ActionGarden.orchardPoseidonParameters
          (fpToZ nk) (fpToZ rho) =
        fpToZ hash := by
    rw [poseidonHash2_deployed]
    exact (fpToZ_poseidonHash2 nk rho).symm
  have scalarCorrespondence :
      ActionGarden.scalarMul
          (ActionGarden.baseAdd (fpToZ hash) (fpToZ psi))
          ActionGarden.orchardNullifierKG =
        pointToZ
          (scalar •
            Zcash.Circuits.Action.orchardBases.nullifierK) := by
    rw [orchardNullifierKG_deployed]
    rw [← fpToZ_add]
    exact pointToZ_baseScalarMul
      Zcash.Circuits.Action.orchardBases.nullifierK (hash + psi)
  have scalarValid :
      (scalar •
        Zcash.Circuits.Action.orchardBases.nullifierK).Valid :=
    Zcash.Circuits.Action.orchardBases.nullifierK.smul_valid scalar
  unfold ActionGarden.nullifier
  simp only
  rw [hashCorrespondence, scalarCorrespondence]
  rw [← pointToZ_addGarden
    (scalar • Zcash.Circuits.Action.orchardBases.nullifierK)
    cm scalarValid cmValid]
  unfold ActionGarden.extractXGarden pointToZ
  apply congrArg (fun point : Point Fp => fpToZ point.x)
  exact Point.add_comm scalarValid cmValid

theorem noteCommit_pointToZ_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (gd pkd : Point Fp) (value rho psi : Fp) (randomness : Fq)
    (hashPoint : Point Fp)
    (hashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars gd pkd value rho psi)) =
        some hashPoint) :
    ProofCore.coreNoteCommit (parameters G B)
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi)
        (fqToZ randomness) =
      pointToZ (hashPoint + randomness • B.noteCommitR) ∧
    ProofCore.sinsemillaHashDefined (parameters G B)
      (pointToZ B.noteQ)
      (ProofCore.noteCommitChunks
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi)) := by
  have hashCorrespondence :=
    sinsemillaHashToPoint_of_some G B B.noteQ hashPoint
      (NoteCommit.NoteCommitScalars.chunks
        (NoteCommit.noteScalars gd pkd value rho psi))
      hashDefined
  rw [← noteCommitChunks_pointToZ] at hashCorrespondence
  constructor
  · unfold ProofCore.coreNoteCommit
    simp only [parameters]
    simp only [parameters] at hashCorrespondence
    rw [hashCorrespondence.1]
    rw [← pointToZ_fullScalarMul]
    rw [← pointToZ_add]
  · exact hashCorrespondence.2

/-- The public Garden-shaped note commitment computes the same point as
Ironwood, and its explicit definedness predicate is exactly witnessed by the
same successful Sinsemilla computation. -/
theorem noteCommitGarden_pointToZ_of_some
    (gd pkd : Point Fp) (value rho psi : Fp) (randomness : Fq)
    (hashPoint : Point Fp)
    (hashDefined :
      Specs.Sinsemilla.hashToPoint
          Specs.Sinsemilla.orchardGenerators.S
          Zcash.Circuits.Action.orchardBases.noteQ
          (NoteCommit.NoteCommitScalars.chunks
            (NoteCommit.noteScalars gd pkd value rho psi)) =
        some hashPoint) :
    ActionGarden.noteCommit ActionGarden.orchardParams
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi)
        (fqToZ randomness) =
      pointToZ
        (hashPoint +
          randomness • Zcash.Circuits.Action.orchardBases.noteCommitR) ∧
    ActionGarden.sinsemillaHashDefinedGarden
      ActionGarden.orchardParams.noteCommitQ
      (ActionGarden.noteCommitMessageGarden
        (pointToZ gd) (pointToZ pkd)
        (fpToZ value) (fpToZ rho) (fpToZ psi)) := by
  let chunks :=
    NoteCommit.NoteCommitScalars.chunks
      (NoteCommit.noteScalars gd pkd value rho psi)
  have chunksInRange :
      ∀ chunk ∈ chunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  have hashCorrespondence :=
    sinsemillaHashGarden_of_some
      Zcash.Circuits.Action.orchardBases.noteQ
      hashPoint chunks chunksInRange hashDefined
  have hashValid : hashPoint.Valid :=
    Specs.Sinsemilla.hashToPoint_valid
      (.inl Zcash.Circuits.Action.orchardBases.noteQ_onCurve)
      (fun chunk membership => by
        simpa [Specs.K] using chunksInRange chunk membership)
      hashDefined
  have randomnessValid :
      (randomness •
        Zcash.Circuits.Action.orchardBases.noteCommitR).Valid :=
    Zcash.Circuits.Action.orchardBases.noteCommitR.smul_valid randomness
  have hashResult :
      ActionGarden.sinsemillaHashToPointGarden
          (pointToZ Zcash.Circuits.Action.noteQ)
          (List.map Int.ofNat
            (NoteCommit.NoteCommitScalars.chunks
              (NoteCommit.noteScalars gd pkd value rho psi))) =
        pointToZ hashPoint := by
    simpa only [chunks] using hashCorrespondence.1
  have hashIsDefined :
      ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.noteQ)
          (List.map Int.ofNat
            (NoteCommit.NoteCommitScalars.chunks
              (NoteCommit.noteScalars gd pkd value rho psi))) := by
    simpa only [chunks] using hashCorrespondence.2
  constructor
  · unfold ActionGarden.noteCommit
    simp only [ActionGarden.orchardParams,
      ActionGarden.Params.noteCommitQ]
    rw [orchardNoteCommitQ_deployed]
    rw [noteCommitMessageGarden_pointToZ]
    rw [hashResult]
    rw [orchardNoteCommitRG_deployed]
    rw [← pointToZ_fullScalarMul]
    rw [← pointToZ_addGarden
      hashPoint
      (randomness •
        Zcash.Circuits.Action.orchardBases.noteCommitR)
      hashValid randomnessValid]
  · simp only [ActionGarden.orchardParams,
      ActionGarden.Params.noteCommitQ]
    rw [orchardNoteCommitQ_deployed]
    rw [noteCommitMessageGarden_pointToZ]
    exact hashIsDefined

theorem commitIvk_pointToZ_of_some
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (ak nk : Fp) (randomness : Fq) (hashPoint : Point Fp)
    (hashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.ivkQ
        (Specs.Sinsemilla.commitIvkChunks ak.val nk.val) =
        some hashPoint) :
    ProofCore.coreCommitIvk (parameters G B)
        (fpToZ ak) (fpToZ nk) (fqToZ randomness) =
      pointToZ (hashPoint + randomness • B.commitIvkR) ∧
    ProofCore.sinsemillaHashDefined (parameters G B)
      (pointToZ B.ivkQ)
      (ProofCore.commitIvkChunks (fpToZ ak) (fpToZ nk)) := by
  have hashCorrespondence :=
    sinsemillaHashToPoint_of_some G B B.ivkQ hashPoint
      (Specs.Sinsemilla.commitIvkChunks ak.val nk.val)
      hashDefined
  rw [← commitIvkChunks_fpToZ] at hashCorrespondence
  constructor
  · unfold ProofCore.coreCommitIvk
    simp only [parameters]
    simp only [parameters] at hashCorrespondence
    rw [hashCorrespondence.1]
    rw [← pointToZ_fullScalarMul]
    rw [← pointToZ_add]
  · exact hashCorrespondence.2

theorem nullifier_pointToZ
    (B : Bases) (G : Specs.Sinsemilla.Generators)
    (nk rho psi : Fp) (cm : Point Fp) (cmValid : cm.Valid) :
    ProofCore.coreNullifier (parameters G B)
        (fpToZ nk) (fpToZ rho) (fpToZ psi) (pointToZ cm) =
      fpToZ
        (cm +
          ((Poseidon.Hash.ConstantLength.value #v[nk, rho] + psi).val : Fq)
            • B.nullifierK).x := by
  unfold ProofCore.coreNullifier
  simp only [parameters]
  rw [← fpToZ_poseidonHash2]
  rw [← fpToZ_add]
  rw [baseToScalar_fpToZ]
  rw [← pointToZ_fullScalarMul]
  rw [← pointToZ_add]
  rw [extractX_pointToZ]
  apply congrArg (fun point : Point Fp => fpToZ point.x)
  exact Point.add_comm (B.nullifierK.smul_valid _) cmValid

theorem spendAuthRandomize_pointToZ
    (B : Bases) (G : Specs.Sinsemilla.Generators)
    (ak : Point Fp) (alpha : Fq) (akOnCurve : ak.OnCurve) :
    ProofCore.coreSpendAuthRandomize (parameters G B)
        (pointToZ ak) (fqToZ alpha) =
      pointToZ (alpha • B.spendAuthG + ak) := by
  unfold ProofCore.coreSpendAuthRandomize
  simp only [parameters]
  rw [← pointToZ_fullScalarMul]
  rw [← pointToZ_add]
  apply congrArg pointToZ
  exact Point.add_comm (.inl akOnCurve) (B.spendAuthG.smul_valid alpha)

theorem signedNetValue_one (magnitude : Fp) :
    ProofCore.coreSignedNetValue (fpToZ magnitude) (fpToZ (1 : Fp)) =
      fqToZ ((magnitude.val : Nat) : Fq) := by
  unfold ProofCore.coreSignedNetValue
  rw [← fpToZ_one, baseEqual_fpToZ]
  simp only [decide_true, ↓reduceIte]
  exact baseToScalar_fpToZ magnitude

theorem signedNetValue_negOne (magnitude : Fp) :
    ProofCore.coreSignedNetValue (fpToZ magnitude) (fpToZ (-1 : Fp)) =
      fqToZ (-((magnitude.val : Nat) : Fq)) := by
  unfold ProofCore.coreSignedNetValue
  rw [← fpToZ_one, baseEqual_fpToZ]
  have negOneNotOne : (-1 : Fp) ≠ 1 := by native_decide
  simp only [negOneNotOne, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [baseToScalar_fpToZ]
  rw [← fqToZ_neg]

theorem valueCommit_pointToZ_one
    (B : Bases) (G : Specs.Sinsemilla.Generators)
    (magnitude : Fp) (randomness : Fq) :
    ProofCore.coreValueCommit (parameters G B)
        (ProofCore.coreSignedNetValue
          (fpToZ magnitude) (fpToZ (1 : Fp)))
        (fqToZ randomness) =
      pointToZ
        (((magnitude.val : Nat) : Fq) • B.valueCommitV +
          randomness • B.valueCommitR) := by
  rw [signedNetValue_one]
  unfold ProofCore.coreValueCommit
  simp only [parameters]
  rw [← pointToZ_shortScalarMul, ← pointToZ_fullScalarMul]
  rw [← pointToZ_add]

theorem valueCommit_pointToZ_negOne
    (B : Bases) (G : Specs.Sinsemilla.Generators)
    (magnitude : Fp) (randomness : Fq) :
    ProofCore.coreValueCommit (parameters G B)
        (ProofCore.coreSignedNetValue
          (fpToZ magnitude) (fpToZ (-1 : Fp)))
        (fqToZ randomness) =
      pointToZ
        (-((magnitude.val : Nat) : Fq) • B.valueCommitV +
          randomness • B.valueCommitR) := by
  rw [signedNetValue_negOne]
  unfold ProofCore.coreValueCommit
  simp only [parameters]
  rw [← pointToZ_shortScalarMul, ← pointToZ_fullScalarMul]
  rw [← pointToZ_add]

theorem basePointMul_pointToZ (value : Fp) (point : Point Fp) :
    ActionGarden.basePointMul (fpToZ value) (pointToZ point) =
      pointToZ (value.val • point) := by
  unfold ActionGarden.basePointMul
  rw [baseNormalize_fpToZ]
  simp only [fpToZ, intToNat_ofNat]
  exact (pointToZ_nsmul value.val point).symm

theorem pathDepth_eq_length (elements : List ProofCore.CorePathElement) :
    ProofCore.pathDepth elements = Int.ofNat elements.length := by
  induction elements with
  | nil => rfl
  | cons element rest inductionHypothesis =>
      simp only [ProofCore.pathDepth, List.length_cons]
      rw [inductionHypothesis]
      unfold ActionGarden.zAdd ActionGarden.zOne
      simp only [Int.ofNat_eq_natCast, Int.natCast_succ]
      exact Int.add_comm 1 (Int.ofNat rest.length)

theorem pathDepth_path (wit : ActionData) :
    ProofCore.pathDepth (path wit) = Int.ofNat 32 := by
  rw [pathDepth_eq_length]
  unfold path
  rw [pathSegment_length]

theorem fpToZ_inRange_of_lt
    (value : Fp) (upperBound : Nat) (upper : value.val < upperBound) :
    ActionGarden.inRange (fpToZ value) (Int.ofNat upperBound) := by
  unfold ActionGarden.inRange fpToZ ActionGarden.zZero
  constructor
  · exact Int.ofNat_zero_le value.val
  · exact Int.ofNat_lt.mpr upper

theorem pallasBaseCard_lt_twoTo255 :
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD < 2 ^ 255 := by
  native_decide

theorem fpToZ_inRange_twoTo255 (value : Fp) :
    ActionGarden.inRange (fpToZ value)
      (ActionGarden.zPowNat ActionGarden.zTwo 255) := by
  change
    ActionGarden.inRange (fpToZ value) (Int.ofNat (2 ^ 255))
  apply fpToZ_inRange_of_lt
  exact Nat.lt_trans value.isLt pallasBaseCard_lt_twoTo255

theorem fpToZ_inRange_twoTo64
    (value : Fp) (upper : value.val < 2 ^ 64) :
    ActionGarden.inRange (fpToZ value)
      (ActionGarden.zPowNat ActionGarden.zTwo 64) := by
  change
    ActionGarden.inRange (fpToZ value) (Int.ofNat (2 ^ 64))
  exact fpToZ_inRange_of_lt value (2 ^ 64) upper

/-- Reflect a standalone 64-bit range check on a field representative. -/
theorem lt_twoTo64_of_fpToZ_inRange
    (value : Fp)
    (range :
      ActionGarden.inRange (fpToZ value)
        (ActionGarden.zPowNat ActionGarden.zTwo 64)) :
    value.val < 2 ^ 64 := by
  change
    ActionGarden.inRange (fpToZ value) (Int.ofNat (2 ^ 64))
    at range
  unfold ActionGarden.inRange fpToZ at range
  exact Int.ofNat_lt.mp range.2

theorem actionInputsTyped_input
    (wit : ActionData)
    (cmOldValid : wit.cmOld.Valid)
    (gdOldOnCurve : wit.gdOld.OnCurve)
    (akOnCurve : wit.akP.OnCurve)
    (pkdOldOnCurve : wit.pkdOld.OnCurve)
    (gdNewOnCurve : wit.gdNew.OnCurve)
    (pkdNewOnCurve : wit.pkdNew.OnCurve) :
    ProofCore.coreInputsTyped (input wit) := by
  unfold ProofCore.coreInputsTyped
  constructor
  · unfold ProofCore.corePointsTyped input
    exact
      ⟨pointCanonical_pointToZ wit.akP,
       pointCanonical_pointToZ wit.cmOld,
       pointCanonical_pointToZ wit.gdOld,
       pointCanonical_pointToZ wit.pkdOld,
       pointCanonical_pointToZ wit.gdNew,
       pointCanonical_pointToZ wit.pkdNew,
       pointOnCurve_pointToZ akOnCurve,
       pointValid_pointToZ cmOldValid,
       pointOnCurve_pointToZ gdOldOnCurve,
       pointOnCurve_pointToZ pkdOldOnCurve,
       pointOnCurve_pointToZ gdNewOnCurve,
       pointOnCurve_pointToZ pkdNewOnCurve⟩
  · constructor
    · unfold ProofCore.coreBaseValuesTyped input
      exact
        ⟨baseCanonical_fpToZ wit.nk,
         baseCanonical_fpToZ wit.rhoOld,
         baseCanonical_fpToZ wit.psiOld,
         baseCanonical_fpToZ wit.vOld,
         baseCanonical_fpToZ wit.anchor,
         baseCanonical_fpToZ wit.enableSpend,
         baseCanonical_fpToZ wit.enableOutput,
         baseCanonical_fpToZ wit.disableCrossAddress,
         baseCanonical_fpToZ wit.magnitude,
         baseCanonical_fpToZ wit.sign,
         baseCanonical_fpToZ wit.cmOld.x,
         baseCanonical_fpToZ wit.vNew,
         baseCanonical_fpToZ wit.psiNew⟩
    · unfold ProofCore.coreScalarValuesTyped input
      exact
        ⟨scalarCanonical_fqToZ wit.rivk.2,
         scalarCanonical_fqToZ wit.alpha.2,
         scalarCanonical_fqToZ wit.rcmOld.2,
         scalarCanonical_fqToZ wit.rcmNew.2,
         scalarCanonical_fqToZ wit.rcv.2⟩

/-- For projected Ironwood data, standalone typing reflects exactly the six
point-validity clauses used by the honest prover predicate. -/
theorem actionPoints_of_typed_input
    (wit : ActionData)
    (typed : ProofCore.coreInputsTyped (input wit)) :
    wit.cmOld.Valid ∧
    wit.gdOld.OnCurve ∧
    wit.akP.OnCurve ∧
    wit.pkdOld.OnCurve ∧
    wit.gdNew.OnCurve ∧
    wit.pkdNew.OnCurve := by
  unfold ProofCore.coreInputsTyped at typed
  have points := typed.1
  unfold ProofCore.corePointsTyped input at points
  rcases points with
    ⟨_akCanonical, _cmCanonical, _gdOldCanonical, _pkdOldCanonical,
     _gdNewCanonical, _pkdNewCanonical,
     akOnCurve, cmOldValid, gdOldOnCurve, pkdOldOnCurve,
     gdNewOnCurve, pkdNewOnCurve⟩
  exact
    ⟨pointValid_of_pointToZ cmOldValid,
     pointOnCurve_of_pointToZ gdOldOnCurve,
     pointOnCurve_of_pointToZ akOnCurve,
     pointOnCurve_of_pointToZ pkdOldOnCurve,
     pointOnCurve_of_pointToZ gdNewOnCurve,
     pointOnCurve_of_pointToZ pkdNewOnCurve⟩

theorem actionRangesValid_input
    (wit : ActionData)
    (vOldRange : wit.vOld.val < 2 ^ 64)
    (vNewRange : wit.vNew.val < 2 ^ 64)
    (magnitudeRange : wit.magnitude.val < 2 ^ 64)
    (signValid : wit.sign = 1 ∨ wit.sign = -1) :
    ProofCore.coreRangesValid (input wit) := by
  unfold ProofCore.coreRangesValid input
  refine
    ⟨fpToZ_inRange_twoTo64 wit.vOld vOldRange,
     fpToZ_inRange_twoTo64 wit.vNew vNewRange,
     fpToZ_inRange_twoTo64 wit.magnitude magnitudeRange,
     ?_, fpToZ_inRange_twoTo255 wit.cmOld.x, ?_⟩
  · rcases signValid with signIsOne | signIsNegOne
    · left
      rw [signIsOne]
      exact fpToZ_one
    · right
      rw [signIsNegOne]
      rw [← fpToZ_one]
      exact fpToZ_neg (1 : Fp)
  · intro element elementInPath
    unfold path pathSegment at elementInPath
    rcases List.mem_map.mp elementInPath with
      ⟨index, indexInRange, elementEquality⟩
    subst element
    unfold pathElementOf
    exact fpToZ_inRange_twoTo255 (wit.merklePath index).1

/-- Reflect the three 64-bit ranges and the `±1` sign condition from the
standalone range group. -/
theorem actionRanges_of_valid_input
    (wit : ActionData)
    (ranges : ProofCore.coreRangesValid (input wit)) :
    wit.vOld.val < 2 ^ 64 ∧
    wit.vNew.val < 2 ^ 64 ∧
    wit.magnitude.val < 2 ^ 64 ∧
    (wit.sign = 1 ∨ wit.sign = -1) := by
  unfold ProofCore.coreRangesValid input at ranges
  refine
    ⟨lt_twoTo64_of_fpToZ_inRange wit.vOld ranges.1,
     lt_twoTo64_of_fpToZ_inRange wit.vNew ranges.2.1,
     lt_twoTo64_of_fpToZ_inRange wit.magnitude ranges.2.2.1,
     ?_⟩
  rcases ranges.2.2.2.1 with signIsOne | signIsNegOne
  · left
    apply fpToZ_injective
    rw [fpToZ_one]
    exact signIsOne
  · right
    apply fpToZ_injective
    rw [fpToZ_neg, fpToZ_one]
    exact signIsNegOne

theorem actionValueConstraints_input
    (wit : ActionData)
    (valueEquation :
      wit.vOld - wit.vNew = wit.magnitude * wit.sign)
    (spendEquation :
      wit.vOld * (1 - wit.enableSpend) = 0)
    (outputEquation :
      wit.vNew * (1 - wit.enableOutput) = 0)
    (crossAddress :
      wit.disableCrossAddress = 0 ∨
        (wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew)) :
    ProofCore.coreValueConstraints (input wit) := by
  unfold ProofCore.coreValueConstraints input
  constructor
  · rw [← fpToZ_sub, ← fpToZ_mul, valueEquation]
  · constructor
    · rw [← fpToZ_one, ← fpToZ_sub, ← fpToZ_mul]
      rw [spendEquation, fpToZ_zero]
    · constructor
      · rw [← fpToZ_one, ← fpToZ_sub, ← fpToZ_mul]
        rw [outputEquation, fpToZ_zero]
      · intro disableNonzero
        rcases crossAddress with disableIsZero | addressesEqual
        · exfalso
          apply disableNonzero
          rw [disableIsZero, fpToZ_zero]
        · exact
            ⟨congrArg pointToZ addressesEqual.1,
             congrArg pointToZ addressesEqual.2⟩

/-- Reflect the field equations and cross-address disjunction from the
standalone value-constraint group. -/
theorem actionValues_of_constraints_input
    (wit : ActionData)
    (constraints : ProofCore.coreValueConstraints (input wit)) :
    wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
    wit.vOld * (1 - wit.enableSpend) = 0 ∧
    wit.vNew * (1 - wit.enableOutput) = 0 ∧
    (wit.disableCrossAddress = 0 ∨
      (wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew)) := by
  unfold ProofCore.coreValueConstraints input at constraints
  constructor
  · apply fpToZ_injective
    rw [fpToZ_sub, fpToZ_mul]
    exact constraints.1
  · constructor
    · apply fpToZ_injective
      rw [fpToZ_mul, fpToZ_sub, fpToZ_one, fpToZ_zero]
      exact constraints.2.1
    · constructor
      · apply fpToZ_injective
        rw [fpToZ_mul, fpToZ_sub, fpToZ_one, fpToZ_zero]
        exact constraints.2.2.1
      · by_cases disableIsZero : wit.disableCrossAddress = 0
        · left
          exact disableIsZero
        · right
          have representativeNonzero :
              fpToZ wit.disableCrossAddress ≠ ActionGarden.zZero := by
            rw [← fpToZ_zero]
            exact fun equality => disableIsZero (fpToZ_injective equality)
          have addressesEqual := constraints.2.2.2 representativeNonzero
          exact
            ⟨pointToZ_injective addressesEqual.1,
             pointToZ_injective addressesEqual.2⟩

theorem actionOwnershipValid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData) (ivkHashPoint oldNoteHashPoint : Point Fp)
    (ivkHashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.ivkQ
        (Specs.Sinsemilla.commitIvkChunks wit.akP.x.val wit.nk.val) =
        some ivkHashPoint)
    (pkdEquation :
      wit.pkdOld =
        ((ivkHashPoint + wit.rivk.2 • B.commitIvkR).x).val •
          wit.gdOld)
    (oldNoteHashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars wit.gdOld wit.pkdOld
            wit.vOld wit.rhoOld wit.psiOld)) =
        some oldNoteHashPoint)
    (cmOldEquation :
      wit.cmOld =
        oldNoteHashPoint + wit.rcmOld.2 • B.noteCommitR) :
    ProofCore.coreOwnershipValid (parameters G B) (input wit) := by
  have ivkCorrespondence :=
    commitIvk_pointToZ_of_some G B wit.akP.x wit.nk
      wit.rivk.2 ivkHashPoint ivkHashDefined
  have oldNoteCorrespondence :=
    noteCommit_pointToZ_of_some G B wit.gdOld wit.pkdOld
      wit.vOld wit.rhoOld wit.psiOld wit.rcmOld.2
      oldNoteHashPoint oldNoteHashDefined
  unfold ProofCore.coreOwnershipValid
  simp only [input]
  rw [extractX_pointToZ]
  simp only [parameters] at ivkCorrespondence oldNoteCorrespondence ⊢
  refine
    ⟨ivkCorrespondence.2, ?_,
     oldNoteCorrespondence.2, ?_⟩
  · rw [ivkCorrespondence.1]
    rw [extractX_pointToZ]
    rw [basePointMul_pointToZ]
    rw [pkdEquation]
  · rw [oldNoteCorrespondence.1]
    rw [cmOldEquation]

/-- Reflect standalone ownership validity into the two successful Ironwood
Sinsemilla hashes and their field equations. -/
theorem actionOwnership_of_valid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData)
    (valid :
      ProofCore.coreOwnershipValid (parameters G B) (input wit)) :
    (∃ ivkHashPoint : Point Fp,
      Specs.Sinsemilla.hashToPoint G.S B.ivkQ
          (Specs.Sinsemilla.commitIvkChunks
            wit.akP.x.val wit.nk.val) =
        some ivkHashPoint ∧
      wit.pkdOld =
        ((ivkHashPoint + wit.rivk.2 • B.commitIvkR).x).val •
          wit.gdOld) ∧
    (∃ oldNoteHashPoint : Point Fp,
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
          (NoteCommit.NoteCommitScalars.chunks
            (NoteCommit.noteScalars wit.gdOld wit.pkdOld
              wit.vOld wit.rhoOld wit.psiOld)) =
        some oldNoteHashPoint ∧
      wit.cmOld =
        oldNoteHashPoint + wit.rcmOld.2 • B.noteCommitR) := by
  unfold ProofCore.coreOwnershipValid at valid
  simp only [input, extractX_pointToZ] at valid
  rcases valid with
    ⟨ivkDefined, pkdEquation, oldNoteDefined, cmOldEquation⟩
  have ivkDefinedMapped := ivkDefined
  simp only [parameters] at ivkDefinedMapped
  rw [commitIvkChunks_fpToZ] at ivkDefinedMapped
  rcases
      sinsemillaHashToPoint_of_defined G B B.ivkQ
        (Specs.Sinsemilla.commitIvkChunks wit.akP.x.val wit.nk.val)
        ivkDefinedMapped with
    ⟨ivkHashPoint, ivkHashDefined, _ivkHashCorrespondence⟩
  have ivkCorrespondence :=
    commitIvk_pointToZ_of_some G B wit.akP.x wit.nk
      wit.rivk.2 ivkHashPoint ivkHashDefined
  rw [ivkCorrespondence.1, extractX_pointToZ,
    basePointMul_pointToZ] at pkdEquation
  have oldNoteDefinedMapped := oldNoteDefined
  simp only [parameters] at oldNoteDefinedMapped
  rw [noteCommitChunks_pointToZ] at oldNoteDefinedMapped
  rcases
      sinsemillaHashToPoint_of_defined G B B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars wit.gdOld wit.pkdOld
            wit.vOld wit.rhoOld wit.psiOld))
        oldNoteDefinedMapped with
    ⟨oldNoteHashPoint, oldNoteHashDefined,
      _oldNoteHashCorrespondence⟩
  have oldNoteCorrespondence :=
    noteCommit_pointToZ_of_some G B wit.gdOld wit.pkdOld
      wit.vOld wit.rhoOld wit.psiOld wit.rcmOld.2
      oldNoteHashPoint oldNoteHashDefined
  rw [oldNoteCorrespondence.1] at cmOldEquation
  exact
    ⟨⟨ivkHashPoint, ivkHashDefined,
       pointToZ_injective pkdEquation⟩,
     ⟨oldNoteHashPoint, oldNoteHashDefined,
       pointToZ_injective cmOldEquation⟩⟩

theorem actionMerkleValid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData) (middle root : Fp)
    (firstSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 0 wit.merklePath wit.cmOld.x 16 =
        some middle)
    (secondSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 16
          (fun index => wit.merklePath (16 + index))
          middle 16 =
        some root)
    (anchorEquation : wit.vOld * (root - wit.anchor) = 0) :
    ProofCore.coreMerkleValid (parameters G B) (input wit) := by
  have merkleCorrespondence :=
    merklePath_pointToZ_of_two_segments G B wit middle root
      firstSucceeds secondSucceeds
  unfold ProofCore.coreMerkleValid input
  refine
    ⟨pathDepth_path wit, merkleCorrespondence.2, ?_, ?_⟩
  · exact (extractX_pointToZ wit.cmOld).symm
  · rcases mul_eq_zero.mp anchorEquation with
      valueIsZero | rootMinusAnchorIsZero
    · left
      rw [valueIsZero, fpToZ_zero]
    · right
      rw [merkleCorrespondence.1]
      have rootIsAnchor : root = wit.anchor :=
        sub_eq_zero.mp rootMinusAnchorIsZero
      rw [rootIsAnchor]

/-- Reflect standalone Merkle validity into Ironwood's two successful Merkle
segments and the honest dummy/non-dummy anchor product equation. -/
theorem actionMerkle_of_valid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData)
    (valid :
      ProofCore.coreMerkleValid (parameters G B) (input wit)) :
    ∃ middle : Fp,
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 0 wit.merklePath wit.cmOld.x 16 =
        some middle ∧
      ∃ root : Fp,
        Sinsemilla.Merkle.CalculateRoot.pathNode
            G B.merkleQ 16
            (fun index => wit.merklePath (16 + index))
            middle 16 =
          some root ∧
        wit.vOld * (root - wit.anchor) = 0 := by
  unfold ProofCore.coreMerkleValid input at valid
  rcases valid with
    ⟨_pathDepth, pathDefined, _leafEquation, anchorValid⟩
  rcases
      merklePath_two_segments_of_defined G B wit pathDefined with
    ⟨middle, firstSucceeds, root, secondSucceeds,
      rootCorrespondence⟩
  refine ⟨middle, firstSucceeds, ?_⟩
  refine ⟨root, secondSucceeds, ?_⟩
  rcases anchorValid with valueIsZero | anchorEquation
  · have fieldValueIsZero : wit.vOld = 0 := by
      apply fpToZ_injective
      rw [fpToZ_zero]
      exact valueIsZero
    rw [fieldValueIsZero, zero_mul]
  · have fieldAnchorEquation : wit.anchor = root := by
      apply fpToZ_injective
      rw [rootCorrespondence] at anchorEquation
      exact anchorEquation
    rw [fieldAnchorEquation, sub_self, mul_zero]

theorem actionNewNoteValid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData) (cmOldValid : wit.cmOld.Valid)
    (newNoteHashPoint : Point Fp)
    (nullifierEquation :
      wit.nfOld =
        (wit.cmOld +
          ((Poseidon.Hash.ConstantLength.value
            #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
            B.nullifierK).x)
    (newNoteHashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars wit.gdNew wit.pkdNew
            wit.vNew wit.nfOld wit.psiNew)) =
        some newNoteHashPoint) :
    ProofCore.coreNewNoteValid (parameters G B) (input wit) := by
  have nullifierCorrespondence :=
    nullifier_pointToZ B G wit.nk wit.rhoOld wit.psiOld
      wit.cmOld cmOldValid
  rw [← nullifierEquation] at nullifierCorrespondence
  have newNoteCorrespondence :=
    noteCommit_pointToZ_of_some G B wit.gdNew wit.pkdNew
      wit.vNew wit.nfOld wit.psiNew wit.rcmNew.2
      newNoteHashPoint newNoteHashDefined
  unfold ProofCore.coreNewNoteValid input
  rw [nullifierCorrespondence]
  simpa only [parameters] using newNoteCorrespondence.2

/-- Reflect new-note definedness using the honestly computed field coreNullifier.
The completion theorem below installs that coreNullifier in the erased public
output row. -/
theorem actionNewNote_of_valid_input
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData) (cmOldValid : wit.cmOld.Valid)
    (valid :
      ProofCore.coreNewNoteValid (parameters G B) (input wit)) :
    ∃ newNoteHashPoint : Point Fp,
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
          (NoteCommit.NoteCommitScalars.chunks
            (NoteCommit.noteScalars wit.gdNew wit.pkdNew
              wit.vNew
              (wit.cmOld +
                ((Poseidon.Hash.ConstantLength.value
                  #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
                  B.nullifierK).x
              wit.psiNew)) =
        some newNoteHashPoint := by
  unfold ProofCore.coreNewNoteValid input at valid
  rw [nullifier_pointToZ B G wit.nk wit.rhoOld wit.psiOld
    wit.cmOld cmOldValid] at valid
  simp only [parameters] at valid
  rw [noteCommitChunks_pointToZ] at valid
  rcases
      sinsemillaHashToPoint_of_defined G B B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars wit.gdNew wit.pkdNew
            wit.vNew
            (wit.cmOld +
              ((Poseidon.Hash.ConstantLength.value
                #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
                B.nullifierK).x
            wit.psiNew))
        valid with
    ⟨newNoteHashPoint, hashDefined, _hashCorrespondence⟩
  exact ⟨newNoteHashPoint, hashDefined⟩

theorem orchardAction_output
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (wit : ActionData)
    (cmOldValid : wit.cmOld.Valid)
    (akOnCurve : wit.akP.OnCurve)
    (middle root : Fp)
    (firstSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 0 wit.merklePath wit.cmOld.x 16 =
        some middle)
    (secondSucceeds :
      Sinsemilla.Merkle.CalculateRoot.pathNode
          G B.merkleQ 16
          (fun index => wit.merklePath (16 + index))
          middle 16 =
        some root)
    (anchorEquation : wit.vOld * (root - wit.anchor) = 0)
    (signValid : wit.sign = 1 ∨ wit.sign = -1)
    (valueCommitmentOne :
      wit.sign = 1 →
        (⟨wit.cvX, wit.cvY⟩ : Point Fp) =
          (wit.magnitude.val : Fq) • B.valueCommitV +
            wit.rcv.2 • B.valueCommitR)
    (valueCommitmentNegOne :
      wit.sign = -1 →
        (⟨wit.cvX, wit.cvY⟩ : Point Fp) =
          -(wit.magnitude.val : Fq) • B.valueCommitV +
            wit.rcv.2 • B.valueCommitR)
    (nullifierEquation :
      wit.nfOld =
        (wit.cmOld +
          ((Poseidon.Hash.ConstantLength.value
            #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
            B.nullifierK).x)
    (randomizedKeyEquation :
      (⟨wit.rkX, wit.rkY⟩ : Point Fp) =
        wit.alpha.2 • B.spendAuthG + wit.akP)
    (newNoteHashPoint : Point Fp)
    (newNoteHashDefined :
      Specs.Sinsemilla.hashToPoint G.S B.noteQ
        (NoteCommit.NoteCommitScalars.chunks
          (NoteCommit.noteScalars wit.gdNew wit.pkdNew
            wit.vNew wit.nfOld wit.psiNew)) =
        some newNoteHashPoint)
    (cmxEquation :
      wit.cmx =
        (newNoteHashPoint + wit.rcmNew.2 • B.noteCommitR).x) :
    output wit = ProofCore.coreOrchardAction (parameters G B) (input wit) := by
  have merkleCorrespondence :=
    merklePath_pointToZ_of_two_segments G B wit middle root
      firstSucceeds secondSucceeds
  have anchorCorrespondence :
      (if ActionGarden.baseEqual (fpToZ wit.vOld) ActionGarden.zZero
       then fpToZ wit.anchor
       else
        ProofCore.merkleRoot (parameters G B)
          (fpToZ wit.cmOld.x) (path wit)) =
        fpToZ wit.anchor := by
    rw [← fpToZ_zero, baseEqual_fpToZ]
    by_cases valueIsZero : wit.vOld = 0
    · simp only [valueIsZero, decide_true, ↓reduceIte]
    · simp only [valueIsZero, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [merkleCorrespondence.1]
      have rootMinusAnchorIsZero :
          root - wit.anchor = 0 :=
        (mul_eq_zero.mp anchorEquation).resolve_left valueIsZero
      have rootIsAnchor : root = wit.anchor :=
        sub_eq_zero.mp rootMinusAnchorIsZero
      rw [rootIsAnchor]
  have valueCommitmentCorrespondence :
      ProofCore.coreValueCommit (parameters G B)
          (ProofCore.coreSignedNetValue
            (fpToZ wit.magnitude) (fpToZ wit.sign))
          (fqToZ wit.rcv.2) =
        pointToZ (⟨wit.cvX, wit.cvY⟩ : Point Fp) := by
    rcases signValid with signIsOne | signIsNegOne
    · rw [signIsOne]
      have mapped :=
        valueCommit_pointToZ_one B G wit.magnitude wit.rcv.2
      exact mapped.trans
        (congrArg pointToZ
          (valueCommitmentOne signIsOne)).symm
    · rw [signIsNegOne]
      have mapped :=
        valueCommit_pointToZ_negOne B G wit.magnitude wit.rcv.2
      exact mapped.trans
        (congrArg pointToZ
          (valueCommitmentNegOne signIsNegOne)).symm
  have nullifierCorrespondence :=
    nullifier_pointToZ B G wit.nk wit.rhoOld wit.psiOld
      wit.cmOld cmOldValid
  rw [← nullifierEquation] at nullifierCorrespondence
  have randomizedKeyCorrespondence :=
    spendAuthRandomize_pointToZ B G wit.akP wit.alpha.2 akOnCurve
  rw [← randomizedKeyEquation] at randomizedKeyCorrespondence
  have newNoteCorrespondence :=
    noteCommit_pointToZ_of_some G B wit.gdNew wit.pkdNew
      wit.vNew wit.nfOld wit.psiNew wit.rcmNew.2
      newNoteHashPoint newNoteHashDefined
  have cmxCorrespondence :=
    congrArg ActionGarden.extractX newNoteCorrespondence.1
  rw [extractX_pointToZ, ← cmxEquation] at cmxCorrespondence
  unfold output ProofCore.coreOrchardAction input
  simp only
  rw [anchorCorrespondence]
  rw [valueCommitmentCorrespondence]
  rw [nullifierCorrespondence]
  rw [randomizedKeyCorrespondence]
  rw [cmxCorrespondence]

/-- A canonical all-zero replacement for each erased 3-bit window array. -/
def zeroWindows : Vector Fp 85 :=
  Vector.ofFn (fun _ : Fin 85 => 0)

/-- The field-valued net commitment selected by the valid `±1` sign. -/
def honestValueCommitment (B : Bases) (wit : ActionData) : Point Fp :=
  if wit.sign = 1
  then
    (wit.magnitude.val : Fq) • B.valueCommitV +
      wit.rcv.2 • B.valueCommitR
  else
    -(wit.magnitude.val : Fq) • B.valueCommitV +
      wit.rcv.2 • B.valueCommitR

/-- Fill exactly the data erased by `input`: public outputs and the five
fixed-base window arrays.  All projected private inputs and scalar values are
preserved. -/
def honestCompletion
    (B : Bases) (wit : ActionData)
    (newNoteHashPoint : Point Fp) : ActionData :=
  let nullifierValue :=
    (wit.cmOld +
      ((Poseidon.Hash.ConstantLength.value
        #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
        B.nullifierK).x
  let randomizedKey := wit.alpha.2 • B.spendAuthG + wit.akP
  let valueCommitment := honestValueCommitment B wit
  {
    wit with
    cvX := valueCommitment.x
    cvY := valueCommitment.y
    nfOld := nullifierValue
    rkX := randomizedKey.x
    rkY := randomizedKey.y
    cmx :=
      (newNoteHashPoint + wit.rcmNew.2 • B.noteCommitR).x
    rcv := (zeroWindows, wit.rcv.2)
    alpha := (zeroWindows, wit.alpha.2)
    rivk := (zeroWindows, wit.rivk.2)
    rcmOld := (zeroWindows, wit.rcmOld.2)
    rcmNew := (zeroWindows, wit.rcmNew.2)
  }

/-- Completion changes no standalone input field. -/
theorem input_honestCompletion
    (B : Bases) (wit : ActionData)
    (newNoteHashPoint : Point Fp) :
    input (honestCompletion B wit newNoteHashPoint) = input wit := by
  rfl

/-- Every valid projected standalone input has an honest Ironwood completion.
Only the five erased window arrays and five erased public outputs are filled;
`input_honestCompletion` proves that no standalone input changes. -/
theorem coreValidActionInputs_has_proverCompletion
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp)
    (valid :
      ProofCore.coreValidActionInputs (parameters G B) (input wit)) :
    ∃ completed : ActionData,
      input completed = input wit ∧
      ProverAssumptionsPost G B proverValue completed hint := by
  unfold ProofCore.coreValidActionInputs at valid
  rcases valid with
    ⟨_parametersValid, typed, ranges, values,
     ownership, merkle, newNote⟩
  rcases actionPoints_of_typed_input wit typed with
    ⟨cmOldValid, gdOldOnCurve, akOnCurve, pkdOldOnCurve,
     gdNewOnCurve, pkdNewOnCurve⟩
  rcases actionRanges_of_valid_input wit ranges with
    ⟨vOldRange, vNewRange, magnitudeRange, signValid⟩
  rcases actionValues_of_constraints_input wit values with
    ⟨valueEquation, spendEquation, outputEquation, crossAddress⟩
  rcases actionOwnership_of_valid_input G B wit ownership with
    ⟨⟨ivkHashPoint, ivkHashDefined, pkdEquation⟩,
     ⟨oldNoteHashPoint, oldNoteHashDefined, cmOldEquation⟩⟩
  rcases actionMerkle_of_valid_input G B wit merkle with
    ⟨middle, firstSucceeds, root, secondSucceeds, anchorEquation⟩
  rcases
      actionNewNote_of_valid_input G B wit cmOldValid newNote with
    ⟨newNoteHashPoint, newNoteHashDefined⟩
  have zeroWindowsValid :
      ∀ window : Fin 85,
        (zeroWindows[window.val]).val < 8 := by
    intro window
    simp [zeroWindows]
  have valueCommitmentOne :
      (honestCompletion B wit newNoteHashPoint).sign = 1 →
        (⟨(honestCompletion B wit newNoteHashPoint).cvX,
          (honestCompletion B wit newNoteHashPoint).cvY⟩ : Point Fp) =
          (wit.magnitude.val : Fq) • B.valueCommitV +
            wit.rcv.2 • B.valueCommitR := by
    intro signIsOne
    change honestValueCommitment B wit =
      (wit.magnitude.val : Fq) • B.valueCommitV +
        wit.rcv.2 • B.valueCommitR
    unfold honestValueCommitment
    simp only [honestCompletion] at signIsOne
    simp only [signIsOne, ↓reduceIte]
  have valueCommitmentNegOne :
      (honestCompletion B wit newNoteHashPoint).sign = -1 →
        (⟨(honestCompletion B wit newNoteHashPoint).cvX,
          (honestCompletion B wit newNoteHashPoint).cvY⟩ : Point Fp) =
          -(wit.magnitude.val : Fq) • B.valueCommitV +
            wit.rcv.2 • B.valueCommitR := by
    intro signIsNegOne
    change honestValueCommitment B wit =
      -(wit.magnitude.val : Fq) • B.valueCommitV +
        wit.rcv.2 • B.valueCommitR
    unfold honestValueCommitment
    simp only [honestCompletion] at signIsNegOne
    have signIsNotOne : wit.sign ≠ (1 : Fp) := by
      intro signIsOne
      rw [signIsOne] at signIsNegOne
      have oneIsNotNegOne : (1 : Fp) ≠ (-1 : Fp) := by
        native_decide
      exact oneIsNotNegOne signIsNegOne
    simp only [signIsNotOne, ↓reduceIte]
  refine
    ⟨honestCompletion B wit newNoteHashPoint,
     input_honestCompletion B wit newNoteHashPoint, ?_⟩
  unfold ProverAssumptionsPost
  constructor
  · unfold ProverAssumptions
    simp only [honestCompletion]
    exact
      ⟨cmOldValid, gdOldOnCurve, akOnCurve, pkdOldOnCurve,
       gdNewOnCurve, pkdNewOnCurve,
       zeroWindowsValid, zeroWindowsValid, zeroWindowsValid,
       zeroWindowsValid, zeroWindowsValid,
       magnitudeRange, signValid, vOldRange, vNewRange,
       ⟨middle, firstSucceeds, root, secondSucceeds, anchorEquation⟩,
       ⟨ivkHashPoint, ivkHashDefined, pkdEquation⟩,
       ⟨oldNoteHashPoint, oldNoteHashDefined, cmOldEquation⟩,
       ⟨newNoteHashPoint, newNoteHashDefined, rfl⟩,
       ⟨valueCommitmentOne, valueCommitmentNegOne⟩,
       rfl, rfl,
       valueEquation, spendEquation, outputEquation⟩
  · simpa only [honestCompletion] using crossAddress

/-- Every Ironwood honest-prover witness satisfies the standalone input
predicate.  The five fixed-base window hypotheses remain on the Ironwood side:
the standalone projection stores the reconstructed scalars, not their
circuit-specific 3-bit decompositions. -/
theorem proverAssumptionsPost_implies_coreValidActionInputs
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp)
    (assumptions :
      ProverAssumptionsPost G B proverValue wit hint) :
    ProofCore.coreValidActionInputs (parameters G B) (input wit) := by
  rcases assumptions with ⟨baseAssumptions, crossAddress⟩
  rcases baseAssumptions with
    ⟨cmOldValid, gdOldOnCurve, akOnCurve, pkdOldOnCurve,
     gdNewOnCurve, pkdNewOnCurve,
     _rcvWindows, _alphaWindows, _rivkWindows,
     _rcmOldWindows, _rcmNewWindows,
     magnitudeRange, signValid, vOldRange, vNewRange,
     merkleAssumptions, ivkAssumptions,
     oldNoteAssumptions, newNoteAssumptions,
     valueCommitmentAssumptions,
     nullifierEquation, randomizedKeyEquation,
     valueEquation, spendEquation, outputEquation⟩
  rcases merkleAssumptions with
    ⟨middle, firstSucceeds, root, secondSucceeds, anchorEquation⟩
  rcases ivkAssumptions with
    ⟨ivkHashPoint, ivkHashDefined, pkdEquation⟩
  rcases oldNoteAssumptions with
    ⟨oldNoteHashPoint, oldNoteHashDefined, cmOldEquation⟩
  rcases newNoteAssumptions with
    ⟨newNoteHashPoint, newNoteHashDefined, cmxEquation⟩
  rcases valueCommitmentAssumptions with
    ⟨valueCommitmentOne, valueCommitmentNegOne⟩
  unfold ProofCore.coreValidActionInputs
  exact
    ⟨coreParametersValid G B,
     actionInputsTyped_input wit cmOldValid gdOldOnCurve
      akOnCurve pkdOldOnCurve gdNewOnCurve pkdNewOnCurve,
     actionRangesValid_input wit vOldRange vNewRange
      magnitudeRange signValid,
     actionValueConstraints_input wit valueEquation spendEquation
      outputEquation crossAddress,
     actionOwnershipValid_input G B wit
      ivkHashPoint oldNoteHashPoint
      ivkHashDefined pkdEquation
      oldNoteHashDefined cmOldEquation,
     actionMerkleValid_input G B wit middle root
      firstSucceeds secondSucceeds anchorEquation,
     actionNewNoteValid_input G B wit cmOldValid
      newNoteHashPoint nullifierEquation newNoteHashDefined⟩

/-- Exact input-predicate equivalence at the projection boundary.

`input` erases the five fixed-base window arrays and the five public output
fields, so an iff with the same `ActionData` would be false.  Existentially
quantifying an honest completion is the precise quotient statement: every
valid standalone projected input has such a completion, and every completion
projects back to a valid standalone input. -/
theorem coreValidActionInputs_iff_exists_proverAssumptionsPost
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp) :
    ProofCore.coreValidActionInputs (parameters G B) (input wit) ↔
    ∃ completed : ActionData,
      input completed = input wit ∧
      ProverAssumptionsPost G B proverValue completed hint := by
  constructor
  · exact
      coreValidActionInputs_has_proverCompletion
        G B proverValue wit hint
  · intro completion
    rcases completion with
      ⟨completed, sameInput, assumptions⟩
    have completedIsValid :=
      proverAssumptionsPost_implies_coreValidActionInputs
        G B proverValue completed hint assumptions
    rw [sameInput] at completedIsValid
    exact completedIsValid

/-- The same honest-prover assumptions identify the existing Ironwood public
output record with the standalone deterministic Action function.  This theorem
is intentionally separate from input validity so downstream translations can
compare the relation and the function independently. -/
theorem proverAssumptionsPost_implies_coreOrchardAction_output
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp)
    (assumptions :
      ProverAssumptionsPost G B proverValue wit hint) :
    output wit = ProofCore.coreOrchardAction (parameters G B) (input wit) := by
  rcases assumptions with ⟨baseAssumptions, _crossAddress⟩
  rcases baseAssumptions with
    ⟨cmOldValid, _gdOldOnCurve, akOnCurve, _pkdOldOnCurve,
     _gdNewOnCurve, _pkdNewOnCurve,
     _rcvWindows, _alphaWindows, _rivkWindows,
     _rcmOldWindows, _rcmNewWindows,
     _magnitudeRange, signValid, _vOldRange, _vNewRange,
     merkleAssumptions, _ivkAssumptions,
     _oldNoteAssumptions, newNoteAssumptions,
     valueCommitmentAssumptions,
     nullifierEquation, randomizedKeyEquation,
     _valueEquation, _spendEquation, _outputEquation⟩
  rcases merkleAssumptions with
    ⟨middle, firstSucceeds, root, secondSucceeds, anchorEquation⟩
  rcases newNoteAssumptions with
    ⟨newNoteHashPoint, newNoteHashDefined, cmxEquation⟩
  rcases valueCommitmentAssumptions with
    ⟨valueCommitmentOne, valueCommitmentNegOne⟩
  exact
    orchardAction_output G B wit cmOldValid akOnCurve
      middle root firstSucceeds secondSucceeds anchorEquation
      signValid valueCommitmentOne valueCommitmentNegOne
      nullifierEquation randomizedKeyEquation
      newNoteHashPoint newNoteHashDefined cmxEquation

/-! ## Direct public Garden-shaped equivalence

The `ProofCore` namespace above is proof-local scaffolding.  The statements
below expose the review surface that is translated to Rocq: the public
`validActionInputs` predicate and `orchardAction` function from
`ActionGarden.lean`. -/

/-- Typing is definitionally unchanged by the public record adapter. -/
theorem actionInputsTyped_fullInput_iff_core (wit : ActionData) :
    ActionGarden.actionInputsTyped (fullInput wit) ↔
      ProofCore.coreInputsTyped (input wit) := by
  rfl

/-- Value and flag equations are definitionally unchanged by the adapter. -/
theorem actionValueConstraints_fullInput_iff_core
    (wit : ActionData) :
    ActionGarden.actionValueConstraints (fullInput wit) ↔
      ProofCore.coreValueConstraints (input wit) := by
  rfl

/-- The public Garden-shaped IVK commitment computes the same point as
Ironwood and carries the same Sinsemilla definedness witness. -/
theorem commitIvkGarden_pointToZ_of_some
    (ak nk : Fp) (randomness : Fq) (hashPoint : Point Fp)
    (hashDefined :
      Specs.Sinsemilla.hashToPoint
          Specs.Sinsemilla.orchardGenerators.S
          Zcash.Circuits.Action.orchardBases.ivkQ
          (Specs.Sinsemilla.commitIvkChunks ak.val nk.val) =
        some hashPoint) :
    ActionGarden.commitIvk ActionGarden.orchardParams
        (fpToZ ak) (fpToZ nk) (fqToZ randomness) =
      pointToZ
        (hashPoint +
          randomness • Zcash.Circuits.Action.orchardBases.commitIvkR) ∧
    ActionGarden.sinsemillaHashDefinedGarden
      ActionGarden.orchardParams.commitIvkQ
      (ActionGarden.commitIvkMessageGarden
        (fpToZ ak) (fpToZ nk)) := by
  let chunks := Specs.Sinsemilla.commitIvkChunks ak.val nk.val
  have chunksInRange :
      ∀ chunk ∈ chunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  have hashCorrespondence :=
    sinsemillaHashGarden_of_some
      Zcash.Circuits.Action.orchardBases.ivkQ
      hashPoint chunks chunksInRange hashDefined
  have hashValid : hashPoint.Valid :=
    Specs.Sinsemilla.hashToPoint_valid
      (.inl Zcash.Circuits.Action.orchardBases.ivkQ_onCurve)
      (fun chunk membership => by
        simpa [Specs.K] using chunksInRange chunk membership)
      hashDefined
  have randomnessValid :
      (randomness •
        Zcash.Circuits.Action.orchardBases.commitIvkR).Valid :=
    Zcash.Circuits.Action.orchardBases.commitIvkR.smul_valid randomness
  have hashResult :
      ActionGarden.sinsemillaHashToPointGarden
          (pointToZ Zcash.Circuits.Action.ivkQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.commitIvkChunks ak.val nk.val)) =
        pointToZ hashPoint := by
    simpa only [chunks] using hashCorrespondence.1
  have hashIsDefined :
      ActionGarden.sinsemillaHashDefinedGarden
          (pointToZ Zcash.Circuits.Action.ivkQ)
          (List.map Int.ofNat
            (Specs.Sinsemilla.commitIvkChunks ak.val nk.val)) := by
    simpa only [chunks] using hashCorrespondence.2
  constructor
  · unfold ActionGarden.commitIvk
    simp only [ActionGarden.orchardParams]
    rw [orchardCommitIvkQ_deployed]
    rw [commitIvkMessageGarden_fpToZ]
    rw [hashResult]
    rw [orchardCommitIvkRG_deployed]
    rw [← pointToZ_fullScalarMul]
    rw [← pointToZ_addGarden
      hashPoint
      (randomness •
        Zcash.Circuits.Action.orchardBases.commitIvkR)
      hashValid randomnessValid]
  · simp only [ActionGarden.orchardParams]
    rw [orchardCommitIvkQ_deployed]
    rw [commitIvkMessageGarden_fpToZ]
    exact hashIsDefined

/-- Garden's base-field scalar conversion acts on any on-curve Pallas point
as Ironwood's raw natural scalar.  The proof makes the reduction modulo the
Pallas group order explicit. -/
theorem scalarMul_fpToZ_pointToZ
    (value : Fp) (point : Point Fp) (onCurve : point.OnCurve) :
    ActionGarden.scalarMul (fpToZ value) (pointToZ point) =
      pointToZ (value.val • point) := by
  unfold ActionGarden.scalarMul
  have normalization := baseToScalar_fpToZ value
  unfold ActionGarden.baseToScalar at normalization
  rw [baseNormalize_fpToZ] at normalization
  rw [normalization]
  change
    ActionGarden.pointNatMul (((value.val : Nat) : Fq).val)
        (pointToZ point) =
      pointToZ (value.val • point)
  rw [← pointToZ_nsmul]
  apply congrArg pointToZ
  apply Point.nsmul_congr onCurve
  rw [ZMod.val_natCast]
  exact Nat.mod_modEq _ _

theorem extractXGarden_pointToZ (point : Point Fp) :
    ActionGarden.extractXGarden (pointToZ point) = fpToZ point.x := by
  rfl

/-- All explicit public constants satisfy the parameter-validity group. -/
theorem actionParametersValid_orchard :
    ActionGarden.actionParametersValid ActionGarden.orchardParams := by
  unfold ActionGarden.actionParametersValid
  simp only [ActionGarden.orchardParams]
  rw [orchardNoteCommitQ_deployed, orchardCommitIvkQ_deployed,
    orchardMerkleCrhQ_deployed, orchardSpendAuthG_deployed,
    orchardValueCommitVG_deployed, orchardValueCommitRG_deployed,
    orchardNullifierKG_deployed, orchardNoteCommitRG_deployed,
    orchardCommitIvkRG_deployed]
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.noteQ, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.ivkQ, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.merkleQ, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.spendAuthG.point, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.valueCommitV.point, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.valueCommitR.point, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.nullifierK.point, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.noteCommitR.point, ?_⟩
  refine
    ⟨pointCanonical_pointToZ
        Zcash.Circuits.Action.orchardBases.commitIvkR.point, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.noteQ_onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.ivkQ_onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.merkleQ_onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.spendAuthG.onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.valueCommitV.onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.valueCommitR.onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.nullifierK.onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.noteCommitR.onCurve, ?_⟩
  refine
    ⟨pointOnCurve_pointToZ
        Zcash.Circuits.Action.orchardBases.commitIvkR.onCurve, ?_⟩
  intro word wordRange
  have nonnegative : Int.ofNat 0 ≤ word := wordRange.1
  have upperBound : Int.toNat word < 1024 := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg nonnegative]
    exact wordRange.2
  let index : Fin 1024 := ⟨Int.toNat word, upperBound⟩
  have wordIsIndex : word = Int.ofNat index.val := by
    change word = Int.ofNat (Int.toNat word)
    exact (Int.toNat_of_nonneg nonnegative).symm
  rw [wordIsIndex, orchardSinsemillaGenerator_deployed index]
  exact
    ⟨pointCanonical_pointToZ
        (Specs.Sinsemilla.orchardGenerators.S index.val),
     pointOnCurve_pointToZ
        (Specs.Sinsemilla.orchardGenerators.S_onCurve
          (by simpa [Specs.K] using upperBound))⟩

/-- Storing a layer beside each path row does not change the sibling-range
condition. -/
theorem gardenPathFrom_siblingRanges_iff
    (layer : Nat) (elements : List ProofCore.CorePathElement)
    (upper : ActionGarden.Z) :
    (∀ element,
        List.Mem element (gardenPathFrom layer elements) →
        ActionGarden.inRange element.2.1 upper) ↔
      (∀ element,
        List.Mem element elements →
        ActionGarden.inRange element.sibling upper) := by
  induction elements generalizing layer with
  | nil =>
      constructor
      · intro _ element membership
        nomatch membership
      · intro _ element membership
        nomatch membership
  | cons head tail inductionHypothesis =>
      constructor
      · intro gardenRanges
        intro element membership
        rcases List.mem_cons.mp membership with rfl | elementInTail
        ·
          exact gardenRanges
            (Int.ofNat layer, element.sibling, element.isRight)
            List.mem_cons_self
        · apply
            (inductionHypothesis (Nat.succ layer)).mp
              (fun gardenElement gardenMembership =>
                gardenRanges gardenElement
                  (List.mem_cons_of_mem
                    (Int.ofNat layer, head.sibling, head.isRight)
                    gardenMembership))
              element elementInTail
      · intro coreRanges
        intro element membership
        rcases List.mem_cons.mp membership with rfl | elementInTail
        ·
          exact coreRanges head List.mem_cons_self
        · apply
            (inductionHypothesis (Nat.succ layer)).mpr
              (fun coreElement coreMembership =>
                coreRanges coreElement
                  (List.mem_cons_of_mem head coreMembership))
              element elementInTail

theorem actionRangesValid_fullInput_iff_core (wit : ActionData) :
    ActionGarden.actionRangesValid (fullInput wit) ↔
      ProofCore.coreRangesValid (input wit) := by
  unfold ActionGarden.actionRangesValid ProofCore.coreRangesValid
  simp only [fullInput, gardenInput, input]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  unfold gardenPath
  exact gardenPathFrom_siblingRanges_iff 0 (path wit)
    (ActionGarden.zPowNat ActionGarden.zTwo 255)

/-- Core ownership validity implies the public ownership group. -/
theorem actionOwnershipValid_fullInput_of_core
    (wit : ActionData) (gdOldOnCurve : wit.gdOld.OnCurve)
    (valid :
      ProofCore.coreOwnershipValid
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (input wit)) :
    ActionGarden.actionOwnershipValid
      ActionGarden.orchardParams (fullInput wit) := by
  rcases
      actionOwnership_of_valid_input
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases wit valid with
    ⟨⟨ivkHashPoint, ivkHashDefined, pkdEquation⟩,
     ⟨oldNoteHashPoint, oldNoteHashDefined, cmOldEquation⟩⟩
  have ivkCorrespondence :=
    commitIvkGarden_pointToZ_of_some
      wit.akP.x wit.nk wit.rivk.2 ivkHashPoint ivkHashDefined
  have oldNoteCorrespondence :=
    noteCommitGarden_pointToZ_of_some
      wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld
      wit.rcmOld.2 oldNoteHashPoint oldNoteHashDefined
  unfold ActionGarden.actionOwnershipValid
  simp only [fullInput, gardenInput]
  refine
    ⟨ivkCorrespondence.2, ?_,
     oldNoteCorrespondence.2, ?_⟩
  · rw [extractXGarden_pointToZ]
    rw [ivkCorrespondence.1]
    rw [extractXGarden_pointToZ]
    rw [scalarMul_fpToZ_pointToZ _ _ gdOldOnCurve]
    rw [pkdEquation]
  · rw [oldNoteCorrespondence.1]
    rw [cmOldEquation]

/-- Public ownership validity reconstructs the successful Ironwood
Sinsemilla computations and therefore the Core ownership group. -/
theorem actionOwnershipValid_core_of_fullInput
    (wit : ActionData) (gdOldOnCurve : wit.gdOld.OnCurve)
    (valid :
      ActionGarden.actionOwnershipValid
        ActionGarden.orchardParams (fullInput wit)) :
    ProofCore.coreOwnershipValid
      (parameters Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases)
      (input wit) := by
  unfold ActionGarden.actionOwnershipValid at valid
  simp only [fullInput, gardenInput] at valid
  rw [extractXGarden_pointToZ] at valid
  rcases valid with
    ⟨ivkDefined, pkdEquation, oldNoteDefined, cmOldEquation⟩
  have ivkDefinedMapped := ivkDefined
  simp only [ActionGarden.orchardParams] at ivkDefinedMapped
  rw [orchardCommitIvkQ_deployed] at ivkDefinedMapped
  rw [commitIvkMessageGarden_fpToZ] at ivkDefinedMapped
  let ivkChunks :=
    Specs.Sinsemilla.commitIvkChunks wit.akP.x.val wit.nk.val
  have ivkChunksInRange :
      ∀ chunk ∈ ivkChunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  rcases
      sinsemillaHashSome_of_gardenDefined
        Zcash.Circuits.Action.orchardBases.ivkQ
        ivkChunks ivkChunksInRange
        (by simpa only [ivkChunks] using ivkDefinedMapped) with
    ⟨ivkHashPoint, ivkHashDefined, _ivkPublicResult⟩
  have ivkCorrespondence :=
    commitIvkGarden_pointToZ_of_some
      wit.akP.x wit.nk wit.rivk.2 ivkHashPoint ivkHashDefined
  rw [ivkCorrespondence.1] at pkdEquation
  rw [extractXGarden_pointToZ] at pkdEquation
  rw [scalarMul_fpToZ_pointToZ _ _ gdOldOnCurve] at pkdEquation
  have pkdFieldEquation :
      wit.pkdOld =
        ((ivkHashPoint +
          wit.rivk.2 •
            Zcash.Circuits.Action.orchardBases.commitIvkR).x).val •
          wit.gdOld :=
    pointToZ_injective pkdEquation
  have oldNoteDefinedMapped := oldNoteDefined
  simp only [ActionGarden.orchardParams] at oldNoteDefinedMapped
  rw [orchardNoteCommitQ_deployed] at oldNoteDefinedMapped
  rw [noteCommitMessageGarden_pointToZ] at oldNoteDefinedMapped
  let oldNoteChunks :=
    NoteCommit.NoteCommitScalars.chunks
      (NoteCommit.noteScalars wit.gdOld wit.pkdOld
        wit.vOld wit.rhoOld wit.psiOld)
  have oldNoteChunksInRange :
      ∀ chunk ∈ oldNoteChunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  rcases
      sinsemillaHashSome_of_gardenDefined
        Zcash.Circuits.Action.orchardBases.noteQ
        oldNoteChunks oldNoteChunksInRange
        (by simpa only [oldNoteChunks] using oldNoteDefinedMapped) with
    ⟨oldNoteHashPoint, oldNoteHashDefined, _oldNotePublicResult⟩
  have oldNoteCorrespondence :=
    noteCommitGarden_pointToZ_of_some
      wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld
      wit.rcmOld.2 oldNoteHashPoint oldNoteHashDefined
  rw [oldNoteCorrespondence.1] at cmOldEquation
  have cmOldFieldEquation :
      wit.cmOld =
        oldNoteHashPoint +
          wit.rcmOld.2 •
            Zcash.Circuits.Action.orchardBases.noteCommitR :=
    pointToZ_injective cmOldEquation
  exact
    actionOwnershipValid_input
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases wit
      ivkHashPoint oldNoteHashPoint ivkHashDefined
      pkdFieldEquation oldNoteHashDefined cmOldFieldEquation

/-- Adding explicit layer fields preserves path length. -/
theorem gardenPathFrom_length
    (layer : Nat) (elements : List ProofCore.CorePathElement) :
    (gardenPathFrom layer elements).length = elements.length := by
  induction elements generalizing layer with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp only [gardenPathFrom, List.length_cons]
      exact congrArg Nat.succ
        (inductionHypothesis (Nat.succ layer))

theorem gardenPath_length (wit : ActionData) :
    (gardenPath wit).length = 32 := by
  unfold gardenPath
  rw [gardenPathFrom_length]
  unfold path
  exact pathSegment_length wit.merklePath 32

/-- Core Merkle validity gives exactly Garden's length, layer, definedness,
leaf, and anchor clauses. -/
theorem actionMerkleValid_fullInput_of_core
    (wit : ActionData)
    (valid :
      ProofCore.coreMerkleValid
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (input wit)) :
    ActionGarden.actionMerkleValid
      ActionGarden.orchardParams (fullInput wit) := by
  unfold ProofCore.coreMerkleValid at valid
  simp only [input] at valid
  rw [extractX_pointToZ] at valid
  rcases valid with
    ⟨_depth, pathDefined, leafEquation, anchorEquation⟩
  have pathCorrespondence :=
    merklePathGarden_of_coreValid wit pathDefined
  unfold ActionGarden.actionMerkleValid
  simp only [fullInput, gardenInput]
  refine
    ⟨gardenPath_length wit,
     pathLayersCanonical_gardenPath wit,
     pathCorrespondence.2, ?_, ?_⟩
  · exact leafEquation
  · rcases anchorEquation with zeroValue | nonzeroValue
    · exact Or.inl zeroValue
    · exact Or.inr (nonzeroValue.trans pathCorrespondence.1.symm)

/-- Garden Merkle validity reconstructs Core path definedness and the same
root. -/
theorem actionMerkleValid_core_of_fullInput
    (wit : ActionData)
    (valid :
      ActionGarden.actionMerkleValid
        ActionGarden.orchardParams (fullInput wit)) :
    ProofCore.coreMerkleValid
      (parameters Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases)
      (input wit) := by
  unfold ActionGarden.actionMerkleValid at valid
  simp only [fullInput, gardenInput] at valid
  rcases valid with
    ⟨_length, _layers, pathDefined, leafEquation, anchorEquation⟩
  have pathCorrespondence :=
    coreMerklePath_of_gardenValid wit pathDefined
  unfold ProofCore.coreMerkleValid
  simp only [input]
  refine
    ⟨pathDepth_path wit, pathCorrespondence.1, ?_, ?_⟩
  · rw [extractX_pointToZ]
  · rcases anchorEquation with zeroValue | nonzeroValue
    · exact Or.inl zeroValue
    · exact Or.inr (nonzeroValue.trans pathCorrespondence.2)

/-- Core new-note definedness implies the public Garden-shaped clause. -/
theorem actionNewNoteValid_fullInput_of_core
    (wit : ActionData) (cmOldValid : wit.cmOld.Valid)
    (valid :
      ProofCore.coreNewNoteValid
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (input wit)) :
    ActionGarden.actionNewNoteValid
      ActionGarden.orchardParams (fullInput wit) := by
  rcases
      actionNewNote_of_valid_input
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases wit cmOldValid valid with
    ⟨newNoteHashPoint, newNoteHashDefined⟩
  let nfField : Fp :=
    (wit.cmOld +
      ((Poseidon.Hash.ConstantLength.value
        #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
        Zcash.Circuits.Action.orchardBases.nullifierK).x
  let chunks :=
    NoteCommit.NoteCommitScalars.chunks
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew
        wit.vNew nfField wit.psiNew)
  have chunksInRange :
      ∀ chunk ∈ chunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  have hashCorrespondence :=
    sinsemillaHashGarden_of_some
      Zcash.Circuits.Action.orchardBases.noteQ
      newNoteHashPoint chunks chunksInRange
      (by simpa only [nfField, chunks] using newNoteHashDefined)
  unfold ActionGarden.actionNewNoteValid
  simp only [fullInput, gardenInput]
  rw [nullifierGarden_pointToZ
    wit.nk wit.rhoOld wit.psiOld wit.cmOld cmOldValid]
  change
    ActionGarden.sinsemillaHashDefinedGarden
      ActionGarden.orchardParams.noteCommitQ
      (ActionGarden.noteCommitMessageGarden
        (pointToZ wit.gdNew) (pointToZ wit.pkdNew)
        (fpToZ wit.vNew) (fpToZ nfField) (fpToZ wit.psiNew))
  simp only [ActionGarden.orchardParams]
  rw [orchardNoteCommitQ_deployed]
  rw [noteCommitMessageGarden_pointToZ]
  simpa only [chunks] using hashCorrespondence.2

/-- The public new-note clause reconstructs Core Sinsemilla definedness. -/
theorem actionNewNoteValid_core_of_fullInput
    (wit : ActionData) (cmOldValid : wit.cmOld.Valid)
    (valid :
      ActionGarden.actionNewNoteValid
        ActionGarden.orchardParams (fullInput wit)) :
    ProofCore.coreNewNoteValid
      (parameters Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases)
      (input wit) := by
  let nfField : Fp :=
    (wit.cmOld +
      ((Poseidon.Hash.ConstantLength.value
        #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq) •
        Zcash.Circuits.Action.orchardBases.nullifierK).x
  let chunks :=
    NoteCommit.NoteCommitScalars.chunks
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew
        wit.vNew nfField wit.psiNew)
  have chunksInRange :
      ∀ chunk ∈ chunks, chunk < 1024 :=
    fun chunk membership => chunksOf_mem_lt_1024 membership
  unfold ActionGarden.actionNewNoteValid at valid
  simp only [fullInput, gardenInput] at valid
  rw [nullifierGarden_pointToZ
    wit.nk wit.rhoOld wit.psiOld wit.cmOld cmOldValid] at valid
  change
    ActionGarden.sinsemillaHashDefinedGarden
      ActionGarden.orchardParams.noteCommitQ
      (ActionGarden.noteCommitMessageGarden
        (pointToZ wit.gdNew) (pointToZ wit.pkdNew)
        (fpToZ wit.vNew) (fpToZ nfField) (fpToZ wit.psiNew))
    at valid
  simp only [ActionGarden.orchardParams] at valid
  rw [orchardNoteCommitQ_deployed] at valid
  rw [noteCommitMessageGarden_pointToZ] at valid
  rcases
      sinsemillaHashSome_of_gardenDefined
        Zcash.Circuits.Action.orchardBases.noteQ
        chunks chunksInRange
        (by simpa only [chunks] using valid) with
    ⟨newNoteHashPoint, newNoteHashDefined, _publicResult⟩
  have coreCorrespondence :=
    sinsemillaHashToPoint_of_some
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases
      Zcash.Circuits.Action.orchardBases.noteQ
      newNoteHashPoint chunks
      (by simpa only [chunks] using newNoteHashDefined)
  unfold ProofCore.coreNewNoteValid
  simp only [input]
  rw [nullifier_pointToZ
    Zcash.Circuits.Action.orchardBases
    Specs.Sinsemilla.orchardGenerators
    wit.nk wit.rhoOld wit.psiOld wit.cmOld cmOldValid]
  change
    ProofCore.sinsemillaHashDefined
      (parameters Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases)
      (pointToZ Zcash.Circuits.Action.orchardBases.noteQ)
      (ProofCore.noteCommitChunks
        (pointToZ wit.gdNew) (pointToZ wit.pkdNew)
        (fpToZ wit.vNew) (fpToZ nfField) (fpToZ wit.psiNew))
  rw [noteCommitChunks_pointToZ]
  simpa only [parameters, chunks] using coreCorrespondence.2

/-- The seven public validity groups are exactly the seven proof-local Core
groups on an Ironwood `ActionData` projection. -/
theorem validActionInputs_fullInput_iff_core (wit : ActionData) :
    ActionGarden.validActionInputs
        ActionGarden.orchardParams (fullInput wit) ↔
      ProofCore.coreValidActionInputs
        (parameters Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases)
        (input wit) := by
  constructor
  · intro gardenValid
    unfold ActionGarden.validActionInputs at gardenValid
    rcases gardenValid with
      ⟨_parametersValid, typed, ranges, values,
       ownership, merkle, newNote⟩
    have coreTyped :
        ProofCore.coreInputsTyped (input wit) :=
      (actionInputsTyped_fullInput_iff_core wit).mp typed
    rcases actionPoints_of_typed_input wit coreTyped with
      ⟨cmOldValid, gdOldOnCurve, _akOnCurve, _pkdOldOnCurve,
       _gdNewOnCurve, _pkdNewOnCurve⟩
    unfold ProofCore.coreValidActionInputs
    exact
      ⟨coreParametersValid
          Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases,
       coreTyped,
       (actionRangesValid_fullInput_iff_core wit).mp ranges,
       (actionValueConstraints_fullInput_iff_core wit).mp values,
       actionOwnershipValid_core_of_fullInput
         wit gdOldOnCurve ownership,
       actionMerkleValid_core_of_fullInput wit merkle,
       actionNewNoteValid_core_of_fullInput
         wit cmOldValid newNote⟩
  · intro coreValid
    unfold ProofCore.coreValidActionInputs at coreValid
    rcases coreValid with
      ⟨_parametersValid, typed, ranges, values,
       ownership, merkle, newNote⟩
    rcases actionPoints_of_typed_input wit typed with
      ⟨cmOldValid, gdOldOnCurve, _akOnCurve, _pkdOldOnCurve,
       _gdNewOnCurve, _pkdNewOnCurve⟩
    unfold ActionGarden.validActionInputs
    exact
      ⟨actionParametersValid_orchard,
       (actionInputsTyped_fullInput_iff_core wit).mpr typed,
       (actionRangesValid_fullInput_iff_core wit).mpr ranges,
       (actionValueConstraints_fullInput_iff_core wit).mpr values,
       actionOwnershipValid_fullInput_of_core
         wit gdOldOnCurve ownership,
       actionMerkleValid_fullInput_of_core wit merkle,
       actionNewNoteValid_fullInput_of_core
         wit cmOldValid newNote⟩

/-- Rebuild the public full input from the proof-local representation.  This
is the explicit inverse on values produced by `input`; it reinstalls the
canonical consecutive Merkle layers. -/
def fullInputOfCore
    (core : ProofCore.CoreActionInputs) :
    ActionGarden.FullActionInputs :=
  {
    action := {
      inAk := core.ak
      inNk := core.nk
      inRhoOld := core.rhoOld
      inPsiOld := core.psiOld
      inCmOld := core.cmOld
      inGdOld := core.gdOld
      inPkdOld := core.pkdOld
      inVOld := core.vOld
      inRivk := core.rivk
      inAlpha := core.alpha
      inAnchorPublic := core.anchorPublic
      inRcv := core.rcv
      inMagnitude := core.magnitude
      inSign := core.sign
      inLeaf := core.leaf
      inPath := gardenPathFrom 0 core.path
      inGdNew := core.gdNew
      inPkdNew := core.pkdNew
      inVNew := core.vNew
      inPsiNew := core.psiNew
      inRcmNew := core.rcmNew
    }
    rcmOld := core.rcmOld
    enableSpend := core.enableSpend
    enableOutput := core.enableOutput
    disableCrossAddress := core.disableCrossAddress
  }

theorem fullInputOfCore_input (wit : ActionData) :
    fullInputOfCore (input wit) = fullInput wit := by
  rfl

theorem fullInput_eq_of_input_eq
    {left right : ActionData}
    (equality : input left = input right) :
    fullInput left = fullInput right := by
  rw [← fullInputOfCore_input left]
  rw [← fullInputOfCore_input right]
  exact congrArg fullInputOfCore equality

/-- Review-facing input theorem.

`fullInput` erases the five fixed-base window arrays and the five stored
output fields.  Existential honest completion is therefore the exact quotient
statement, now expressed solely with the public Garden-shaped predicate. -/
theorem validActionInputs_iff_exists_proverAssumptionsPost
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp) :
    ActionGarden.validActionInputs
        ActionGarden.orchardParams (fullInput wit) ↔
      ∃ completed : ActionData,
        fullInput completed = fullInput wit ∧
        ProverAssumptionsPost
          Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases
          proverValue completed hint := by
  rw [validActionInputs_fullInput_iff_core]
  constructor
  · intro coreValid
    rcases
        coreValidActionInputs_has_proverCompletion
          Specs.Sinsemilla.orchardGenerators
          Zcash.Circuits.Action.orchardBases
          proverValue wit hint coreValid with
      ⟨completed, sameInput, assumptions⟩
    exact
      ⟨completed, fullInput_eq_of_input_eq sameInput, assumptions⟩
  · rintro ⟨completed, sameFullInput, assumptions⟩
    have completedValid :=
      proverAssumptionsPost_implies_coreValidActionInputs
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        proverValue completed hint assumptions
    have sameCoreInput : input completed = input wit := by
      rw [← coreInputOfFull_fullInput completed]
      rw [sameFullInput]
      exact coreInputOfFull_fullInput wit
    rw [sameCoreInput] at completedValid
    exact completedValid

/-- The standalone integer randomization agrees with Ironwood's native
spend-authorizing-key randomization after encoding both points. -/
theorem spendAuthRandomizeGarden_pointToZ
    (ak : Point Fp) (alpha : Fq) (akOnCurve : ak.OnCurve) :
    ActionGarden.spendAuthRandomize
        (pointToZ ak) (fqToZ alpha) =
      pointToZ
        (alpha • Zcash.Circuits.Action.orchardBases.spendAuthG + ak) := by
  have randomizedValid :
      (alpha •
        Zcash.Circuits.Action.orchardBases.spendAuthG).Valid :=
    Zcash.Circuits.Action.orchardBases.spendAuthG.smul_valid alpha
  unfold ActionGarden.spendAuthRandomize
  rw [orchardSpendAuthG_deployed]
  rw [← pointToZ_fullScalarMul]
  rw [← pointToZ_addGarden
    ak
    (alpha • Zcash.Circuits.Action.orchardBases.spendAuthG)
    (.inl akOnCurve) randomizedValid]
  apply congrArg pointToZ
  exact Point.add_comm (.inl akOnCurve) randomizedValid

theorem scalarNormalize_zNeg_fpToZ (value : Fp) :
    ActionGarden.scalarNormalize
        (ActionGarden.zNeg (fpToZ value)) =
      fqToZ (-((value.val : Nat) : Fq)) := by
  rw [← fqToZ_zToFq]
  apply congrArg fqToZ
  unfold zToFq ActionGarden.zNeg
  rw [show
    (Int.cast (Int.neg (fpToZ value)) : Fq) =
      -Int.cast (fpToZ value) from Int.cast_neg (fpToZ value)]
  rfl

theorem signedNetValueGarden_one (magnitude : Fp) :
    ActionGarden.signedNetValue
        (fpToZ magnitude) (fpToZ (1 : Fp)) =
      fpToZ magnitude := by
  unfold ActionGarden.signedNetValue
  rw [fpToZ_one]
  unfold ActionGarden.zEq
  simp only [decide_true, ↓reduceIte]

theorem signedNetValueGarden_negOne (magnitude : Fp) :
    ActionGarden.signedNetValue
        (fpToZ magnitude) (fpToZ (-1 : Fp)) =
      ActionGarden.zNeg (fpToZ magnitude) := by
  unfold ActionGarden.signedNetValue
  have negOneNotOne : fpToZ (-1 : Fp) ≠ ActionGarden.zOne := by
    rw [← fpToZ_one]
    exact fun equality =>
      (show (-1 : Fp) ≠ 1 by native_decide)
        (fpToZ_injective equality)
  unfold ActionGarden.zEq
  simp only [negOneNotOne, decide_false, Bool.false_eq_true,
    ↓reduceIte]

theorem scalarMul_zNeg_fpToZ
    (base : Ecc.MulFixed.Short.FixedBase) (magnitude : Fp) :
    ActionGarden.scalarMul
        (ActionGarden.zNeg (fpToZ magnitude))
        (pointToZ base.point) =
      pointToZ
        ((-((magnitude.val : Nat) : Fq)) • base) := by
  unfold ActionGarden.scalarMul
  rw [scalarNormalize_zNeg_fpToZ]
  change
    ActionGarden.pointNatMul
        ((-((magnitude.val : Nat) : Fq)).val)
        (pointToZ base.point) =
      pointToZ
        ((-((magnitude.val : Nat) : Fq)).val • base.point)
  exact
    (pointToZ_nsmul
      (-((magnitude.val : Nat) : Fq)).val base.point).symm

theorem pointToZ_baseScalarMul_short
    (base : Ecc.MulFixed.Short.FixedBase) (value : Fp) :
    ActionGarden.scalarMul (fpToZ value) (pointToZ base.point) =
      pointToZ (((value.val : Nat) : Fq) • base) := by
  rw [pointToZ_shortScalarMul]
  unfold ActionGarden.scalarMul
  have normalization := baseToScalar_fpToZ value
  unfold ActionGarden.baseToScalar at normalization
  rw [baseNormalize_fpToZ] at normalization
  rw [normalization]
  rw [scalarNormalize_fqToZ]

theorem valueCommitGarden_pointToZ_one
    (magnitude : Fp) (randomness : Fq) :
    ActionGarden.valueCommit
        (ActionGarden.signedNetValue
          (fpToZ magnitude) (fpToZ (1 : Fp)))
        (fqToZ randomness) =
      pointToZ
        (((magnitude.val : Nat) : Fq) •
            Zcash.Circuits.Action.orchardBases.valueCommitV +
          randomness •
            Zcash.Circuits.Action.orchardBases.valueCommitR) := by
  rw [signedNetValueGarden_one]
  unfold ActionGarden.valueCommit
  rw [orchardValueCommitVG_deployed, orchardValueCommitRG_deployed]
  rw [pointToZ_baseScalarMul_short
    Zcash.Circuits.Action.orchardBases.valueCommitV magnitude]
  rw [← pointToZ_fullScalarMul
    Zcash.Circuits.Action.orchardBases.valueCommitR randomness]
  rw [← pointToZ_addGarden
    (((magnitude.val : Nat) : Fq) •
      Zcash.Circuits.Action.orchardBases.valueCommitV)
    (randomness •
      Zcash.Circuits.Action.orchardBases.valueCommitR)
    (Zcash.Circuits.Action.orchardBases.valueCommitV.smul_valid _)
    (Zcash.Circuits.Action.orchardBases.valueCommitR.smul_valid _)]

theorem valueCommitGarden_pointToZ_negOne
    (magnitude : Fp) (randomness : Fq) :
    ActionGarden.valueCommit
        (ActionGarden.signedNetValue
          (fpToZ magnitude) (fpToZ (-1 : Fp)))
        (fqToZ randomness) =
      pointToZ
        ((-((magnitude.val : Nat) : Fq)) •
            Zcash.Circuits.Action.orchardBases.valueCommitV +
          randomness •
            Zcash.Circuits.Action.orchardBases.valueCommitR) := by
  rw [signedNetValueGarden_negOne]
  unfold ActionGarden.valueCommit
  rw [orchardValueCommitVG_deployed, orchardValueCommitRG_deployed]
  rw [scalarMul_zNeg_fpToZ
    Zcash.Circuits.Action.orchardBases.valueCommitV magnitude]
  rw [← pointToZ_fullScalarMul
    Zcash.Circuits.Action.orchardBases.valueCommitR randomness]
  rw [← pointToZ_addGarden
    ((-((magnitude.val : Nat) : Fq)) •
      Zcash.Circuits.Action.orchardBases.valueCommitV)
    (randomness •
      Zcash.Circuits.Action.orchardBases.valueCommitR)
    (Zcash.Circuits.Action.orchardBases.valueCommitV.smul_valid _)
    (Zcash.Circuits.Action.orchardBases.valueCommitR.smul_valid _)]

/-- Review-facing output theorem.

Every output field computed by the standalone Garden-shaped function is the
integer encoding of the corresponding native Ironwood output fixed by the
post-synthesis assumptions. -/
theorem proverAssumptionsPost_implies_gardenOrchardAction_output
    (proverValue : ProverValue unit Fp) (wit : ActionData)
    (hint : ProverHint Fp)
    (assumptions :
      ProverAssumptionsPost
        Specs.Sinsemilla.orchardGenerators
        Zcash.Circuits.Action.orchardBases
        proverValue wit hint) :
    gardenOutput wit =
      ActionGarden.orchardAction
        ActionGarden.orchardParams (gardenInput wit) := by
  rcases assumptions with ⟨baseAssumptions, _crossAddress⟩
  rcases baseAssumptions with
    ⟨cmOldValid, _gdOldOnCurve, akOnCurve, _pkdOldOnCurve,
     _gdNewOnCurve, _pkdNewOnCurve,
     _rcvWindows, _alphaWindows, _rivkWindows,
     _rcmOldWindows, _rcmNewWindows,
     _magnitudeRange, signValid, _vOldRange, _vNewRange,
     merkleAssumptions, _ivkAssumptions,
     _oldNoteAssumptions, newNoteAssumptions,
     valueCommitmentAssumptions,
     nullifierEquation, randomizedKeyEquation,
     _valueEquation, _spendEquation, _outputEquation⟩
  rcases merkleAssumptions with
    ⟨middle, firstSucceeds, root, secondSucceeds, anchorEquation⟩
  rcases newNoteAssumptions with
    ⟨newNoteHashPoint, newNoteHashDefined, cmxEquation⟩
  rcases valueCommitmentAssumptions with
    ⟨valueCommitmentOne, valueCommitmentNegOne⟩
  have coreMerkleCorrespondence :=
    merklePath_pointToZ_of_two_segments
      Specs.Sinsemilla.orchardGenerators
      Zcash.Circuits.Action.orchardBases wit middle root
      firstSucceeds secondSucceeds
  have publicMerkleCorrespondence :=
    merklePathGarden_of_coreValid wit coreMerkleCorrespondence.2
  have publicRoot :
      ActionGarden.merkleRootGarden
          ActionGarden.orchardParams.merkleCrhQ
          (fpToZ wit.cmOld.x) (gardenPath wit) =
        fpToZ root :=
    publicMerkleCorrespondence.1.trans
      coreMerkleCorrespondence.1
  have anchorCorrespondence :
      (if ActionGarden.zEq
          (fpToZ wit.vOld) ActionGarden.zZero
       then fpToZ wit.anchor
       else
        ActionGarden.merkleRootGarden
          ActionGarden.orchardParams.merkleCrhQ
          (fpToZ wit.cmOld.x) (gardenPath wit)) =
        fpToZ wit.anchor := by
    rw [zEq_fpToZ_zero]
    by_cases valueIsZero : wit.vOld = 0
    · simp only [valueIsZero, decide_true, ↓reduceIte]
    · simp only [valueIsZero, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [publicRoot]
      have rootMinusAnchorIsZero :
          root - wit.anchor = 0 :=
        (mul_eq_zero.mp anchorEquation).resolve_left valueIsZero
      have rootIsAnchor : root = wit.anchor :=
        sub_eq_zero.mp rootMinusAnchorIsZero
      rw [rootIsAnchor]
  have valueCommitmentCorrespondence :
      ActionGarden.valueCommit
          (ActionGarden.signedNetValue
            (fpToZ wit.magnitude) (fpToZ wit.sign))
          (fqToZ wit.rcv.2) =
        pointToZ (⟨wit.cvX, wit.cvY⟩ : Point Fp) := by
    rcases signValid with signIsOne | signIsNegOne
    · rw [signIsOne]
      exact
        (valueCommitGarden_pointToZ_one
          wit.magnitude wit.rcv.2).trans
          (congrArg pointToZ
            (valueCommitmentOne signIsOne)).symm
    · rw [signIsNegOne]
      exact
        (valueCommitGarden_pointToZ_negOne
          wit.magnitude wit.rcv.2).trans
          (congrArg pointToZ
            (valueCommitmentNegOne signIsNegOne)).symm
  have nullifierCorrespondence :=
    nullifierGarden_pointToZ
      wit.nk wit.rhoOld wit.psiOld wit.cmOld cmOldValid
  rw [← nullifierEquation] at nullifierCorrespondence
  have randomizedKeyCorrespondence :=
    spendAuthRandomizeGarden_pointToZ
      wit.akP wit.alpha.2 akOnCurve
  rw [← randomizedKeyEquation] at randomizedKeyCorrespondence
  have newNoteCorrespondence :=
    noteCommitGarden_pointToZ_of_some
      wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew
      wit.rcmNew.2 newNoteHashPoint newNoteHashDefined
  have cmxCorrespondence :=
    congrArg ActionGarden.extractXGarden newNoteCorrespondence.1
  rw [extractXGarden_pointToZ, ← cmxEquation] at cmxCorrespondence
  unfold gardenOutput ActionGarden.orchardAction gardenInput
  simp only
  rw [anchorCorrespondence]
  rw [valueCommitmentCorrespondence]
  rw [nullifierCorrespondence]
  rw [randomizedKeyCorrespondence]
  rw [cmxCorrespondence]

end Zcash.Circuits.Action.Circuit.ActionGardenBridge
