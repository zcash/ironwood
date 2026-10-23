import Mathlib.Tactic.IntervalCases
import Zcash.Circuits.Poseidon.HashTheorems
import Zcash.Circuits.Tests.TestVectors.OrchardPoseidonData
import Zcash.Meta.AxiomCheck

/-!
# Orchard Poseidon against zcash-test-vectors

Checks the model's Orchard Poseidon (`P128Pow5T3`) against the `orchard_poseidon` and
`orchard_poseidon_hash` vectors of
[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors), at the revision pinned in
`OrchardPoseidonData.lean`. The model mirrors
`halo2_poseidon/src/fp.rs` (constants) and `halo2_gadgets/src/poseidon/pow5.rs` (schedule).

## What is checked

* `roundConstants_eq_generator`, `mds_eq_generator`: the ported round constants and MDS matrix
  equal those of the vectors' generator, `zcash_test_vectors/orchard/poseidon.py`. Both sides
  come from the same Grain parameter generation, so this catches a transcription error, not a
  wrong parameter generation;
* `permute_value_eq_vector`: `Permute.concreteValue` (`Permute.value` at the ported constants)
  maps every `orchard_poseidon` input state to its output state;
* `constantLength_value_eq_vector`: the two-input `Hash.ConstantLength.value`, the hash that
  `PRF^nfOrchard` instantiates, maps every `orchard_poseidon_hash` input to its output. The rest
  of the nullifier derivation is not checked here;
* `vector_counts`, `data_canonical`: the data holds the 11 + 11 published vectors, and every
  value in it is below `p`, so the comparisons above are not vacuous and the casts to `Fp` lose
  nothing.

The comparison is at the field-element level: each vector entry is the integer its 32-byte
little-endian encoding denotes. Byte-level encoding is out of scope. `P128Pow5T3.mdsInv`, which
the partial-round gate uses, does not occur in the value-level model;
`Permute.P128Pow5T3.mds_mul_mdsInv_apply` ties it to `mds`.

## Method

Evaluating the field-level model in the kernel is impractically slow, because of the `ZMod`
instance layer (see `Zcash/Circuits/Tests/BenchFixedBase.lean`). So the vectors are evaluated by
`decide +kernel`, whose `Nat` arithmetic uses the kernel's GMP acceleration, on `permN`, a `Nat`
mirror of the same schedule that reduces modulo `P` after every operation; `toState_permN`
transfers the result to `Fp` once, for every input.
-/

namespace Zcash.Circuits.Tests.TestVectors.OrchardPoseidon

open Zcash.Circuits.Poseidon
open Zcash.Circuits.Poseidon.Permute (State)

/-- The Pallas base-field modulus. -/
abbrev P : Nat := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD

/-- The field state an integer state denotes. -/
def toState (s : State Nat) : State Fp := { x0 := s.x0, x1 := s.x1, x2 := s.x2 }

-- Test-local: `decide +kernel` compares integer states below.
deriving instance DecidableEq for State

/-! ## The generator's constants, by index -/

/-- Round `r` of the generator's round constants. -/
def rcN (r : Nat) : State Nat := generatorRoundConstants.getD r { x0 := 0, x1 := 0, x2 := 0 }

/-- Entry `(i, j)` of the generator's MDS matrix. -/
def mdsN (i j : Nat) : Nat := (generatorMds.getD i []).getD j 0

/-! ## A `Nat`-level mirror of the schedule -/

/-- `x ↦ x⁵ mod P`, in the shape of `pow5`. -/
def pow5N (x : Nat) : Nat :=
  let x2 := x * x % P
  x2 * x2 % P * x % P

/-- The MDS matrix applied to a state, modulo `P`. -/
def mixN (s : State Nat) : State Nat :=
  { x0 := (s.x0 * mdsN 0 0 + s.x1 * mdsN 0 1 + s.x2 * mdsN 0 2) % P
    x1 := (s.x0 * mdsN 1 0 + s.x1 * mdsN 1 1 + s.x2 * mdsN 1 2) % P
    x2 := (s.x0 * mdsN 2 0 + s.x1 * mdsN 2 1 + s.x2 * mdsN 2 2) % P }

/-- One full round at source round `r`, mirroring `FullRound.value`. -/
def fullN (r : Nat) (s : State Nat) : State Nat :=
  mixN
    { x0 := pow5N ((s.x0 + (rcN r).x0) % P)
      x1 := pow5N ((s.x1 + (rcN r).x1) % P)
      x2 := pow5N ((s.x2 + (rcN r).x2) % P) }

/-- One partial-round row (source rounds `r` and `r + 1`), mirroring `PartialRounds.value`. -/
def partialN (r : Nat) (s : State Nat) : State Nat :=
  let mid := mixN
    { x0 := pow5N ((s.x0 + (rcN r).x0) % P)
      x1 := (s.x1 + (rcN r).x1) % P
      x2 := (s.x2 + (rcN r).x2) % P }
  mixN
    { x0 := pow5N ((mid.x0 + (rcN (r + 1)).x0) % P)
      x1 := (mid.x1 + (rcN (r + 1)).x1) % P
      x2 := (mid.x2 + (rcN (r + 1)).x2) % P }

/-- Apply `f k`, `f (k + 1)`, …, `f (k + n - 1)` in order. Structural recursion, so the kernel
evaluates it directly (`Fin.foldl` is well-founded recursion). -/
def iterN (f : Nat → State Nat → State Nat) : Nat → Nat → State Nat → State Nat
  | _, 0, s => s
  | k, n + 1, s => iterN f (k + 1) n (f k s)

/-- The `Nat`-level permutation: 4 full rounds, 28 partial-round rows, 4 full rounds. -/
def permN (s : State Nat) : State Nat :=
  iterN (fun i => fullN (4 + 56 + i)) 0 4 <|
    iterN (fun i => partialN (4 + 2 * i)) 0 28 <|
      iterN (fun i => fullN i) 0 4 s

/-! ## Kernel checks over `Nat` -/

/-- The generator's shape is the `P128Pow5T3` schedule: width 3, `R_F = 8` (4 + 4) and
`R_P = 56`, one constant row per round, and a 3×3 MDS matrix. The model applies two partial
rounds per chip row (consuming two constant rows), as the `pow5` chip lays them out. -/
theorem generator_shape :
    generatorWidth = 3 ∧ generatorFullRounds = 8 ∧ generatorPartialRounds = 56 ∧
    generatorRoundConstants.length = 64 ∧ generatorMds.length = 3 ∧
    ∀ row ∈ generatorMds, row.length = 3 := by
  decide +kernel

/-- The generator's capacity word is `2·2⁶⁴`, the `ConstantLength<2>` domain. -/
theorem generatorCapacity_eq : generatorCapacity = 2 * 2 ^ 64 := by
  decide +kernel

/-- The data holds all 11 + 11 published vectors, so the checks below are not vacuous. -/
theorem vector_counts : permutationVectors.length = 11 ∧ hashVectors.length = 11 := by
  decide +kernel

/-- Every value in the data is below `P`: the casts to `Fp` below lose nothing. -/
theorem data_canonical :
    (∀ r ∈ generatorRoundConstants, r.x0 < P ∧ r.x1 < P ∧ r.x2 < P) ∧
    (∀ row ∈ generatorMds, ∀ x ∈ row, x < P) ∧ generatorCapacity < P ∧
    (∀ v ∈ permutationVectors, v.input.x0 < P ∧ v.input.x1 < P ∧ v.input.x2 < P ∧
      v.output.x0 < P ∧ v.output.x1 < P ∧ v.output.x2 < P) ∧
    (∀ v ∈ hashVectors, v.x < P ∧ v.y < P ∧ v.output < P) := by
  decide +kernel

/-- The `Nat` mirror maps every `orchard_poseidon` input state to its output state. -/
theorem permN_vectors : ∀ v ∈ permutationVectors, permN v.input = v.output := by
  decide +kernel

/-- The `Nat` mirror's first output word, on `(x, y, capacity)`, is every
`orchard_poseidon_hash` output. -/
theorem permN_hash_vectors :
    ∀ v ∈ hashVectors, (permN { x0 := v.x, x1 := v.y, x2 := generatorCapacity }).x0 = v.output := by
  decide +kernel

/-! ## The ported constants equal the generator's -/

/-- The ported round constants equal the generator's, round by round. -/
theorem roundConstants_eq_generator (r : Nat) (hr : r < 64) :
    Permute.P128Pow5T3.roundConstants r = toState (rcN r) := by
  interval_cases r <;>
    simp only [Permute.P128Pow5T3.roundConstants, Permute.P128Pow5T3.fromRaw, toState, rcN,
      generatorRoundConstants, List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num

/-- The ported MDS matrix equals the generator's, entry by entry. -/
theorem mds_eq_generator (i j : Nat) (hi : i < 3) (hj : j < 3) :
    Permute.P128Pow5T3.mds i j = (mdsN i j : Fp) := by
  interval_cases i <;> interval_cases j <;>
    simp only [Permute.P128Pow5T3.mds, Permute.P128Pow5T3.fromRaw, mdsN, generatorMds,
      List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num

/-! ## Transport from `Nat` to `Fp` -/

/-- `pow5N` denotes `pow5`. -/
theorem cast_pow5N (x : Nat) : ((pow5N x : Nat) : Fp) = pow5 (x : Fp) := by
  simp only [pow5N, pow5, Nat.cast_mul, ZMod.natCast_mod]

/-- `mixN` denotes the ported MDS matrix applied to the state. -/
theorem toState_mixN (a b c : Nat) :
    toState (mixN { x0 := a, x1 := b, x2 := c }) =
      { x0 := a * Permute.P128Pow5T3.mds 0 0 + b * Permute.P128Pow5T3.mds 0 1 +
          c * Permute.P128Pow5T3.mds 0 2
        x1 := a * Permute.P128Pow5T3.mds 1 0 + b * Permute.P128Pow5T3.mds 1 1 +
          c * Permute.P128Pow5T3.mds 1 2
        x2 := a * Permute.P128Pow5T3.mds 2 0 + b * Permute.P128Pow5T3.mds 2 1 +
          c * Permute.P128Pow5T3.mds 2 2 } := by
  simp (disch := decide) only [toState, mixN, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    mds_eq_generator]

/-- One `Nat` full round denotes `FullRound.value` at the ported constants. -/
theorem toState_fullN (r : Nat) (hr : r < 64) (s : State Nat) :
    toState (fullN r s) =
      FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
        Permute.P128Pow5T3.mds r) (toState s) := by
  have hrc := roundConstants_eq_generator r hr
  rw [fullN, toState_mixN]
  simp only [FullRound.value, FullRound.params, hrc, toState, cast_pow5N, ZMod.natCast_mod,
    Nat.cast_add]

/-- One `Nat` partial-round row denotes `PartialRounds.value` at the ported constants. -/
theorem toState_partialN (r : Nat) (hr : r + 1 < 64) (s : State Nat) :
    toState (partialN r s) =
      PartialRounds.value (PartialRounds.paramsP128 Permute.P128Pow5T3.roundConstants r)
        (toState s) := by
  have hrc := roundConstants_eq_generator r (by omega)
  have hrc' := roundConstants_eq_generator (r + 1) hr
  simp only [partialN, PartialRounds.value, PartialRounds.mid0SboxValue,
    PartialRounds.paramsP128, PartialRounds.params, hrc, hrc']
  rw [toState_mixN]
  simp (disch := decide) only [toState, mixN, cast_pow5N, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_mul, mds_eq_generator]

/-- `iterN` denotes the matching `Fin.foldl`, given that each step denotes its counterpart. -/
theorem toState_iterN (f : Nat → State Nat → State Nat) (F : Nat → State Fp → State Fp) :
    ∀ (n k : Nat) (s : State Nat),
      (∀ i t, k ≤ i → i < k + n → toState (f i t) = F i (toState t)) →
      toState (iterN f k n s) = Fin.foldl n (fun st i => F (k + i.val) st) (toState s)
  | 0, _, _, _ => by simp [iterN]
  | n + 1, k, s, h => by
    rw [iterN, toState_iterN f F n (k + 1) (f k s) (fun i t h1 h2 => h i t (by omega) (by omega)),
      Fin.foldl_succ, h k s (by omega) (by omega)]
    simp only [Fin.val_succ, Fin.val_zero, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

/-- The `Nat` mirror denotes `Permute.value` at the ported constants, on every input. -/
theorem toState_permN (s : State Nat) :
    toState (permN s) = Permute.value Permute.P128Pow5T3.roundConstants (toState s) := by
  have h1 := toState_iterN (fun i => fullN i)
    (fun i => FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
      Permute.P128Pow5T3.mds i)) 4 0 s
    (fun i t _ hi => toState_fullN i (by omega) t)
  have h2 := toState_iterN (fun i => partialN (4 + 2 * i))
    (fun i => PartialRounds.value
      (PartialRounds.paramsP128 Permute.P128Pow5T3.roundConstants (4 + 2 * i))) 28 0
    (iterN (fun i => fullN i) 0 4 s)
    (fun i t _ hi => toState_partialN (4 + 2 * i) (by omega) t)
  have h3 := toState_iterN (fun i => fullN (4 + 56 + i))
    (fun i => FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
      Permute.P128Pow5T3.mds (4 + 56 + i))) 4 0
    (iterN (fun i => partialN (4 + 2 * i)) 0 28 (iterN (fun i => fullN i) 0 4 s))
    (fun i t _ hi => toState_fullN (4 + 56 + i) (by omega) t)
  simp only [Nat.zero_add] at h1 h2 h3
  rw [permN, h3, h2, h1, Permute.value]

/-! ## The model against the vectors -/

/-- `Permute.concreteValue` maps every `orchard_poseidon` input state to its output state. -/
theorem permute_value_eq_vector :
    ∀ v ∈ permutationVectors, Permute.concreteValue (toState v.input) = toState v.output := by
  intro v hv
  rw [Permute.concreteValue, ← toState_permN, permN_vectors v hv]

/-- The two-input `Hash.ConstantLength.value` maps every `orchard_poseidon_hash` input to its
output. -/
theorem constantLength_value_eq_vector :
    ∀ v ∈ hashVectors, Hash.ConstantLength.value #v[(v.x : Fp), (v.y : Fp)] = (v.output : Fp) := by
  intro v hv
  have hcap : Hash.ConstantLength.capacity 2 = (generatorCapacity : Fp) := by
    rw [generatorCapacity_eq]
    simp [Hash.ConstantLength.capacity]
  have hperm := toState_permN { x0 := v.x, x1 := v.y, x2 := generatorCapacity }
  calc Hash.ConstantLength.value #v[(v.x : Fp), (v.y : Fp)]
      = (Permute.value Permute.P128Pow5T3.roundConstants
          (toState { x0 := v.x, x1 := v.y, x2 := generatorCapacity })).x0 := by
        simp [Hash.ConstantLength.value, Sponge.GetOutput.value, Hash.ConstantLength.blockCount,
          hcap, Fin.foldl_succ, Hash.ConstantLength.stepValueAt,
          Hash.ConstantLength.absorbPermuteValue, Permute.concreteValue, Sponge.AddInput.value,
          Hash.ConstantLength.blockValue, Hash.ConstantLength.paddedWord, toState]
    _ = (v.output : Fp) := by rw [← hperm, ← permN_hash_vectors v hv]; rfl

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.generator_shape
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.vector_counts
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.data_canonical
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.roundConstants_eq_generator
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.mds_eq_generator
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.permute_value_eq_vector
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.constantLength_value_eq_vector

end Zcash.Circuits.Tests.TestVectors.OrchardPoseidon
