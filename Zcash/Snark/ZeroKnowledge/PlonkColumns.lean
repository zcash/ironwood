import Zcash.Snark.ZeroKnowledge.ColumnSequence
import Zcash.Common.Probability.Distribution

/-!
# The pinned private-column schedule

The order follows steps 1–3 of the pinned description: all advice columns; each lookup's
permuted input/table pair; all permutation products; then all lookup products. Advice and
lookup permutation columns replace six rows. Products retain the terminal row and replace
five. The retained-row algorithms are supplied functions of the complete earlier private
history, to be instantiated with the lookup and grand-product constructions.

Five common observation points can be disclosed from every column. This deliberately
retains more evaluations than the actual proof, allowing its query groups to be formed by
one deterministic projection of the joint distribution.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The five kinds of newly committed private column. -/
inductive PrivateColumnId (actions : ℕ) where
  | advice (action : Fin actions) (column : Fin 10)
  | lookupInput (action : Fin actions) (lookup : Fin 3)
  | lookupTable (action : Fin actions) (lookup : Fin 3)
  | permutationProduct (action : Fin actions) (set : Fin 3)
  | lookupProduct (action : Fin actions) (lookup : Fin 3)
  deriving DecidableEq, Repr

/-- The exact commitment order, with the action loop outside each phase's column loop. -/
def privateColumnOrder (actions : ℕ) : List (PrivateColumnId actions) :=
  (List.finRange actions).flatMap (fun a => (List.finRange 10).map (.advice a)) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).flatMap
    (fun l => [.lookupInput a l, .lookupTable a l])) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).map (.permutationProduct a)) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).map (.lookupProduct a))

/-- Products retain the terminal product row `2042`; the other columns replace it. -/
def PrivateColumnId.firstMasked {actions : ℕ} : PrivateColumnId actions → ℕ
  | .advice _ _ | .lookupInput _ _ | .lookupTable _ _ => 2042
  | .permutationProduct _ _ | .lookupProduct _ _ => 2043

/-- All scheduled private columns retain at most the first 2043 rows. -/
theorem PrivateColumnId.firstMasked_le {actions : ℕ} (id : PrivateColumnId actions) :
    id.firstMasked ≤ 2043 := by cases id <;> simp [PrivateColumnId.firstMasked]

/-- Install the supplied private constructions in the pinned order. -/
def plonkColumnSteps {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    List (ColumnStep 2048) :=
  (privateColumnOrder actions).map fun id => ⟨id.firstMasked, construct id⟩

/-- There are ten advice, six lookup permutation, and six product columns per Action. -/
theorem privateColumnOrder_length (actions : ℕ) : (privateColumnOrder actions).length = 22 * actions := by
  simp [privateColumnOrder, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  omega

/-- Every private column identity occurs in the declared commitment schedule. -/
theorem privateColumnOrder_mem {actions : ℕ} (id : PrivateColumnId actions) :
    id ∈ privateColumnOrder actions := by
  cases id <;> simp [privateColumnOrder, List.mem_flatMap]

/-- Locate a private commitment in the emitted point vector. -/
def privateColumnIndex {actions : ℕ} (id : PrivateColumnId actions) : Fin (22 * actions) :=
  ⟨(privateColumnOrder actions).idxOf id, by
    simpa only [privateColumnOrder_length] using List.idxOf_lt_length_of_mem (privateColumnOrder_mem id)⟩

/-- Read the identity of the private commitment at a given position. -/
def privateColumnAt {actions : ℕ} (i : Fin (22 * actions)) : PrivateColumnId actions :=
  (privateColumnOrder actions)[i.val]'(by simpa only [privateColumnOrder_length] using i.isLt)

/-- Indexing the schedule by an identity recovers that identity. -/
theorem privateColumnAt_index {actions : ℕ} (id : PrivateColumnId actions) :
    privateColumnAt (privateColumnIndex id) = id := by
  simp [privateColumnAt, privateColumnIndex, List.getElem_idxOf]

/-- The executable column schedule has the same declared number of private columns. -/
theorem plonkColumnSteps_length {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    (plonkColumnSteps construct).length = 22 * actions := by
  simp [plonkColumnSteps, privateColumnOrder_length]

/-- Summing a flattened list equals summing its component totals, assembling per-column randomness
counts. -/
private theorem sum_flatMap_nat {A : Type*} (values : List A) (f : A → List ℕ) :
    (values.flatMap f).sum = (values.map fun a => (f a).sum).sum := by
  induction values with
  | nil => rfl
  | cons a values ih => simp [ih]

/-- The exact replacement-row budget: `16m` six-row masks and `6m` five-row masks. -/
theorem plonkColumnSteps_row_samples {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    columnRowSampleCount (plonkColumnSteps construct) = 126 * actions := by
  rw [columnRowSampleCount_eq_sum]
  simp [plonkColumnSteps, privateColumnOrder, PrivateColumnId.firstMasked, List.map_flatMap,
    sum_flatMap_nat, Function.comp_def, List.sum_replicate, Nat.mul_comm]
  omega

/-- Every scheduled suffix has at least five fresh rows. -/
theorem plonkColumnSteps_firstMasked_le {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (step : ColumnStep 2048) (hstep : step ∈ plonkColumnSteps construct) : step.firstMasked ≤ 2043 := by
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp hstep
  exact id.firstMasked_le

/-- All five evaluations of all private columns are jointly hidden, including private dependencies. -/
theorem plonkColumns_joint_uniform {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (points : Fin 5 → Fp)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, points i ≠ omegaOf 11 ^ j.val) :
    (idealColumnRows (plonkColumnSteps construct) history).map (observeColumnRows (omegaOf 11) points) =
      uniformColumnViews 5 (22 * actions) := by
  rw [← plonkColumnSteps_length construct]
  apply idealColumnRows_joint_uniform _ _ _ _ (omegaOf_rows_injective 11 (by decide)) hpoints
  · intro step hstep i j
    exact haway i ⟨j.val, lt_of_lt_of_le j.isLt
      ((plonkColumnSteps_firstMasked_le construct step hstep).trans (by decide))⟩
  · intro step hstep
    have h := plonkColumnSteps_firstMasked_le construct step hstep
    omega

/-- The same entire evaluation trace with wide-reduced replacement rows costs `126m × bias`. -/
theorem sampledPlonkColumns_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (points : Fin 5 → Fp)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, points i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE
        ((sampledColumnRows (plonkColumnSteps construct) history).map (observeColumnRows (omegaOf 11) points))
        (uniformColumnViews 5 (22 * actions)) (((126 * actions : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (uniformColumnViews 5 (22 * actions))
        ((sampledColumnRows (plonkColumnSteps construct) history).map (observeColumnRows (omegaOf 11) points))
        (((126 * actions : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := sampledColumnRows_error_bound (plonkColumnSteps construct) history
  have forward := eventBias_map h.1 (observeColumnRows (omegaOf 11) points)
  have reverse := eventBias_map h.2 (observeColumnRows (omegaOf 11) points)
  rw [plonkColumns_joint_uniform construct history points hpoints haway, plonkColumnSteps_row_samples] at forward reverse
  exact ⟨forward, reverse⟩

end Zcash.Snark.ZeroKnowledge
