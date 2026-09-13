import Zcash.Snark.ZeroKnowledge.TranscriptQuery
import Zcash.Common.Probability.DistributionKernel

/-!
# Probability of a prior query naming the first private commitment

One byte address can name at most one first private point. A list of `q` prior
addresses therefore covers at most `q` such points, including when addresses
are duplicated. A pointwise mass bound prices this entire list at once.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open scoped ENNReal

/-- A single prior address has at most the maximum point mass of its unique possible anchor. -/
theorem transcriptAnchor_mass_le (law : PMF VestaG) {mass : ℝ≥0∞}
    (hatom : ∀ point, law point ≤ mass) (initial : List (TranscriptElt Fp VestaG))
    (address : TranscriptHashAddress) :
    law.toOuterMeasure {point | HasTranscriptAnchor initial address point} ≤ mass := by
  classical
  by_cases hexists : ∃ point, HasTranscriptAnchor initial address point
  · obtain ⟨point, hpoint⟩ := hexists
    have hsubset : {other | HasTranscriptAnchor initial address other} ∩ law.support ⊆ {point} := by
      intro other ⟨hother, _⟩
      exact hother.unique hpoint
    calc
      _ ≤ law.toOuterMeasure {point} := law.toOuterMeasure_mono hsubset
      _ = law point := PMF.toOuterMeasure_apply_singleton _ _
      _ ≤ mass := hatom point
  · have hempty : {point | HasTranscriptAnchor initial address point} = ∅ := by
      ext point
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hexists ⟨point, h⟩
    rw [hempty, MeasureTheory.measure_empty]
    exact zero_le

/-- All prior addresses together cost at most their count times the maximum anchor mass. -/
theorem transcriptAnchorList_mass_le (law : PMF VestaG) {mass : ℝ≥0∞}
    (hatom : ∀ point, law point ≤ mass) (initial : List (TranscriptElt Fp VestaG))
    (addresses : List TranscriptHashAddress) :
    law.toOuterMeasure {point | ∃ address ∈ addresses, HasTranscriptAnchor initial address point} ≤
      addresses.length * mass := by
  induction addresses with
  | nil => simp
  | cons address addresses ih =>
    have hevent : {point | ∃ query ∈ address :: addresses, HasTranscriptAnchor initial query point} =
        {point | HasTranscriptAnchor initial address point} ∪
          {point | ∃ query ∈ addresses, HasTranscriptAnchor initial query point} := by
      ext point
      simp
    rw [hevent]
    calc
      _ ≤ law.toOuterMeasure {point | HasTranscriptAnchor initial address point} +
          law.toOuterMeasure {point | ∃ query ∈ addresses, HasTranscriptAnchor initial query point} :=
        MeasureTheory.measure_union_le _ _
      _ ≤ mass + addresses.length * mass := add_le_add (transcriptAnchor_mass_le law hatom initial address) ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]; ac_rfl

end Zcash.Snark.ZeroKnowledge
