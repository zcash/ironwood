import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace

/-!
# Excluding initial-row selector activations

A selector absent from every local row zero is absent from global row zero under
any nonnegative region placement. This allows source checks to establish initial
inactivity without evaluating the floor planner or assuming a packing map.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits.Trace

/-- Check that the listed selectors never occur at local row zero. -/
def initialSelectorCheck (forbidden : List ℕ) (trace : List (List (ℕ × ℕ))) : Bool :=
  trace.all fun body => body.all fun activation =>
    activation.2 != 0 || !forbidden.contains activation.1

/-- Every successful source check excludes each listed selector in every region. -/
theorem initialSelectorCheck_not_mem_local (forbidden : List ℕ)
    (trace : List (List (ℕ × ℕ))) (hcheck : initialSelectorCheck forbidden trace = true)
    (selector : ℕ) (hselector : selector ∈ forbidden)
    (body : List (ℕ × ℕ)) (hbody : body ∈ trace) :
    (selector, 0) ∉ body := by
  intro hactivation
  have hlocal := List.all_eq_true.mp (List.all_eq_true.mp hcheck body hbody)
    (selector, 0) hactivation
  simp [hselector] at hlocal

/-- A placed row-zero activation must already have occurred at local row zero. -/
theorem mem_placeLabels_initial (starts : List ℕ)
    (trace : List (List (ℕ × ℕ))) (initial selector : ℕ)
    (hactivation : (selector, 0) ∈ placeLabels starts trace initial) :
    ∃ body ∈ trace, (selector, 0) ∈ body := by
  obtain ⟨⟨body, index⟩, hregion, hactivation⟩ := List.mem_flatMap.mp hactivation
  obtain ⟨⟨source, row⟩, hlocal, hequal⟩ := List.mem_map.mp hactivation
  have hsource : source = selector := congrArg Prod.fst hequal
  have hrow : row = 0 := by
    have habsolute := congrArg Prod.snd hequal
    dsimp at habsolute
    omega
  subst source row
  exact ⟨body, List.fst_mem_of_mem_zipIdx hregion, hlocal⟩

/-- Source exclusion remains true after any supplied region placement. -/
theorem initialSelectorCheck_not_mem_placed (forbidden : List ℕ)
    (trace : List (List (ℕ × ℕ))) (hcheck : initialSelectorCheck forbidden trace = true)
    (starts : List ℕ) (initial selector : ℕ) (hselector : selector ∈ forbidden) :
    (selector, 0) ∉ placeLabels starts trace initial := by
  intro hactivation
  obtain ⟨body, hbody, hlocal⟩ := mem_placeLabels_initial starts trace initial selector hactivation
  exact initialSelectorCheck_not_mem_local forbidden trace hcheck selector hselector body hbody hlocal

end Zcash.Snark.ZeroKnowledge
