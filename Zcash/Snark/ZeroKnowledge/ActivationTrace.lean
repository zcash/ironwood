import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace
import Zcash.Circuits.Trace.Activations

/-!
# The selector trace as a projection of the activation trace

The compact activation traces and their label projections are pure Halo2 compiler semantics and
live in `Zcash/Circuits/Trace/Activations.lean`, written to be lifted into Clean. What remains
here are the two equations tying this tree's existing selector names to the general ones.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Trace

variable {F : Type}

/-- The selector trace already in use is the selector projection of the activations. -/
theorem regionSelectorTrace_eq_project (body : RegionOperations F) :
    regionSelectorTrace body = (regionActivations body).flatMap selectorOf := by
  rw [regionActivations, project_of_vanishing _ _ selectorOf_vanishes]
  rfl

/-- The selector placement already in use is the generic one at a numeric payload. -/
theorem placeSelectorTrace_eq_placeLabels (starts : List ℕ) (trace : List (List (ℕ × ℕ)))
    (initial : ℕ) : placeSelectorTrace starts trace initial = placeLabels starts trace initial :=
  rfl

end Zcash.Snark.ZeroKnowledge
