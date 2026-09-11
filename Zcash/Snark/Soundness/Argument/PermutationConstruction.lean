import Zcash.Common.PermutationConstruction
import Zcash.Snark.Soundness.Argument.Permutation

/-! # Copy equalities from the permutation argument

The compiler's cycle partition and the permutation argument's value invariance
jointly enforce all declared equality constraints.
-/

namespace Zcash.PermConstruction

open Zcash.Snark

/-! ## Closing the loop with the permutation-argument soundness -/

/-- **Declared equalities are enforced.** If the verifier accepts — yielding the permutation-argument
multiset identity `h` for the constructed permutation `σ = build cs` (see `Permutation.lean`) — and the
copy constraints force `x` and `y` equal (the `Relation.EqvGen` closure), then their witnessed values
coincide. Combines `build_correct` (σ's cycles are exactly the constraint classes) with
`Permutation.perm_copy_constraints` (cells in a cycle hold equal values). -/
theorem value_eq_of_constraints {ι L V : Type*} [Fintype ι] [DecidableEq ι]
    (cs : List (ι × ι)) {label : ι → L} (hlabel : Function.Injective label) (value : ι → V)
    (h : Finset.univ.val.map (fun c => (value c, label c))
       = Finset.univ.val.map (fun c => (value c, label ((build cs) c))))
    {x y : ι} (hxy : Relation.EqvGen (fun u v => (u, v) ∈ cs) x y) :
    value x = value y :=
  perm_copy_constraints (build cs) hlabel value h ((build_correct cs x y).mpr hxy)

/-- Specialization to a directly declared copy constraint `(c, d) ∈ cs`. -/
theorem value_eq_of_mem {ι L V : Type*} [Fintype ι] [DecidableEq ι]
    (cs : List (ι × ι)) {label : ι → L} (hlabel : Function.Injective label) (value : ι → V)
    (h : Finset.univ.val.map (fun c => (value c, label c))
       = Finset.univ.val.map (fun c => (value c, label ((build cs) c))))
    {c d : ι} (hcd : (c, d) ∈ cs) :
    value c = value d :=
  value_eq_of_constraints cs hlabel value h (Relation.EqvGen.rel c d hcd)

end Zcash.PermConstruction
