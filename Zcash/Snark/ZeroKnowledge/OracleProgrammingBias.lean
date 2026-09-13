import Zcash.Snark.ZeroKnowledge.OracleProgramming

/-!
# Statistical loss from oracle programming conflicts

A common finite answer tape couples the actual cached oracle with independent
answers followed by programming. Their complete result/cache distributions
differ by at most the independent experiment's programming-failure probability.
The averaged theorem also covers a privately randomized oracle computation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Run on independent replies, then install the recorded trace without overwriting cached answers. -/
noncomputable def programmedOracleLaw {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) (comp : OracleComp Query Reply Value) (cache : OracleCache Query Reply) :
    PMF (Option (Value × OracleCache Query Reply)) :=
  (freshOracleTraceLaw answerLaw comp).map (programOracleView cache)

/-- The fixed-tape programming experiment has exactly the recorded independent-answer law. -/
theorem programmedOracleRunTape_law {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (h : comp.QueryBound budget) (cache : OracleCache Query Reply) :
    (independentTapeLaw answerLaw budget).map
        (fun tape => (freshOracleRunTape budget comp tape).bind (programOracleView cache)) =
      programmedOracleLaw answerLaw comp cache := by
  have hmap := congrArg (PMF.map (fun view => view.bind (programOracleView cache)))
    (freshOracleRunTape_law answerLaw h)
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_some, programmedOracleLaw] using hmap

/-- Cached execution and conflict-checked programming differ only on a programming failure. -/
theorem oracleProgramming_error_bound {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (h : comp.QueryBound budget) (cache : OracleCache Query Reply) :
    let error := (freshOracleTraceLaw answerLaw comp).toOuterMeasure
      {view | programOracleView cache view = none}
    PMFEventBiasLE ((cachedOracleLaw answerLaw comp cache).map some)
        (programmedOracleLaw answerLaw comp cache) error ∧
      PMFEventBiasLE (programmedOracleLaw answerLaw comp cache)
        ((cachedOracleLaw answerLaw comp cache).map some) error := by
  let tapeLaw := independentTapeLaw answerLaw budget
  let actual := cachedOracleRunTape budget comp cache
  let programmed := fun tape => (freshOracleRunTape budget comp tape).bind (programOracleView cache)
  have hactual : tapeLaw.map actual = (cachedOracleLaw answerLaw comp cache).map some :=
    cachedOracleRunTape_law answerLaw h cache
  have hprogrammed : tapeLaw.map programmed = programmedOracleLaw answerLaw comp cache :=
    programmedOracleRunTape_law answerLaw h cache
  have hbad : tapeLaw.toOuterMeasure {tape | programmed tape = none} =
      (freshOracleTraceLaw answerLaw comp).toOuterMeasure {view | programOracleView cache view = none} := by
    change tapeLaw.toOuterMeasure (programmed ⁻¹' {none}) = _
    rw [← PMF.toOuterMeasure_map_apply, hprogrammed, programmedOracleLaw, PMF.toOuterMeasure_map_apply]
    rfl
  have hagree (tape : Fin budget → Reply) (hgood : programmed tape ≠ none) :
      actual tape = programmed tape :=
    cachedOracleRunTape_eq_programmed budget comp cache tape hgood
  have forward := eventBias_map_of_agree tapeLaw actual programmed
    {tape | programmed tape = none} (fun tape _ hgood => hagree tape hgood)
  have reverse := eventBias_map_of_agree tapeLaw programmed actual
    {tape | programmed tape = none} (fun tape _ hgood => (hagree tape hgood).symm)
  rw [hactual, hprogrammed, hbad] at forward reverse
  exact ⟨forward, reverse⟩

/-- Private coins average the same conflict bound; no pointwise entropy assumption is needed. -/
theorem oracleProgramming_family_error_bound {Seed Query Reply Value : Type*} [DecidableEq Query]
    (seedLaw : PMF Seed) (answerLaw : PMF Reply) (comp : Seed → OracleComp Query Reply Value)
    (budget : ℕ) (h : ∀ seed, (comp seed).QueryBound budget) (cache : OracleCache Query Reply) :
    let actual := seedLaw.bind (fun seed => (cachedOracleLaw answerLaw (comp seed) cache).map some)
    let programmed := seedLaw.bind (fun seed => programmedOracleLaw answerLaw (comp seed) cache)
    let error := (seedLaw.bind (fun seed => freshOracleTraceLaw answerLaw (comp seed))).toOuterMeasure
      {view | programOracleView cache view = none}
    PMFEventBiasLE actual programmed error ∧ PMFEventBiasLE programmed actual error := by
  dsimp only
  rw [PMF.toOuterMeasure_bind_apply]
  exact ⟨eventBias_bind_average_tsum seedLaw
      (fun seed => (oracleProgramming_error_bound answerLaw (h seed) cache).1),
    eventBias_bind_average_tsum seedLaw
      (fun seed => (oracleProgramming_error_bound answerLaw (h seed) cache).2)⟩

end Zcash.Snark.ZeroKnowledge
