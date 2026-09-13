import Zcash.Snark.ZeroKnowledge.RandomTapeSource
import Mathlib.Data.List.OfFn

/-!
# Finite retry tapes from separated private and public sources

The complete private source may correlate every word and every attempt. Public
reply slots are sampled independently of it. Uniform private tapes recover the
independent-attempt source used by the retained-history theorem. These identities
do not infer independence of generated blocks from any marginal assumption.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- Converting a finite vector of independent samples to a list gives the existing retry-tape law. -/
theorem independentTapeLaw_toList {A : Type*} (law : PMF A) (budget : ℕ) :
    (independentTapeLaw law budget).map List.ofFn = retryAttemptTape law budget := by
  induction budget with
  | zero => exact PMF.pure_map _ _
  | succ budget ih =>
    simp only [independentTapeLaw, retryAttemptTape, PMF.map_bind, PMF.map_comp,
      Function.comp_def, List.ofFn_cons]
    apply congrArg (PMF.bind law)
    funext value
    have h := congrArg (PMF.map (List.cons value)) ih
    simpa only [PMF.map_comp, Function.comp_def] using h

/-- Deterministic conversion of each complete attempt tape commutes with independent retry sampling. -/
theorem retryAttemptTape_map {A B : Type*} (law : PMF A) (convert : A → B) (budget : ℕ) :
    (retryAttemptTape law budget).map (List.map convert) = retryAttemptTape (law.map convert) budget := by
  induction budget with
  | zero => exact PMF.pure_map _ _
  | succ budget ih =>
    simp only [retryAttemptTape, PMF.map_bind, PMF.map_comp, PMF.bind_map,
      Function.comp_def, List.map_cons]
    apply congrArg (PMF.bind law)
    funext value
    have h := congrArg (PMF.map (List.cons (convert value))) ih
    simpa only [PMF.map_comp, Function.comp_def] using h

/-- Separate uniform public and private vectors are exactly the independent joint-attempt tape law. -/
theorem uniformRetryTape_source_law {Coins Tape View : Type*}
    [Fintype Coins] [Nonempty Coins] [Fintype Tape] [Nonempty Tape]
    (budget : ℕ) (finish : List (Coins × Tape) → View) :
    sourceTapeExperiment (PMF.uniformOfFintype (Fin budget → Coins))
        (PMF.uniformOfFintype (Fin budget → Tape))
        (fun coins tapes => finish (List.ofFn (fun i => (coins i, tapes i)))) =
      (retryAttemptTape (PMF.uniformOfFintype (Coins × Tape)) budget).map finish := by
  let combine := (Equiv.arrowProdEquivProdArrow (Fin budget) (fun _ => Coins) (fun _ => Tape)).symm
  have hpair := Zcash.map_uniformOfFintype_equiv combine
  have h := congrArg (PMF.map (fun tape : Fin budget → Coins × Tape => finish (List.ofFn tape))) hpair
  rw [PMF.map_comp, ← Zcash.independentProductPMF_uniform] at h
  have hlist : (PMF.uniformOfFintype (Fin budget → Coins × Tape)).map List.ofFn =
      retryAttemptTape (PMF.uniformOfFintype (Coins × Tape)) budget := by
    rw [← independentTapeLaw_uniform]
    exact independentTapeLaw_toList _ budget
  have hfinish := congrArg (PMF.map finish) hlist
  rw [PMF.map_comp] at hfinish
  simpa only [sourceTapeExperiment, Zcash.independentProductPMF,
    PMF.map_bind, PMF.map_comp, Function.comp_def] using h.trans hfinish

/-- Separate uniform sources also recover the joint retry law after the specified deterministic tape conversion. -/
theorem uniformRetryTape_source_map_law {Coins Tape Attempt View : Type*}
    [Fintype Coins] [Nonempty Coins] [Fintype Tape] [Nonempty Tape]
    (budget : ℕ) (convert : Coins × Tape → Attempt) (finish : List Attempt → View) :
    sourceTapeExperiment (PMF.uniformOfFintype (Fin budget → Coins))
        (PMF.uniformOfFintype (Fin budget → Tape))
        (fun coins tapes => finish (List.ofFn (fun i => convert (coins i, tapes i)))) =
      (retryAttemptTape ((PMF.uniformOfFintype (Coins × Tape)).map convert) budget).map finish := by
  have h := uniformRetryTape_source_law budget (fun tapes => finish (tapes.map convert))
  have hmap := congrArg (PMF.map finish)
    (retryAttemptTape_map (PMF.uniformOfFintype (Coins × Tape)) convert budget)
  rw [PMF.map_comp] at hmap
  simpa only [List.map_ofFn, Function.comp_def] using h.trans hmap

end Zcash.Snark.ZeroKnowledge
