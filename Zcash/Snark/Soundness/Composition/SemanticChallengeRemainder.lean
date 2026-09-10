import Zcash.Snark.Soundness.Pricing.ChallengePricing
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.Composition.StraightLineConstraint

/-!
# The semantic challenge remainder

The compressed-identity capstones price the multiopen and IPA events. The Action-level
statement also needs the *semantic* exclusions: the `y` fold split, and the permutation and
lookup `β`, `γ`, `θ` resolvers. `ChallengePricing` bounds each exclusion set; this module
prices the bundle-wide unions and adds them into one remainder.

Each term stays separate and named because each counts circuit-sized quantities over `|Fp|`,
so the total must be evaluated at the deployed shape rather than assumed to fit. Each
challenge is its own squeeze, so the events are priced independently and added.

At the captured key it fits with room. The cell count is `3` chunks over `15` columns at
`2048` rows, `= 30720 ≈ 2^14.9`. Permutation `β` dominates at about `2^-223`, being quadratic
in the cell count; the other three surfaces are `2^-229` or smaller, and the `y` term adds
only `n · |constraints|`. Charged at `(Q+1)` with `Q = 2^123` the total is about `2^-100`,
sixteen bits under the compressed model's `2^-84` ceiling, so exposing these terms does not
move the headline. Permutation `β` is what to re-check if the key changes.
-/

namespace Zcash.Snark

open scoped ENNReal
open Finset

variable {shape : Shape} {G : Type*}

/-! ## Bundle-wide permutation exclusions -/

/-- The bundle-wide permutation `γ` exclusion costs the summed cell counts, doubled. -/
theorem allResolverPermutationGammaBadSet_measure_le
    {circuitShape : CircuitShape}
    (numProofs : ℕ)
    (vk : VerifyingKey circuitShape Fp G) (ch : Challenges circuitShape.k Fp)
    (poly : CommitmentId → CPoly) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationGammaBadSet numProofs vk ch poly m) ≤
      ((∑ p : Fin numProofs,
        2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast le_trans (Finset.card_biUnion_le)
    (Finset.sum_le_sum fun p _ => resolverPermutationGammaBadSet_card_le vk ch poly p m)

/-- The bundle-wide permutation `β` exclusion costs the summed quadratic cell counts. -/
theorem allResolverPermutationBetaBadSet_measure_le
    {circuitShape : CircuitShape}
    (numProofs : ℕ)
    (vk : VerifyingKey circuitShape Fp G)
    (poly : CommitmentId → CPoly) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationBetaBadSet numProofs vk poly m) ≤
      ((∑ p : Fin numProofs,
        (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
          Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast le_trans (Finset.card_biUnion_le)
    (Finset.sum_le_sum fun p _ => resolverPermutationBetaBadSet_card_le vk poly p m)

/-! ## Bundle-wide lookup exclusions -/

/-- The bundle-wide lookup `γ` exclusion costs `2(u+1)` per (proof, lookup) pair. -/
theorem allResolverLookupGammaBadSet_measure_le
    {circuitShape : CircuitShape} {k : ℕ} (numProofs : ℕ)
    (vk : VerifyingKey circuitShape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupGammaBadSet numProofs vk ch poly u) ≤
      ((numProofs * circuitShape.numLookups * (2 * (u + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  refine_lift Nat.cast_le.mpr ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum fun q _ =>
    resolverLookupGammaBadSet_card_le vk ch poly q.1 q.2 u) ?_
  simp [Finset.sum_const, Fintype.card_prod, Nat.mul_assoc]

/-- The bundle-wide lookup `β` exclusion costs `(u+2)(u+1) + (u+1)` per pair. -/
theorem allResolverLookupBetaBadSet_measure_le
    {circuitShape : CircuitShape} {k : ℕ} (numProofs : ℕ)
    (vk : VerifyingKey circuitShape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupBetaBadSet numProofs vk ch poly u) ≤
      ((numProofs * circuitShape.numLookups * ((u + 2) * (u + 1) + (u + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  refine_lift Nat.cast_le.mpr ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum fun q _ =>
    resolverLookupBetaBadSet_card_le vk ch poly q.1 q.2 u) ?_
  simp [Finset.sum_const, Fintype.card_prod, Nat.mul_assoc]

/-! ## The remainder -/

/-- **The Action-level semantic challenge remainder.**  The `y` fold-split term, the permutation
`β`/`γ` terms and the lookup `β`/`γ` terms, each as a count over `|Fp|`.

`θ` is not folded in here: `enabledLookupThetaBadSetFamily_card_le` prices it against an
environment family rather than a verifying key, so it is charged where that family is fixed. -/
noncomputable def semanticChallengeRemainder
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly) (constraints : List (CPoly))
    (m u : ℕ) : ℝ≥0∞ :=
  ((vk.n * constraints.length : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((∑ p : Fin numProofs,
      2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((∑ p : Fin numProofs,
      (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
        Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((numProofs * shape.numLookups * (2 * (u + 1)) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((numProofs * shape.numLookups * ((u + 2) * (u + 1) + (u + 1)) : ℕ) : ℝ≥0∞) /
      Fintype.card Fp

/-- **Each semantic exclusion is charged once, and the four bundle-wide events sum to the
remainder.**  The `y` event is priced over its own squeeze by `goodY_failure_measure_le`; the
other three are the bundle-wide unions above.  Stated as a sum because each challenge is a
separate squeeze. -/
theorem semanticChallengeRemainder_covers
    (numProofs : ℕ) (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (constraints : List (CPoly))
    (m u : ℕ) (hn : vk.n ≠ 0) :
    uniformChallenge.toOuterMeasure
        {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness constraints vk.n j)} +
      uniformChallenge.toOuterMeasure
          (allResolverPermutationGammaBadSet numProofs vk ch poly m) +
      uniformChallenge.toOuterMeasure
          (allResolverPermutationBetaBadSet numProofs vk poly m) +
      uniformChallenge.toOuterMeasure
          (allResolverLookupGammaBadSet numProofs vk ch poly u) +
      uniformChallenge.toOuterMeasure
          (allResolverLookupBetaBadSet numProofs vk ch poly u) ≤
      semanticChallengeRemainder numProofs vk poly constraints m u := by
  unfold semanticChallengeRemainder
  gcongr
  · exact goodY_failure_measure_le constraints hn
  · exact allResolverPermutationGammaBadSet_measure_le numProofs vk ch poly m
  · exact allResolverPermutationBetaBadSet_measure_le numProofs vk poly m
  · exact allResolverLookupGammaBadSet_measure_le numProofs vk ch poly u
  · exact allResolverLookupBetaBadSet_measure_le numProofs vk ch poly u


/-! ## The four surfaces at their squeeze indices

`theta` is squeezed first, then `beta`, then `gamma`, then `y` — indices `0`, `1`, `2`, `3` of the
pre-IPA record.  Each surface is priced by the index-generic squeeze bound, so the four premises
the semantic endpoint takes are one application apiece.
-/

/-- The `theta` surface: index `0`. -/
abbrev thetaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 0 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 0 family badF

/-- The `beta` surface: index `1`. -/
abbrev betaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 1 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 1 family badF

/-- The `gamma` surface: index `2`. -/
abbrev gammaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 2 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 2 family badF

/-- The `y` surface: index `3`. -/
abbrev ySurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 3 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 3 family badF

/-- **The four semantic surfaces, priced together.**  Each costs `(Q + 1)` times its own
per-challenge bound, so the semantic endpoint's `hY`, `hBeta`, `hGamma` and `hTheta` premises are
supplied at once.  The per-challenge bounds are the bundle-wide exclusion measures above; the
stability inputs come from `hstab_of_prefixDeterminedAt` at the matching index. -/
theorem semanticSurfaces_prob_le {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (badTheta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 0 → Fp) → Set Fp)
    (badBeta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 1 → Fp) → Set Fp)
    (badGamma : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 2 → Fp) → Set Fp)
    (badY : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 3 → Fp) → Set Fp)
    {epsTheta epsBeta epsGamma epsY : ENNReal}
    (hstabTheta : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 0) v)) 0 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
    (hstabBeta : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 1) v)) 1 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
    (hstabGamma : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 2) v)) 2 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
    (hstabY : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 3) v)) 3 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
    (hTheta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badTheta basis t nu) ≤ epsTheta)
    (hBeta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badBeta basis t nu) ≤ epsBeta)
    (hGamma : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badGamma basis t nu) ≤ epsGamma)
    (hY : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badY basis t nu) ≤ epsY) :
    (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          thetaSurface family badTheta) ≤ (family.Q + 1 : ℕ) * epsTheta ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          betaSurface family badBeta) ≤ (family.Q + 1 : ℕ) * epsBeta ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          gammaSurface family badGamma) ≤ (family.Q + 1 : ℕ) * epsGamma ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          ySurface family badY) ≤ (family.Q + 1 : ℕ) * epsY :=
  ⟨squeezeSurfaceEvent_prob_le 0 query family badTheta hstabTheta hTheta,
   squeezeSurfaceEvent_prob_le 1 query family badBeta hstabBeta hBeta,
   squeezeSurfaceEvent_prob_le 2 query family badGamma hstabGamma hGamma,
   squeezeSurfaceEvent_prob_le 3 query family badY hstabY hY⟩


/-! ## Run-uniformity of the epsilons

`semanticSurfaces_prob_le` takes bounds uniform over runs, while the card bounds are stated against
a resolver `poly`.  For the permutation surfaces the dependence is only apparent: the chunk pair
list is a `map` over the key's own `permutationChunks`, so its length — and hence the cell count
the bound is stated in — is the same for every `poly`.  The lookup bounds are already stated in
the usable-row count alone.
-/

/-- The resolver's chunk pair count is the key's, not the run's. -/
theorem resolverPermutationPairs_length {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (c : ℕ) :
    (ResolverPermutationPairs vk poly p c).length = (vk.permutationChunks.getD c []).length :=
  List.length_map _

/-- Hence two runs give the same permutation cell count, so the epsilon is run-uniform. -/
theorem resolverPermutationCell_card_congr
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly poly' : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    Fintype.card (ResolverPermutationCell vk poly p m) =
      Fintype.card (ResolverPermutationCell vk poly' p m) := by
  unfold ResolverPermutationCell
  simp only [resolverPermutationPairs_length]


/-! ## The semantic endpoint with its surfaces supplied

`straightLineConstraintSemanticFailure_prob_le_of_compressed_bound` takes the four semantic
exclusions as abstract sets with abstract bounds.  The theorem below instantiates them at the four
surfaces and discharges the bounds from `semanticSurfaces_prob_le`, so a caller supplies only a
per-challenge exclusion measure and prefix-determinism at each of the four squeeze indices.
-/

/-- **The semantic failure bound at the four surfaces.**  Each semantic exclusion costs `(Q + 1)`
times its per-challenge measure, on top of the compressed bound:
`compressedBound + (Q+1)·(epsY + epsBeta + epsGamma + epsTheta)`.

Prefix-determinism at index `n` says the first `n` squeezed prefixes depend only on oracle answers
strictly shorter than the index-`n` prefix, which is what lets one challenge be resampled in
place. -/
theorem straightLineConstraintSemanticFailure_prob_le_of_surfaces
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) → T)
    (family : ComputedStraightLineDeployedFSFamily shape)
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) → Prop)
    (badTheta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 0 → Fp) → Set Fp)
    (badBeta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 1 → Fp) → Set Fp)
    (badGamma : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 2 → Fp) → Set Fp)
    (badY : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 3 → Fp) → Set Fp)
    {compressedBound epsTheta epsBeta epsGamma epsY : ENNReal}
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained semanticDecoded
      (ySurface family.toFamily badY) (betaSurface family.toFamily badBeta)
      (gammaSurface family.toFamily badGamma) (thetaSurface family.toFamily badTheta))
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent) ≤ compressedBound)
    (hdetTheta : PrefixDeterminedAt family.toFamily 0)
    (hdetBeta : PrefixDeterminedAt family.toFamily 1)
    (hdetGamma : PrefixDeterminedAt family.toFamily 2)
    (hdetY : PrefixDeterminedAt family.toFamily 3)
    (hTheta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badTheta basis t nu) ≤ epsTheta)
    (hBeta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badBeta basis t nu) ≤ epsBeta)
    (hGamma : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badGamma basis t nu) ≤ epsGamma)
    (hY : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badY basis t nu) ≤ epsY) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent semanticDecoded)
      ≤ compressedBound + ((family.Q + 1 : ℕ) * epsY + ((family.Q + 1 : ℕ) * epsBeta +
          ((family.Q + 1 : ℕ) * epsGamma + (family.Q + 1 : ℕ) * epsTheta))) :=
  have hsurfaces := semanticSurfaces_prob_le query family.toFamily badTheta badBeta badGamma badY
    (hstab_of_prefixDeterminedAt family.toFamily 0 hdetTheta)
    (hstab_of_prefixDeterminedAt family.toFamily 1 hdetBeta)
    (hstab_of_prefixDeterminedAt family.toFamily 2 hdetGamma)
    (hstab_of_prefixDeterminedAt family.toFamily 3 hdetY)
    hTheta hBeta hGamma hY
  family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound
    query semanticDecoded _ _ _ _ hsemantic hcompressed
    hsurfaces.2.2.2 hsurfaces.2.1 hsurfaces.2.2.1 hsurfaces.1

end Zcash.Snark
